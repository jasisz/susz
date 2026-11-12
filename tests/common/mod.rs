// Shared by the tests: the single-pass decoder against the two-pass check
// and the iterators.

use std::collections::hash_map::DefaultHasher;
use std::hash::Hasher;
use susz::read::{
    decode, decode_block, verify, verify_two_pass, Block, BlockRef, Component, Decl, Event, Expr,
    File, Level, Outcome, Stop, Visit,
};

// The outcome when blocks are left for later and then decoded in
// declaration order, as a lazy reader that checks every theorem would.
pub fn lazy_outcome(bytes: &[u8]) -> Outcome {
    struct Later;
    impl Visit<'_> for Later {
        type Error = ();
        fn open_block(&mut self, _: &BlockRef) -> bool {
            false
        }
    }
    let f = match File::open(bytes) {
        Ok(f) => f,
        Err(e) => return e.outcome(),
    };
    let d = match decode(&f, &mut Later) {
        Ok(d) => d,
        Err(Stop::File(e)) => return e.outcome(),
        Err(Stop::Visitor(())) => unreachable!(),
    };
    for &b in &d.state.blocks {
        match decode_block(bytes, &d.state, b, |_, _| Ok::<(), ()>(())) {
            Ok(()) => {}
            Err(Stop::File(e)) => return e.outcome(),
            Err(Stop::Visitor(())) => unreachable!(),
        }
    }
    Outcome::Accepted(d.summary)
}

// verify (one pass), the two-pass check and the lazy order give the same
// outcome, summary and error location.
pub fn same_outcomes(bytes: &[u8]) -> Result<(), String> {
    let one = format!("{:?}", verify(bytes));
    let two = format!("{:?}", verify_two_pass(bytes));
    let lazy = format!("{:?}", lazy_outcome(bytes));
    if one != two || one != lazy {
        return Err(format!("one pass: {one}\ntwo passes: {two}\nlazy: {lazy}"));
    }
    Ok(())
}

#[derive(Default)]
struct Log {
    h: DefaultHasher,
    n: u64,
}

impl Log {
    fn put(&mut self, s: String) {
        self.h.write(s.as_bytes());
        self.h.write_u8(0);
        self.n += 1;
    }
    fn end(self) -> (u64, u64) {
        (self.n, self.h.finish())
    }
}

fn name(id: u32, prefix: u32, part: Component) -> String {
    format!("N {id} {prefix} {part:?}")
}
fn level(id: u32, l: Level) -> String {
    format!("L {id} {l:?}")
}
fn expr(id: u32, e: &Expr) -> String {
    format!("E {id} {e:?}")
}
fn bexpr(k: u32, e: &Expr) -> String {
    format!("B {k} {e:?}")
}
fn decl(i: u32, off: u64, d: &Decl) -> String {
    format!("D {i} {off} {d:?}")
}

struct Logger {
    log: Log,
    lazy: bool,
}

impl<'a> Visit<'a> for Logger {
    type Error = ();
    fn name(&mut self, id: u32, prefix: u32, part: Component<'a>) -> Result<(), ()> {
        self.log.put(name(id, prefix, part));
        Ok(())
    }
    fn level(&mut self, id: u32, l: Level) -> Result<(), ()> {
        self.log.put(level(id, l));
        Ok(())
    }
    fn expr(&mut self, id: u32, e: &Expr<'a>) -> Result<(), ()> {
        self.log.put(expr(id, e));
        Ok(())
    }
    fn frontier(&mut self, kind: u8, index: u32, item: u32) -> Result<(), ()> {
        self.log.put(format!("F {kind} {index} {item}"));
        Ok(())
    }
    fn open_block(&mut self, _: &BlockRef) -> bool {
        !self.lazy
    }
    fn block_expr(&mut self, k: u32, e: &Expr<'_>) -> Result<(), ()> {
        self.log.put(bexpr(k, e));
        Ok(())
    }
    fn decl(&mut self, i: u32, off: u64, d: &Decl<'a>) -> Result<(), ()> {
        self.log.put(decl(i, off, d));
        Ok(())
    }
}

// On an accepted file, the single pass hands out exactly the records the
// iterators read, in the same order (eagerly: a block right before its
// theorem); a lazy pass then decode_block give the same records too.
pub fn same_events(bytes: &[u8]) -> Result<(), String> {
    let f = File::open(bytes).map_err(|e| e.to_string())?;
    let mut it = Log::default();
    let mut later = Log::default();
    let mut outer = Log::default();
    let mut m = f.main();
    while let Some(ev) = m.next() {
        let ev = ev.map_err(|e| e.to_string())?;
        let line = match &ev {
            Event::Name { id, prefix, part } => name(*id, *prefix, *part),
            Event::Level { id, level: l } => level(*id, *l),
            Event::Expr { id, expr: e } => expr(*id, e),
            Event::Frontier { kind, index, item } => format!("F {kind} {index} {item}"),
            Event::Decl {
                index,
                offset,
                decl: d,
            } => decl(*index, *offset, d),
        };
        outer.put(line.clone());
        match ev {
            Event::Decl {
                index,
                offset,
                decl: d,
            } => {
                if let Decl::ThmBlock { block, .. } = &d {
                    for r in Block::new(bytes, m.state(), *block) {
                        let (k, e) = r.map_err(|e| e.to_string())?;
                        it.put(bexpr(k, &e));
                        later.put(bexpr(k, &e));
                    }
                }
                it.put(decl(index, offset, &d));
            }
            _ => it.put(line),
        }
    }
    let mut eager = Logger {
        log: Log::default(),
        lazy: false,
    };
    decode(&f, &mut eager).map_err(|e| format!("{e:?}"))?;
    if eager.log.end() != it.end() {
        return Err("the single pass hands out other records than the iterators".into());
    }
    let mut lazy = Logger {
        log: Log::default(),
        lazy: true,
    };
    let d = decode(&f, &mut lazy).map_err(|e| format!("{e:?}"))?;
    let mut blocks = Log::default();
    for &b in &d.state.blocks {
        decode_block(bytes, &d.state, b, |k, e| {
            blocks.put(bexpr(k, e));
            Ok::<(), ()>(())
        })
        .map_err(|e| format!("{e:?}"))?;
    }
    if lazy.log.end() != outer.end() {
        return Err("a lazy pass hands out other MAIN records than the iterator".into());
    }
    if d.unread != d.state.blocks.len() as u64 || blocks.end() != later.end() {
        return Err("decode_block reads other records than the block iterator".into());
    }
    Ok(())
}
