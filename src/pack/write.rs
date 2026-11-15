// The walk back (owners, numbers, the frontier's items) and the writer of
// the canonical layout (spec section 9).
//
// The walk back leaves in each expression's owner slot a number counted
// backwards: for an expression in MAIN, how many MAIN expressions come after
// it; for one in a block, how many of its block's expressions come after it.
// A reference from e to c is then the difference of their slots in both
// cases, so the forward writing needs nothing written before it and is cut
// into segments written on several workers; the main thread joins their
// output in order.

use super::pk::{rv, wv, Pk, FLAG, MAIN, NONE};
use super::{cant, inv, Stats, R};
use crate::format;
use std::collections::HashMap;
use std::io::Write;

const UNUSED: u32 = u32::MAX;
const USED: u32 = u32::MAX - 1;
// the bit of a k column entry the walk back sets on a frontier item
const KFLAG: u8 = 0x20;
// the bit of a block expression's slot after the walk back (below 2^31 expressions)
const BLOCK: u32 = 1 << 31;

struct Sink<'w, W: Write> {
    w: &'w mut W,
    total: u64,
}

impl<W: Write> Sink<'_, W> {
    fn put(&mut self, b: &[u8]) -> R<()> {
        if b.is_empty() {
            return Ok(());
        }
        self.w
            .write_all(b)
            .map_err(|e| cant!("cannot write: {e}"))?;
        self.total += b.len() as u64;
        Ok(())
    }
}

#[inline(always)]
unsafe fn pv(mut p: *mut u8, mut v: u64) -> *mut u8 {
    while v >= 128 {
        *p = (v as u8) | 128;
        p = p.add(1);
        v >>= 7;
    }
    *p = v as u8;
    p.add(1)
}

// Every declared name once (spec 5.2), checked on canonical names.
fn unique_names(pk: &Pk) -> R<()> {
    let mut by: Vec<u32> = vec![u32::MAX; pk.cn.count()];
    let mut q = 0usize;
    let mut di = 0u32;
    while q < pk.dmeta.len() {
        let cnt = pk.dmeta[q + 1] as usize;
        for &n in &pk.dmeta[q + 2..q + 2 + cnt] {
            let c = pk.canon[n as usize] as usize;
            if c == crate::canon::ANON as usize {
                // a structural error of MAIN (spec 5.2)
                return Err(inv!("declaration {di} declares the anonymous name"));
            }
            if by[c] != u32::MAX {
                let name = pk.cn.display(&pk.stream, c as u32);
                return Err(if by[c] == di {
                    inv!("declaration {di} declares {name} twice")
                } else {
                    inv!("{name} is declared twice (declarations {} and {di})", by[c])
                });
            }
            by[c] = di;
        }
        q += 2 + cnt;
        di += 1;
    }
    Ok(())
}

// A run of expressions one block owns: start..end, block o.
#[derive(Clone, Copy)]
struct Run {
    start: u32,
    end: u32,
    o: u32,
}

// Where a segment starts: in the stream at p (inside a run record with left
// expressions of it still to come, or at a record), at expression e0, with
// the ids and positions of the columns there.
#[derive(Clone, Copy, Default)]
struct Seg {
    p: usize,
    left: u32,
    e0: u32,
    e1: u32,
    name_id: usize,
    level_id: usize,
    di: u32,
    sn: usize,
    sl: usize,
    m0: u32,
}

// A declaration record of a segment: its offset in the segment's MAIN bytes,
// its INDEX kind, and for one with a block, where the block length goes.
struct Dec {
    off: usize,
    kind: u8,
    hole: usize,
    di: u32,
}

#[derive(Default)]
struct SegOut {
    main: Vec<u8>,
    decls: Vec<Dec>,
    // the records of the blocks' expressions in this segment, in pieces of
    // one block: (block, start, end) in arena
    arena: Vec<u8>,
    pieces: Vec<(u32, u32, u32)>,
    // per block from the segment's first declaration on: its first piece and
    // last piece; per piece the block's next one
    head: Vec<u32>,
    tail: Vec<u32>,
    next: Vec<u32>,
    // a block whose declaration came before the segment (never so)
    bad: bool,
    // where it ended, to check against where the next one starts
    end: (usize, u32, usize, usize, u32, usize, usize, u32),
}

// What the workers read: the columns, the owner slots as the walk back left
// them, the frontier items' bits, the stream.
struct Ctx<'a> {
    ow: *const u32,
    k: *const u8,
    a: *const u32,
    b: *const u32,
    nm: *const u32,
    lo: *const u64,
    // per 32 expressions: frontier items before them (high half), and which
    // of them are frontier items (low half)
    fw: *const u64,
    x: &'a [u8],
    s: &'a [u8],
    runs: &'a [Run],
    size: &'a [u32],
    name_f: &'a [u32],
    level_f: &'a [u32],
    mm: u32,
    top: u32,
    segs: &'a [Seg],
    // the buffers of segments already joined, for the next ones
    pool: std::sync::Mutex<Vec<SegOut>>,
    // columns given back once a segment is written
    kcol: &'a [u8],
    acol: &'a [u32],
    bcol: &'a [u32],
    ncol: &'a [u32],
}
unsafe impl Sync for Ctx<'_> {}

pub fn write<W: Write>(pk: Pk, w: &mut W, with_index: bool, threads: usize) -> R<Stats> {
    let mut pk = pk;
    let n = pk.exprs as usize;
    let nd = pk.decls as usize;
    if pk.names == u32::MAX || pk.levels == u32::MAX || pk.decls == u32::MAX {
        return Err(cant!("more than 2^32 - 1 names, levels or declarations"));
    }
    unique_names(&pk)?;
    let mut name_f: Vec<u32> = vec![UNUSED; pk.names as usize];
    let mut level_f: Vec<u32> = vec![UNUSED; pk.levels as usize];
    let mm: u32;
    let mut cols = std::mem::take(&mut pk.cols);
    if cols.k.len() != n || cols.a.len() != n || cols.b.len() != n || pk.owner.len() != n {
        return Err(cant!("internal: expression counts disagree"));
    }
    // the segments: where the reading saw each SEG-th expression start
    let threads = threads.max(1);
    let s = &pk.stream[..];
    let mut segs = vec![Seg {
        name_id: 1,
        level_id: 1,
        ..Seg::default()
    }];
    for x in &pk.segs {
        segs.push(Seg {
            p: x.p,
            left: x.left,
            e0: x.e0,
            name_id: x.name_id as usize,
            level_id: x.level_id as usize,
            di: x.di,
            ..Seg::default()
        });
    }
    if segs.windows(2).any(|w| w[1].e0 <= w[0].e0) || segs.last().unwrap().e0 as usize > n {
        return Err(cant!("internal: segments disagree"));
    }
    for j in 0..segs.len() {
        segs[j].e1 = if j + 1 < segs.len() {
            segs[j + 1].e0
        } else {
            n as u32
        };
    }
    for j in 0..segs.len() {
        segs[j].e1 = if j + 1 < segs.len() {
            segs[j + 1].e0
        } else {
            n as u32
        };
    }
    // INDEX's name table is all that needs the canonical names: made now
    // (beside the walk back on a worker), they are given back before writing
    let mut table: Vec<u8> = Vec::new();
    let table_now = with_index && threads <= 1;
    if table_now {
        table = name_table(&pk.cn, &pk.canon, &pk.dmeta, &pk.stream);
    }
    if !(with_index && !table_now) {
        give_back_names(&mut pk.cn, &mut pk.canon, &mut pk.dmeta);
    }
    // block sizes, by declaration
    let mut size: Vec<u32> = vec![0; nd];
    let mut runs: Vec<Run> = Vec::new();
    // frontier items: per 32 expressions, the items before them (high half)
    // and which of them are items (low half)
    let mut fw: Vec<u64> = vec![0; n.div_ceil(32)];
    // The walk back: an expression is owned by theorem T when only T's value
    // reaches it (through expressions T owns); every other one is in MAIN.
    // Children of owned expressions get FLAG: those in MAIN are frontier items.
    // It stops at each segment's start to note where the columns are there.
    // block expressions' slots get the top bit when no count can reach it
    let top = if n <= 1 << 31 { BLOCK } else { 0 };
    let (owp, kvp) = (pk.owner.as_mut_ptr(), cols.k.as_mut_ptr());
    let walked: R<u32> = std::thread::scope(|sc| {
        let th = if with_index && !table_now {
            let (cn, canon, dmeta) = (&pk.cn, &pk.canon[..], &pk.dmeta[..]);
            Some(sc.spawn(move || name_table(cn, canon, dmeta, s)))
        } else {
            None
        };
        let r = (|| -> R<u32> {
            unsafe {
                let mut wk = Wk {
                    ow: owp,
                    kv: kvp,
                    av: cols.a.as_ptr(),
                    bv: cols.b.as_ptr(),
                    nmv: cols.names.as_ptr(),
                    fw: fw.as_mut_ptr(),
                    ni: cols.names.len(),
                    li: cols.loffs.len(),
                    m: 0,
                };
                let mut e = n;
                for sg in segs.iter_mut().rev() {
                    let lo = sg.e0 as usize;
                    while e > lo {
                        let v = *wk.ow.add(e - 1) & !FLAG;
                        e = if v >= NONE {
                            walk_main(&mut wk, e, lo, &cols.x, &cols.loffs)
                        } else {
                            let c = walk_owned(
                                &mut wk,
                                e,
                                lo,
                                v,
                                size[v as usize],
                                top,
                                &cols.x,
                                &cols.loffs,
                                &mut name_f,
                                &mut level_f,
                            );
                            size[v as usize] = c.1;
                            runs.push(Run {
                                start: c.0 as u32,
                                end: e as u32,
                                o: v,
                            });
                            c.0
                        };
                    }
                    sg.sn = wk.ni;
                    sg.sl = wk.li;
                    // MAIN expressions after the start, for now
                    sg.m0 = wk.m;
                }
                if wk.ni != 0 || wk.li != 0 {
                    return Err(cant!("internal: records disagree"));
                }
                Ok(wk.m)
            }
        })();
        if let Some(h) = th {
            table = h.join().unwrap();
        }
        r
    });
    mm = walked?;
    give_back_names(&mut pk.cn, &mut pk.canon, &mut pk.dmeta);
    runs.reverse();
    let mut f0 = 0u64;
    for x in fw.iter_mut() {
        let c = (*x as u32).count_ones() as u64;
        *x |= f0 << 32;
        f0 += c;
    }
    for sg in segs.iter_mut() {
        sg.m0 = mm - sg.m0;
    }
    // the frontier's names and levels numbered in id order
    let mut f = 0u32;
    for x in name_f.iter_mut().filter(|x| **x == USED) {
        *x = f;
        f += 1;
    }
    f = 0;
    for x in level_f.iter_mut().filter(|x| **x == USED) {
        *x = f;
        f += 1;
    }

    let mut sink = Sink { w, total: 0 };
    let mut hd: Vec<u8> = format::MAGIC.to_vec();
    hd.extend_from_slice(&format::MAJOR.to_le_bytes());
    hd.extend_from_slice(&[0u8; 6]);
    sink.put(&hd)?;
    let moff = sink.total;
    if name_f[0] != UNUSED {
        sink.put(&[19, 0, 1])?;
    }
    if level_f[0] != UNUSED {
        sink.put(&[19, 1, 1])?;
    }

    // INDEX entries: kind, offset of the record's tag byte in MAIN, block length
    let mut ix_kind: Vec<u8> = Vec::new();
    let mut ix_off: Vec<u64> = Vec::new();
    let mut ix_blen: Vec<u64> = Vec::new();
    if with_index {
        ix_kind.reserve(nd);
        ix_off.reserve(nd);
    }
    // PROOFS grows while the columns already written are given back (its
    // pages are only taken as they are written).
    let mut proofs: Vec<u8> = Vec::with_capacity(n * 3 + n / 2 + 4096);
    let mut lazy = 0u64;
    // block parts of the segments joined so far whose declaration is still to come
    let mut carry: HashMap<u32, Vec<u8>> = HashMap::new();
    let mut prev_end = (0usize, 0u32, 1usize, 1usize, 0u32, 0usize, 0usize, 0u32);
    {
        let ctx = Ctx {
            ow: pk.owner.as_ptr(),
            k: cols.k.as_ptr(),
            a: cols.a.as_ptr(),
            b: cols.b.as_ptr(),
            nm: cols.names.as_ptr(),
            lo: cols.loffs.as_ptr(),
            fw: fw.as_ptr(),
            x: &cols.x,
            s,
            runs: &runs,
            size: &size,
            name_f: &name_f,
            level_f: &level_f,
            mm,
            top,
            segs: &segs,
            kcol: &cols.k,
            acol: &cols.a,
            bcol: &cols.b,
            ncol: &cols.names,
            pool: std::sync::Mutex::new(Vec::new()),
        };
        let mut join = |j: usize, so: SegOut| -> R<()> {
            let sg = &segs[j];
            let start = (
                sg.p,
                sg.e0,
                sg.name_id,
                sg.level_id,
                sg.di,
                sg.sn,
                sg.sl,
                sg.m0,
            );
            if j > 0 && start != prev_end {
                return Err(cant!("internal: segments disagree"));
            }
            prev_end = so.end;
            if so.bad {
                return Err(cant!("internal: a block before its segment"));
            }
            let (main, arena, pieces) = (&so.main, &so.arena, &so.pieces);
            let base = sg.di;
            let mut pos = 0usize;
            for d in &so.decls {
                if with_index {
                    sink.put(&main[pos..d.off])?;
                    pos = d.off;
                    ix_off.push(sink.total - moff);
                    ix_kind.push(d.kind);
                }
                if d.hole != usize::MAX {
                    sink.put(&main[pos..d.hole])?;
                    pos = d.hole;
                    let before = carry.remove(&d.di).unwrap_or_default();
                    let rel = (d.di - base) as usize;
                    let first = so.head.get(rel).copied().unwrap_or(u32::MAX);
                    let mut blen = before.len() as u64;
                    let mut q = first;
                    while q != u32::MAX {
                        let (_, a, b) = pieces[q as usize];
                        blen += (b - a) as u64;
                        q = so.next[q as usize];
                    }
                    let mut v = Vec::with_capacity(10);
                    wv(&mut v, blen);
                    sink.put(&v)?;
                    if with_index {
                        ix_blen.push(blen);
                    }
                    proofs.extend_from_slice(&before);
                    let mut q = first;
                    while q != u32::MAX {
                        let (_, a, b) = pieces[q as usize];
                        proofs.extend_from_slice(&arena[a as usize..b as usize]);
                        q = so.next[q as usize];
                    }
                    lazy += 1;
                }
            }
            sink.put(&main[pos..])?;
            // the blocks whose declarations come later
            for &(o, a, b) in pieces {
                if o >= so.end.4 {
                    carry
                        .entry(o)
                        .or_default()
                        .extend_from_slice(&arena[a as usize..b as usize]);
                }
            }
            ctx.pool.lock().unwrap().push(so);
            Ok(())
        };
        pipeline(
            threads,
            segs.len(),
            |j| unsafe { write_seg(&ctx, j) },
            &mut join,
        )?;
    }
    if prev_end.0 != s.len()
        || prev_end.1 as usize != n
        || prev_end.4 as usize != nd
        || prev_end.7 != mm
        || !carry.is_empty()
    {
        return Err(cant!("internal: counts disagree"));
    }
    drop(fw);
    drop(runs);
    cols.give_back();
    super::give_back(std::mem::take(&mut pk.owner));
    let mlen = sink.total - moff;
    let mut dir: Vec<(u16, u16, u64, u64)> =
        vec![(format::SEC_MAIN, format::MUST_UNDERSTAND, moff, mlen)];
    let poff = sink.total;
    let plen = proofs.len() as u64;
    if lazy > 0 {
        sink.put(&proofs)?;
        dir.push((format::SEC_PROOFS, format::MUST_UNDERSTAND, poff, plen));
    }
    super::give_back(proofs);
    let mut index_bytes = 0u64;
    if with_index {
        let ix = build_index(&ix_kind, &ix_off, &ix_blen, &table);
        let off = sink.total;
        sink.put(&ix)?;
        index_bytes = ix.len() as u64;
        dir.push((format::SEC_INDEX, 0, off, index_bytes));
    }
    let soff = sink.total;
    sink.put(&pk.meta)?;
    dir.push((format::SEC_SOURCE, 0, soff, pk.meta.len() as u64));
    let mut t: Vec<u8> = Vec::new();
    for x in [pk.names, pk.levels, mm, pk.decls] {
        t.extend_from_slice(&x.to_le_bytes());
    }
    t.extend_from_slice(&(dir.len() as u32).to_le_bytes());
    for &(id, fl, off, len) in &dir {
        t.extend_from_slice(&id.to_le_bytes());
        t.extend_from_slice(&fl.to_le_bytes());
        t.extend_from_slice(&0u32.to_le_bytes());
        t.extend_from_slice(&off.to_le_bytes());
        t.extend_from_slice(&len.to_le_bytes());
    }
    let tlen = 16 + 4 + 24 * dir.len() as u32 + 8;
    t.extend_from_slice(&tlen.to_le_bytes());
    t.extend_from_slice(&format::END_MAGIC);
    sink.put(&t)?;
    Ok(Stats {
        names: pk.names as u64,
        levels: pk.levels as u64,
        exprs: n as u64,
        main_exprs: mm as u64,
        decls: nd as u64,
        blocks: lazy,
        main_bytes: mlen,
        proofs_bytes: if lazy > 0 { plen } else { 0 },
        index_bytes,
        source_bytes: pk.meta.len() as u64,
        file_bytes: sink.total,
        parallel: false,
    })
}

// make(0..count) on up to `threads` workers, each result handed to join in
// order on this thread; the workers stay at most a few segments ahead.
fn pipeline<T: Send>(
    threads: usize,
    count: usize,
    make: impl Fn(usize) -> T + Sync,
    join: &mut impl FnMut(usize, T) -> R<()>,
) -> R<()> {
    if threads <= 1 || count <= 1 {
        for j in 0..count {
            join(j, make(j))?;
        }
        return Ok(());
    }
    use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
    use std::sync::{mpsc, Condvar, Mutex};
    let next = AtomicUsize::new(0);
    let stop = AtomicBool::new(false);
    // segments joined so far
    let done = Mutex::new(0usize);
    let cv = Condvar::new();
    let ahead = threads;
    let (tx, rx) = mpsc::channel::<(usize, T)>();
    std::thread::scope(|sc| {
        for _ in 0..threads.min(count) {
            let tx = tx.clone();
            let (next, stop, done, cv, make) = (&next, &stop, &done, &cv, &make);
            sc.spawn(move || loop {
                let j = next.fetch_add(1, Ordering::Relaxed);
                if j >= count {
                    break;
                }
                {
                    let mut d = done.lock().unwrap();
                    while j >= *d + ahead && !stop.load(Ordering::Relaxed) {
                        d = cv.wait(d).unwrap();
                    }
                }
                if stop.load(Ordering::Relaxed) {
                    break;
                }
                if tx.send((j, make(j))).is_err() {
                    break;
                }
            });
        }
        drop(tx);
        let mut wait: Vec<Option<T>> = (0..count).map(|_| None).collect();
        let mut j = 0usize;
        let res = (|| {
            while j < count {
                let Ok((i, r)) = rx.recv() else {
                    return Err(cant!("internal: a worker stopped"));
                };
                wait[i] = Some(r);
                while j < count {
                    let Some(r) = wait[j].take() else { break };
                    join(j, r)?;
                    j += 1;
                    *done.lock().unwrap() = j;
                    cv.notify_all();
                }
            }
            Ok(())
        })();
        if res.is_err() {
            stop.store(true, Ordering::Relaxed);
            cv.notify_all();
            drop(rx);
        }
        res
    })
}

// The segment j's MAIN bytes and block parts.
unsafe fn write_seg(cx: &Ctx, j: usize) -> SegOut {
    let sg = &cx.segs[j];
    let s = cx.s;
    let mut so = cx.pool.lock().unwrap().pop().unwrap_or_default();
    so.main.clear();
    so.decls.clear();
    so.arena.clear();
    so.pieces.clear();
    so.head.clear();
    so.tail.clear();
    so.next.clear();
    let mut st = St {
        e: sg.e0,
        sn: sg.sn,
        sl: sg.sl,
        mains: 0,
        r: cx.runs.partition_point(|r| r.end <= sg.e0),
        last: u32::MAX,
        base: sg.di,
    };
    let e1 = sg.e1;
    let mut p = sg.p;
    let (mut name_id, mut level_id, mut di) = (sg.name_id, sg.level_id, sg.di);
    let mut whole = true;
    if sg.left > 0 {
        let take = sg.left.min(e1 - st.e);
        let to = st.e + take;
        exprs(cx, &mut st, to, &mut so);
        whole = take == sg.left;
    }
    while whole && p < s.len() {
        let tag = s[p];
        match tag {
            1 | 2 => {
                let q0 = p;
                p += 1;
                rv(s, &mut p);
                let x = rv(s, &mut p);
                if tag == 1 {
                    p += x as usize;
                }
                so.main.extend_from_slice(&s[q0..p]);
                if cx.name_f[name_id] != UNUSED {
                    so.main.extend_from_slice(&[19, 0, 1]);
                }
                name_id += 1;
            }
            3..=6 => {
                let q0 = p;
                p += 1;
                rv(s, &mut p);
                if tag == 4 || tag == 5 {
                    rv(s, &mut p);
                }
                so.main.extend_from_slice(&s[q0..p]);
                if cx.level_f[level_id] != UNUSED {
                    so.main.extend_from_slice(&[19, 1, 1]);
                }
                level_id += 1;
            }
            20 => {
                if st.e == e1 {
                    break;
                }
                p += 1;
                let k = rv(s, &mut p) as u32;
                let take = k.min(e1 - st.e);
                let to = st.e + take;
                exprs(cx, &mut st, to, &mut so);
                if take < k {
                    break;
                }
            }
            _ => {
                // 18: a declaration
                p += 1;
                let kind = s[p];
                p += 1;
                let blocked = cx.size[di as usize] > 0;
                let off = so.main.len();
                let out = &mut so.main;
                out.push(18);
                // MAIN expressions before this record
                let mnext = (sg.m0 + st.mains) as u64;
                let (ow, mm) = (cx.ow, cx.mm as u64);
                let back = |c: u32| -> u64 { mnext + *ow.add(c as usize) as u64 + 1 - mm };
                let mut hole = usize::MAX;
                out.push(if blocked { 6 } else { kind });
                loop {
                    let t = s[p];
                    p += 1;
                    match t {
                        0 => {
                            let l = rv(s, &mut p) as usize;
                            out.extend_from_slice(&s[p..p + l]);
                            p += l;
                        }
                        1 | 2 if !blocked || t == 1 => {
                            let c = rv(s, &mut p) as u32;
                            wv(out, back(c));
                        }
                        2 => {
                            // the value: block length (joined later) and expression count
                            rv(s, &mut p);
                            hole = out.len();
                            wv(out, cx.size[di as usize] as u64);
                        }
                        _ => break,
                    }
                }
                so.decls.push(Dec {
                    off,
                    kind: if blocked { 6 } else { kind },
                    hole,
                    di,
                });
                di += 1;
            }
        }
    }
    so.end = (
        p,
        st.e,
        name_id,
        level_id,
        di,
        st.sn,
        st.sl,
        sg.m0 + st.mains,
    );
    // the columns of this segment are not read again
    let (e0, e1) = (sg.e0 as usize, sg.e1 as usize);
    super::give_back_range(cx.kcol, e0, e1);
    super::give_back_range(cx.acol, e0, e1);
    super::give_back_range(cx.bcol, e0, e1);
    super::give_back_range(cx.ncol, sg.sn, st.sn);
    so
}

// Where a worker is in its segment.
struct St {
    e: u32,
    sn: usize,
    sl: usize,
    mains: u32,
    // the next owned run, the block written last, the segment's first declaration
    r: usize,
    last: u32,
    base: u32,
}

// The expressions from st.e to end: MAIN ones into so.main, owned ones into
// their block's part.
#[inline(never)]
unsafe fn exprs(cx: &Ctx, st: &mut St, end: u32, so: &mut SegOut) {
    let runs = cx.runs;
    while st.e < end {
        while st.r < runs.len() && runs[st.r].end <= st.e {
            st.r += 1;
        }
        if st.r < runs.len() && runs[st.r].start <= st.e {
            let o = runs[st.r].o;
            let stop = runs[st.r].end.min(end);
            if st.last != o {
                if o < st.base {
                    so.bad = true;
                    st.e = stop;
                    continue;
                }
                let rel = (o - st.base) as usize;
                if rel >= so.head.len() {
                    so.head.resize(rel + 1, u32::MAX);
                    so.tail.resize(rel + 1, u32::MAX);
                }
                let ix = so.pieces.len() as u32;
                let at = so.arena.len() as u32;
                so.pieces.push((o, at, at));
                so.next.push(u32::MAX);
                match so.tail[rel] {
                    u32::MAX => so.head[rel] = ix,
                    t => so.next[t as usize] = ix,
                }
                so.tail[rel] = ix;
                st.last = o;
            }
            if cx.top != 0 {
                owned_run::<true>(cx, st, stop, cx.size[o as usize], &mut so.arena);
            } else {
                owned_run::<false>(cx, st, stop, cx.size[o as usize], &mut so.arena);
            }
            so.pieces.last_mut().unwrap().2 = so.arena.len() as u32;
        } else {
            let stop = if st.r < runs.len() {
                runs[st.r].start.min(end)
            } else {
                end
            };
            while st.e < stop {
                let cend = stop.min(st.e.saturating_add(32768));
                so.main.reserve(32768 * 24);
                main_run(cx, st, cend, &mut so.main);
            }
        }
    }
}

// The walk back's columns and where it is in them.
struct Wk {
    ow: *mut u32,
    kv: *mut u8,
    av: *const u32,
    bv: *const u32,
    nmv: *const u32,
    fw: *mut u64,
    // the binder names and leaves before the expression reached
    ni: usize,
    li: usize,
    // expressions in MAIN
    m: u32,
}

// Back from expression e - 1 while the expressions are in MAIN (owned by no
// declaration, or by several): their children are in MAIN too. Each one's
// slot takes the MAIN expressions after it. Returns how many expressions are
// left.
#[inline(never)]
unsafe fn walk_main(wk: &mut Wk, mut e: usize, lo: usize, xs: &[u8], loffs: &[u64]) -> usize {
    let (ow, kv, av, bv, fw) = (wk.ow, wk.kv, wk.av, wk.bv, wk.fw);
    let (mut ni, mut li, mut m) = (wk.ni, wk.li, wk.m);
    while e > lo {
        let i = e - 1;
        let x = *ow.add(i);
        if x & !FLAG < NONE {
            break;
        }
        *ow.add(i) = m;
        m += 1;
        let kind = *kv.add(i);
        if x & FLAG != 0 {
            *kv.add(i) = kind | KFLAG;
            *fw.add(i / 32) |= 1 << (i % 32);
        }
        if kind != 0 {
            if kind >= 2 {
                ni -= 1;
            }
            let p1 = ow.add(*av.add(i) as usize);
            *p1 = MAIN | (*p1 & FLAG);
            let p2 = ow.add(*bv.add(i) as usize);
            *p2 = MAIN | (*p2 & FLAG);
        } else {
            li -= 1;
            xchildren(
                xs,
                *loffs.get_unchecked(li) as usize,
                |c| {
                    let p = ow.add(c as usize);
                    *p = MAIN | (*p & FLAG);
                },
                |_| {},
                |_| {},
            );
        }
        e = i;
    }
    wk.ni = ni;
    wk.li = li;
    wk.m = m;
    e
}

// Back from expression e - 1 while declaration o owns the expressions: each
// child is owned by o too unless something else reaches it, and gets FLAG.
// Each one's slot takes the expressions of o after it, counting from c.
// Returns how many expressions are left and the new count.
#[allow(clippy::too_many_arguments)]
#[inline(never)]
unsafe fn walk_owned(
    wk: &mut Wk,
    mut e: usize,
    lo: usize,
    o: u32,
    mut c: u32,
    top: u32,
    xs: &[u8],
    loffs: &[u64],
    name_f: &mut [u32],
    level_f: &mut [u32],
) -> (usize, u32) {
    let (ow, kv, av, bv, nmv) = (wk.ow, wk.kv, wk.av, wk.bv, wk.nmv);
    let (mut ni, mut li) = (wk.ni, wk.li);
    let mark = |c: u32| {
        let p = ow.add(c as usize);
        let w = *p & !FLAG;
        let nw = if w == NONE || w == o { o } else { MAIN };
        *p = nw | FLAG;
    };
    while e > lo {
        let i = e - 1;
        if *ow.add(i) & !FLAG != o {
            break;
        }
        *ow.add(i) = c | top;
        c += 1;
        let kind = *kv.add(i);
        if kind != 0 {
            mark(*av.add(i));
            mark(*bv.add(i));
            if kind >= 2 {
                ni -= 1;
                *name_f.get_unchecked_mut(*nmv.add(ni) as usize) = USED;
            }
        } else {
            li -= 1;
            xchildren(
                xs,
                *loffs.get_unchecked(li) as usize,
                mark,
                |x| name_f[x as usize] = USED,
                |l| level_f[l as usize] = USED,
            );
        }
        e = i;
    }
    wk.ni = ni;
    wk.li = li;
    (e, c)
}

// The MAIN expressions from st.e to cend: their records into out (room for
// 24 bytes each reserved).
#[inline(never)]
unsafe fn main_run(cx: &Ctx, st: &mut St, cend: u32, out: &mut Vec<u8>) {
    let (ow, sk, sa, sb, snm, slo) = (cx.ow, cx.k, cx.a, cx.b, cx.nm, cx.lo);
    let (mut e, mut sn, mut sl) = (st.e, st.sn, st.sl);
    let mut ob = out.as_mut_ptr();
    let mut op = ob.add(out.len());
    while e < cend {
        let i = e as usize;
        let kx = *sk.add(i);
        let kind = (kx & 15) as u32;
        let oe = *ow.add(i);
        let mref = |c: u32| (*ow.add(c as usize) - oe) as u64;
        match kind {
            1 => {
                *op = 10;
                op = pv(op.add(1), mref(*sa.add(i)));
                op = pv(op, mref(*sb.add(i)));
            }
            2..=9 => {
                *op = if kind < 6 { 11 } else { 12 };
                *op.add(1) = ((kind - 2) & 3) as u8;
                op = pv(op.add(2), *snm.add(sn) as u64);
                sn += 1;
                op = pv(op, mref(*sa.add(i)));
                op = pv(op, mref(*sb.add(i)));
            }
            _ => {
                let lo = *slo.add(sl) as usize;
                sl += 1;
                out.set_len(op.offset_from(ob) as usize);
                main_other(cx.x, lo, out, mref);
                out.reserve(32768 * 24);
                ob = out.as_mut_ptr();
                op = ob.add(out.len());
            }
        }
        if kx & KFLAG != 0 {
            *op = 19;
            *op.add(1) = 2;
            *op.add(2) = 1;
            op = op.add(3);
        }
        e += 1;
    }
    out.set_len(op.offset_from(ob) as usize);
    st.mains += e - st.e;
    st.e = e;
    st.sn = sn;
    st.sl = sl;
}

// The expressions from st.e to stop, all of the block of size `size`: their
// records into its part.
#[inline(never)]
unsafe fn owned_run<const TOP: bool>(
    cx: &Ctx,
    st: &mut St,
    stop: u32,
    size: u32,
    buf: &mut Vec<u8>,
) {
    let (ow, sk, sa, sb, snm, slo, fw) = (cx.ow, cx.k, cx.a, cx.b, cx.nm, cx.lo, cx.fw);
    let (mut e, mut sn, mut sl) = (st.e, st.sn, st.sl);
    buf.reserve(64);
    let mut cb = buf.as_mut_ptr();
    let mut cp = cb.add(buf.len());
    let mut ce = cb.add(buf.capacity());
    let nf = cx.name_f.as_ptr();
    while e < stop {
        let i = e as usize;
        if (ce.offset_from(cp) as usize) < 64 {
            buf.set_len(cp.offset_from(cb) as usize);
            let l = buf.len();
            buf.reserve(l.max(256));
            cb = buf.as_mut_ptr();
            cp = cb.add(buf.len());
            ce = cb.add(buf.capacity());
        }
        let kind = (*sk.add(i) & 15) as u32;
        let oe = *ow.add(i);
        let er = |c: u32| -> u64 { owned_ref::<TOP>(ow, fw, oe, size, c) };
        match kind {
            1 => {
                *cp = 10;
                cp = pv(cp.add(1), er(*sa.add(i)));
                cp = pv(cp, er(*sb.add(i)));
            }
            2..=9 => {
                *cp = if kind < 6 { 11 } else { 12 };
                *cp.add(1) = ((kind - 2) & 3) as u8;
                cp = pv(cp.add(2), *nf.add(*snm.add(sn) as usize) as u64);
                sn += 1;
                cp = pv(cp, er(*sa.add(i)));
                cp = pv(cp, er(*sb.add(i)));
            }
            _ => {
                let lo = *slo.add(sl) as usize;
                sl += 1;
                buf.set_len(cp.offset_from(cb) as usize);
                owned_other(cx.x, lo, buf, &er, cx.name_f, cx.level_f);
                buf.reserve(64);
                cb = buf.as_mut_ptr();
                cp = cb.add(buf.len());
                ce = cb.add(buf.capacity());
            }
        }
        e += 1;
    }
    buf.set_len(cp.offset_from(cb) as usize);
    st.e = e;
    st.sn = sn;
    st.sl = sl;
}

// The reference from an expression of a block of `size` expressions, whose
// slot is oe, to c: back to an expression of the block, or to a frontier
// item (spec 9).
#[inline(always)]
unsafe fn owned_ref<const TOP: bool>(
    ow: *const u32,
    fw: *const u64,
    oe: u32,
    size: u32,
    c: u32,
) -> u64 {
    if TOP {
        // the slots of block expressions have the top bit
        let v = *ow.add(c as usize);
        if v & BLOCK != 0 {
            return (v - oe) as u64;
        }
        let w = *fw.add(c as usize / 32);
        let b = c % 32;
        let before = (w >> 32) + ((w as u32) & ((1u32 << b) - 1)).count_ones() as u64;
        return (size - 1 - (oe & !BLOCK)) as u64 + 1 + before;
    }
    let w = *fw.add(c as usize / 32);
    let b = c % 32;
    if (w >> b) & 1 != 0 {
        let before = (w >> 32) + ((w as u32) & ((1u32 << b) - 1)).count_ones() as u64;
        (size - 1 - oe) as u64 + 1 + before
    } else {
        (*ow.add(c as usize) - oe) as u64
    }
}

// The INDEX section (spec 6a.1): the declarations, then the name table.
fn build_index(kinds: &[u8], offs: &[u64], blens: &[u64], table: &[u8]) -> Vec<u8> {
    let nd = kinds.len();
    let mut ix: Vec<u8> = Vec::with_capacity(nd * 4 + table.len() + 1024);
    format::put_varint(&mut ix, nd as u64);
    let mut prev = 0u64;
    let mut b = 0usize;
    for i in 0..nd {
        ix.push(kinds[i]);
        format::put_varint(&mut ix, offs[i] - prev);
        prev = offs[i];
        if kinds[i] == 6 {
            format::put_varint(&mut ix, blens[b]);
            b += 1;
        }
    }
    ix.extend_from_slice(table);
    ix
}

// The canonical names and the declarations' names, not needed any more.
fn give_back_names(cn: &mut crate::canon::Canon, canon: &mut Vec<u32>, dmeta: &mut Vec<u32>) {
    std::mem::take(cn).give_back();
    super::give_back(std::mem::take(canon));
    super::give_back(std::mem::take(dmeta));
}

// INDEX's name table: every declared name, sorted by key, front-coded.
fn name_table(cn: &crate::canon::Canon, canon: &[u32], dmeta: &[u32], stream: &[u8]) -> Vec<u8> {
    let mut ix: Vec<u8> = Vec::new();
    let mut arena: Vec<u8> = Vec::new();
    let mut keys: Vec<(usize, usize, u32)> = Vec::new();
    let mut q = 0usize;
    let mut di = 0u32;
    while q < dmeta.len() {
        let cnt = dmeta[q + 1] as usize;
        for &nm in &dmeta[q + 2..q + 2 + cnt] {
            let c = canon[nm as usize];
            let start = arena.len();
            cn.key(stream, c, &mut arena);
            keys.push((start, arena.len(), di));
        }
        q += 2 + cnt;
        di += 1;
    }
    let key = |k: &(usize, usize, u32)| &arena[k.0..k.1];
    keys.sort_unstable_by(|a, b| key(a).cmp(key(b)));
    format::put_varint(&mut ix, keys.len() as u64);
    let mut last: &[u8] = &[];
    for k in &keys {
        let cur = key(k);
        let shared = last
            .iter()
            .zip(cur.iter())
            .take_while(|(x, y)| x == y)
            .count();
        format::put_varint(&mut ix, shared as u64);
        format::put_varint(&mut ix, (cur.len() - shared) as u64);
        ix.extend_from_slice(&cur[shared..]);
        format::put_varint(&mut ix, k.2 as u64);
        last = cur;
    }
    ix
}

// The parts of an expression record of xbuf at off: expression children,
// its name, its levels.
#[inline(always)]
fn xchildren(
    xb: &[u8],
    off: usize,
    mut ch: impl FnMut(u32),
    mut name: impl FnMut(u32),
    mut level: impl FnMut(u32),
) {
    let mut q = off + 1;
    match xb[off] {
        8 => level(rv(xb, &mut q) as u32),
        9 => {
            name(rv(xb, &mut q) as u32);
            let k = rv(xb, &mut q);
            for _ in 0..k {
                level(rv(xb, &mut q) as u32);
            }
        }
        13 => {
            name(rv(xb, &mut q) as u32);
            for _ in 0..3 {
                ch(rv(xb, &mut q) as u32);
            }
        }
        16 => {
            name(rv(xb, &mut q) as u32);
            rv(xb, &mut q);
            ch(rv(xb, &mut q) as u32);
        }
        _ => {}
    }
}

// Where the record of section 9 at off ends.
fn rec_end(xb: &[u8], off: usize) -> usize {
    let mut q = off + 1;
    match xb[off] {
        7 | 8 => {
            rv(xb, &mut q);
        }
        9 => {
            rv(xb, &mut q);
            let k = rv(xb, &mut q);
            for _ in 0..k {
                rv(xb, &mut q);
            }
        }
        13 => {
            for _ in 0..4 {
                rv(xb, &mut q);
            }
        }
        14 | 15 => {
            let l = rv(xb, &mut q) as usize;
            q += l;
        }
        16 => {
            for _ in 0..3 {
                rv(xb, &mut q);
            }
        }
        _ => unreachable!(),
    }
    q
}

#[inline(never)]
fn main_other(xb: &[u8], off: usize, out: &mut Vec<u8>, mref: impl Fn(u32) -> u64) {
    let tag = xb[off];
    let mut q = off + 1;
    match tag {
        13 => {
            out.push(13);
            wv(out, rv(xb, &mut q));
            for _ in 0..3 {
                let c = rv(xb, &mut q) as u32;
                wv(out, mref(c));
            }
        }
        16 => {
            out.push(16);
            wv(out, rv(xb, &mut q));
            wv(out, rv(xb, &mut q));
            let c = rv(xb, &mut q) as u32;
            wv(out, mref(c));
        }
        _ => {
            let end = rec_end(xb, off);
            out.extend_from_slice(&xb[off..end]);
        }
    }
}

#[inline(never)]
fn owned_other(
    xb: &[u8],
    off: usize,
    buf: &mut Vec<u8>,
    er: &dyn Fn(u32) -> u64,
    name_f: &[u32],
    level_f: &[u32],
) {
    let tag = xb[off];
    let mut q = off + 1;
    buf.push(tag);
    match tag {
        7 => {
            wv(buf, rv(xb, &mut q));
        }
        8 => {
            let l = rv(xb, &mut q) as usize;
            wv(buf, level_f[l] as u64);
        }
        9 => {
            let n = rv(xb, &mut q) as usize;
            wv(buf, name_f[n] as u64);
            let k = rv(xb, &mut q);
            wv(buf, k);
            for _ in 0..k {
                let l = rv(xb, &mut q) as usize;
                wv(buf, level_f[l] as u64);
            }
        }
        13 => {
            let n = rv(xb, &mut q) as usize;
            wv(buf, name_f[n] as u64);
            for _ in 0..3 {
                let c = rv(xb, &mut q) as u32;
                wv(buf, er(c));
            }
        }
        14 | 15 => {
            buf.pop();
            let end = rec_end(xb, off);
            buf.extend_from_slice(&xb[off..end]);
        }
        16 => {
            let n = rv(xb, &mut q) as usize;
            wv(buf, name_f[n] as u64);
            wv(buf, rv(xb, &mut q));
            let c = rv(xb, &mut q) as u32;
            wv(buf, er(c));
        }
        _ => unreachable!(),
    }
}
