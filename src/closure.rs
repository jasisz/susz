//! The dependency closure of some declarations, shared by `slice` and
//! `axioms`: the first two of slice's passes (see [`crate::slice`]).
//!
//! 1. Scan: MAIN through [`decode`], every check inline. Each MAIN expression
//!    is kept as a kind byte and two u32 (its children, or the name of a
//!    constant or projection), each declaration as the list of expressions
//!    and names it refers to. The reader's own state stays too: canonical
//!    names, declaring declarations, frontier tables and block positions.
//! 2. Closure, on those tables: a declaration needs its expressions, its
//!    mutual (`all`) and inductive companions, and the declarations of the
//!    constants and projections in them, and of those in its proof block. A
//!    quotient needs all four quotient declarations, a Nat literal `Nat`, a
//!    string literal `String`, `Char`, `List` and their constructors
//!    (spec A.9).

use crate::canon::{Part, ANON};
use crate::read::{
    decode, decode_block, BlockRef, Decl, Expr, Failure, File, Ref, State, Stop, Visit,
};
use std::convert::Infallible;
use std::fmt;

// ---------------------------------------------------------------------------
// Bit sets

pub(crate) struct Bits(pub(crate) Vec<u64>);

impl Bits {
    pub(crate) fn new(n: usize) -> Bits {
        Bits(vec![0; n.div_ceil(64)])
    }
    #[inline(always)]
    pub(crate) fn get(&self, i: u32) -> bool {
        self.0[(i >> 6) as usize] >> (i & 63) & 1 != 0
    }
    /// Sets bit i; true when it was not set before.
    #[inline(always)]
    pub(crate) fn set(&mut self, i: u32) -> bool {
        let w = &mut self.0[(i >> 6) as usize];
        let m = 1u64 << (i & 63);
        let new = *w & m == 0;
        *w |= m;
        new
    }
    pub(crate) fn clear(&mut self, i: u32) {
        self.0[(i >> 6) as usize] &= !(1u64 << (i & 63));
    }
    pub(crate) fn count(&self) -> u64 {
        self.0.iter().map(|w| w.count_ones() as u64).sum()
    }
}

// ---------------------------------------------------------------------------
// What records refer to

#[inline(always)]
fn main_id(r: &Ref) -> u32 {
    match r {
        Ref::Main(i) => *i,
        // MAIN expressions only refer to MAIN expressions
        Ref::Block(_) => unreachable!("a block reference in MAIN"),
    }
}

// The expressions a declaration refers to.
fn decl_exprs(d: &Decl, f: &mut impl FnMut(u32)) {
    match d {
        Decl::Axiom { head, .. } | Decl::Quot { head, .. } | Decl::ThmBlock { head, .. } => {
            f(head.ty)
        }
        Decl::Defn { head, value, .. }
        | Decl::Thm { head, value, .. }
        | Decl::Opaque { head, value, .. } => {
            f(head.ty);
            f(*value);
        }
        Decl::Inductive(ind) => {
            for t in &ind.types {
                f(t.head.ty);
            }
            for c in &ind.ctors {
                f(c.head.ty);
            }
            for r in &ind.recs {
                f(r.head.ty);
                for x in &r.rules {
                    f(x.rhs);
                }
            }
        }
    }
}

// The names of other declarations a declaration lists: its mutual block
// (`all`), an inductive's constructors, a constructor's inductive, a rule's
// constructor.
pub(crate) fn decl_dep_names(d: &Decl, f: &mut impl FnMut(u32)) {
    match d {
        Decl::Axiom { .. } | Decl::Quot { .. } => {}
        Decl::Defn { all, .. }
        | Decl::Thm { all, .. }
        | Decl::Opaque { all, .. }
        | Decl::ThmBlock { all, .. } => all.iter().for_each(&mut *f),
        Decl::Inductive(ind) => {
            for t in &ind.types {
                t.all.iter().for_each(&mut *f);
                t.ctors.iter().for_each(&mut *f);
            }
            for c in &ind.ctors {
                f(c.induct);
            }
            for r in &ind.recs {
                r.all.iter().for_each(&mut *f);
                for x in &r.rules {
                    f(x.ctor);
                }
            }
        }
    }
}

// The names and levels an expression holds.
pub(crate) fn expr_marks(e: &Expr, names: &mut Bits, levels: &mut Bits) {
    match e {
        Expr::Sort(l) => {
            levels.set(*l);
        }
        Expr::Const(n, us) => {
            names.set(*n);
            for u in us.iter() {
                levels.set(u);
            }
        }
        Expr::Lam(_, n, ..) | Expr::Pi(_, n, ..) | Expr::Let(n, ..) | Expr::Proj(n, ..) => {
            names.set(*n);
        }
        Expr::BVar(_) | Expr::App(..) | Expr::Nat(_) | Expr::Str(_) => {}
    }
}

// ---------------------------------------------------------------------------
// Pass 1: the tables

const K_NONE: u8 = 0;
const K_PAIR: u8 = 1; // app, lam, forallE: a, b
const K_LET: u8 = 2; // a type, b value; the body in `lets`
const K_CONST: u8 = 3; // a name
const K_PROJ: u8 = 4; // a struct, b name
const K_NAT: u8 = 5;
const K_STR: u8 = 6;

const NAME_DEP: u64 = 1 << 32;

#[derive(Default)]
struct Scan {
    ek: Vec<u8>,
    ea: Vec<u32>,
    eb: Vec<u32>,
    // (let expression, its body), by expression id
    lets: Vec<(u32, u32)>,
    // declaration i refers to deps[doff[i]..doff[i + 1]]: an expression id,
    // or NAME_DEP | a name id
    doff: Vec<u64>,
    deps: Vec<u64>,
    quots: Vec<u32>,
    // every axiom declaration, by index
    axioms: Vec<u32>,
}

impl Scan {
    fn new(exprs_hint: usize, decls_hint: usize) -> Scan {
        let mut doff = Vec::with_capacity(decls_hint + 1);
        doff.push(0);
        Scan {
            ek: Vec::with_capacity(exprs_hint),
            ea: Vec::with_capacity(exprs_hint),
            eb: Vec::with_capacity(exprs_hint),
            doff,
            deps: Vec::with_capacity(decls_hint * 3),
            ..Scan::default()
        }
    }
    #[inline(always)]
    fn push(&mut self, k: u8, a: u32, b: u32) {
        self.ek.push(k);
        self.ea.push(a);
        self.eb.push(b);
    }
}

impl<'a> Visit<'a> for Scan {
    type Error = Infallible;
    #[inline]
    fn expr(&mut self, id: u32, e: &Expr<'a>) -> Result<(), Infallible> {
        match e {
            Expr::App(f, a) => self.push(K_PAIR, main_id(f), main_id(a)),
            Expr::Lam(_, _, t, b) | Expr::Pi(_, _, t, b) => {
                self.push(K_PAIR, main_id(t), main_id(b))
            }
            Expr::Let(_, t, v, b) => {
                self.push(K_LET, main_id(t), main_id(v));
                self.lets.push((id, main_id(b)));
            }
            Expr::Const(n, _) => self.push(K_CONST, *n, 0),
            Expr::Proj(n, _, x) => self.push(K_PROJ, main_id(x), *n),
            Expr::Nat(_) => self.push(K_NAT, 0, 0),
            Expr::Str(_) => self.push(K_STR, 0, 0),
            Expr::BVar(_) | Expr::Sort(_) => self.push(K_NONE, 0, 0),
        }
        Ok(())
    }
    fn open_block(&mut self, _: &BlockRef) -> bool {
        false
    }
    fn decl(&mut self, index: u32, _: u64, d: &Decl<'a>) -> Result<(), Infallible> {
        decl_exprs(d, &mut |e| self.deps.push(e as u64));
        decl_dep_names(d, &mut |n| self.deps.push(NAME_DEP | n as u64));
        self.doff.push(self.deps.len() as u64);
        match d {
            Decl::Quot { .. } => self.quots.push(index),
            Decl::Axiom { .. } => self.axioms.push(index),
            _ => {}
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Pass 2: the closure

struct Closure<'s> {
    bytes: &'s [u8],
    st: &'s State,
    scan: &'s Scan,
    decls: Bits,
    exprs: Bits,
    names: Bits,
    levels: Bits,
    dstack: Vec<u32>,
    estack: Vec<u32>,
    nat: bool,
    str: bool,
    quot_done: bool,
    nat_done: bool,
    str_done: bool,
    block_exprs: u64,
}

impl<'s> Closure<'s> {
    fn decl_of_name(&self, n: u32) -> Option<u32> {
        let c = *self.st.name_canon.get(n as usize)?;
        let d = *self.st.canon_decl.get(c as usize)?;
        (d != u32::MAX).then_some(d)
    }
    #[inline]
    fn need_decl(&mut self, d: u32) {
        if self.decls.set(d) {
            self.dstack.push(d);
        }
    }
    #[inline]
    fn need_name_decl(&mut self, n: u32) {
        if let Some(d) = self.decl_of_name(n) {
            self.need_decl(d);
        }
    }
    #[inline]
    fn need_expr(&mut self, e: u32) {
        if !self.exprs.get(e) {
            self.estack.push(e);
        }
    }
    fn need_named(&mut self, parts: &[&str]) {
        let mut c = ANON;
        for p in parts {
            match self.st.canon.find(self.bytes, c, Part::Str(p.as_bytes())) {
                Some(x) => c = x,
                None => return,
            }
        }
        if let Some(&d) = self.st.canon_decl.get(c as usize) {
            if d != u32::MAX {
                self.need_decl(d);
            }
        }
    }

    fn run(&mut self) -> Result<(), Failure> {
        loop {
            while let Some(e) = self.estack.pop() {
                if !self.exprs.set(e) {
                    continue;
                }
                let (a, b) = (self.scan.ea[e as usize], self.scan.eb[e as usize]);
                match self.scan.ek[e as usize] {
                    K_PAIR => {
                        self.need_expr(a);
                        self.need_expr(b);
                    }
                    K_LET => {
                        self.need_expr(a);
                        self.need_expr(b);
                        let lets = &self.scan.lets;
                        let i = lets.partition_point(|x| x.0 < e);
                        self.need_expr(lets[i].1);
                    }
                    K_CONST => self.need_name_decl(a),
                    K_PROJ => {
                        self.need_expr(a);
                        self.need_name_decl(b);
                    }
                    K_NAT => self.nat = true,
                    K_STR => self.str = true,
                    _ => {}
                }
            }
            if let Some(d) = self.dstack.pop() {
                self.decl(d)?;
                continue;
            }
            // what literals stand for (spec A.9), and the quotient's four
            if self.nat && !self.nat_done {
                self.nat_done = true;
                self.need_named(&["Nat"]);
                continue;
            }
            if self.str && !self.str_done {
                self.str_done = true;
                for p in [
                    &["String"][..],
                    &["String", "mk"],
                    &["String", "ofList"],
                    &["Char"],
                    &["Char", "ofNat"],
                    &["List"],
                ] {
                    self.need_named(p);
                }
                continue;
            }
            break;
        }
        Ok(())
    }

    fn decl(&mut self, d: u32) -> Result<(), Failure> {
        let (from, to) = (
            self.scan.doff[d as usize] as usize,
            self.scan.doff[d as usize + 1] as usize,
        );
        for i in from..to {
            let x = self.scan.deps[i];
            if x & NAME_DEP != 0 {
                self.need_name_decl(x as u32);
            } else {
                self.need_expr(x as u32);
            }
        }
        if !self.quot_done && self.scan.quots.binary_search(&d).is_ok() {
            self.quot_done = true;
            for i in 0..self.scan.quots.len() {
                self.need_decl(self.scan.quots[i]);
            }
        }
        let (st, bytes) = (self.st, self.bytes);
        if let Ok(i) = st.blocks.binary_search_by_key(&d, |b| b.decl) {
            let b = st.blocks[i];
            self.block_exprs += b.exprs;
            let r = decode_block(bytes, st, b, |_, e| {
                self.block_expr(e);
                Ok::<(), Infallible>(())
            });
            match r {
                Ok(()) => {}
                Err(Stop::File(f)) => return Err(f),
                Err(Stop::Visitor(x)) => match x {},
            }
        }
        Ok(())
    }

    fn block_expr(&mut self, e: &Expr) {
        expr_marks(e, &mut self.names, &mut self.levels);
        let r = |s: &mut Self, x: &Ref| {
            if let Ref::Main(i) = x {
                s.need_expr(*i);
            }
        };
        match e {
            Expr::Const(n, _) => self.need_name_decl(*n),
            Expr::Proj(n, _, x) => {
                self.need_name_decl(*n);
                r(self, x);
            }
            Expr::App(a, b) | Expr::Lam(_, _, a, b) | Expr::Pi(_, _, a, b) => {
                r(self, a);
                r(self, b);
            }
            Expr::Let(_, t, v, b) => {
                r(self, t);
                r(self, v);
                r(self, b);
            }
            Expr::Nat(_) => self.nat = true,
            Expr::Str(_) => self.str = true,
            Expr::BVar(_) | Expr::Sort(_) => {}
        }
    }
}

// The declarations `roots` names, as a bit set over declarations; how many.
fn find_roots(
    bytes: &[u8],
    st: &State,
    roots: &[String],
    prefixes: &[String],
    decls: &mut Bits,
) -> Result<u64, CloseError> {
    let mut found = vec![false; roots.len()];
    let mut n = 0u64;
    let mut keep = |d: u32, decls: &mut Bits| {
        if decls.set(d) {
            n += 1;
        }
    };
    // a root whose components are all strings: looked up directly
    for (i, r) in roots.iter().enumerate() {
        let mut c = ANON;
        for p in r.split('.') {
            match st.canon.find(bytes, c, Part::Str(p.as_bytes())) {
                Some(x) => c = x,
                None => {
                    c = ANON;
                    break;
                }
            }
        }
        if let Some(&d) = st.canon_decl.get(c as usize) {
            if c != ANON && d != u32::MAX {
                found[i] = true;
                keep(d, decls);
            }
        }
    }
    // the rest (numeric components, dots inside components) and the
    // prefixes: by the dotted form of every declared name
    if !prefixes.is_empty() || found.iter().any(|f| !f) {
        let want: std::collections::HashMap<&str, usize> = roots
            .iter()
            .enumerate()
            .filter(|(i, _)| !found[*i])
            .map(|(i, r)| (r.as_str(), i))
            .collect();
        for (c, &d) in st.canon_decl.iter().enumerate() {
            if d == u32::MAX {
                continue;
            }
            let s = st.canon.display(bytes, c as u32);
            if let Some(&i) = want.get(s.as_str()) {
                found[i] = true;
                keep(d, decls);
            }
            if prefixes.iter().any(|p| s.starts_with(p.as_str())) {
                keep(d, decls);
            }
        }
    }
    let missing: Vec<String> = roots
        .iter()
        .zip(&found)
        .filter(|(_, f)| !**f)
        .map(|(r, _)| r.clone())
        .collect();
    if !missing.is_empty() {
        return Err(CloseError::NotFound(missing));
    }
    if n == 0 {
        return Err(CloseError::Empty);
    }
    Ok(n)
}

// ---------------------------------------------------------------------------
// Both passes

/// Where the closure starts.
pub(crate) enum Roots<'o> {
    /// The declarations named exactly so, and every declaration whose
    /// dotted name starts with one of the prefixes.
    Named {
        roots: &'o [String],
        prefixes: &'o [String],
    },
    /// Every declaration. The closure is then every declaration, so only
    /// `decls` is filled in, and no proof block is read.
    All,
}

pub(crate) enum CloseError {
    /// The input failed a check (rejected or declined).
    File(Failure),
    /// Roots that name no declaration.
    NotFound(Vec<String>),
    /// No root given, or no declaration matched the prefixes.
    Empty,
}

/// The closure, and what of the reader's state its users need.
pub(crate) struct Closed {
    /// The reader's state after MAIN: counts, canonical names.
    pub(crate) st: State,
    /// How many declarations the roots name.
    pub(crate) roots: u64,
    /// The declarations, MAIN expressions, names and levels needed (names
    /// and levels only those of the proof blocks read; the rest is left to
    /// the caller).
    pub(crate) decls: Bits,
    pub(crate) exprs: Bits,
    pub(crate) names: Bits,
    pub(crate) levels: Bits,
    /// Expressions in the proof blocks needed.
    pub(crate) block_exprs: u64,
    /// Every axiom declaration of the file, by index, in file order.
    pub(crate) axioms: Vec<u32>,
}

/// Reads MAIN of `f` (the file `bytes`) and closes `roots` under dependency.
pub(crate) fn close(
    bytes: &[u8],
    f: &File,
    roots: Roots,
    clock: &mut Clock,
) -> Result<Closed, CloseError> {
    let main_len = f.section(crate::format::SEC_MAIN).map_or(0, |s| s.length);
    let hint = |c: u32, per: u64| (c as u64).min(main_len / per) as usize;

    // 1. the tables
    let mut scan = Scan::new(hint(f.counts[2], 2), hint(f.counts[3], 8));
    let st = match decode(f, &mut scan) {
        Ok(d) => d.state,
        Err(Stop::File(e)) => return Err(CloseError::File(e)),
        Err(Stop::Visitor(x)) => match x {},
    };
    let (n_names, n_levels, n_exprs, n_decls) = (st.names, st.levels, st.exprs, st.decls);
    clock.lap(format_args!(
        "read MAIN: {} names, {} levels, {} expressions, {} declarations",
        n_names - 1,
        n_levels - 1,
        n_exprs,
        n_decls
    ));

    // 2. the closure
    let mut cl = Closure {
        bytes,
        st: &st,
        scan: &scan,
        decls: Bits::new(n_decls as usize),
        exprs: Bits::new(n_exprs as usize),
        names: Bits::new(n_names as usize),
        levels: Bits::new(n_levels as usize),
        dstack: Vec::new(),
        estack: Vec::new(),
        nat: false,
        str: false,
        quot_done: false,
        nat_done: false,
        str_done: false,
        block_exprs: 0,
    };
    let all = matches!(roots, Roots::All);
    let n_roots = match roots {
        Roots::Named { roots, prefixes } => {
            let n = find_roots(bytes, &st, roots, prefixes, &mut cl.decls)?;
            for (w, &x) in cl.decls.0.iter().enumerate() {
                let mut x = x;
                while x != 0 {
                    cl.dstack.push((w * 64) as u32 + x.trailing_zeros());
                    x &= x - 1;
                }
            }
            cl.dstack.reverse();
            cl.run().map_err(CloseError::File)?;
            n
        }
        Roots::All => {
            for d in 0..n_decls {
                cl.decls.set(d);
            }
            n_decls as u64
        }
    };
    let Closure {
        decls,
        exprs,
        names,
        levels,
        block_exprs,
        ..
    } = cl;
    let axioms = std::mem::take(&mut scan.axioms);
    drop(scan);
    if all {
        clock.lap(format_args!("closure: every declaration, {n_decls}"));
    } else {
        clock.lap(format_args!(
            "closure: {} declarations, {} MAIN expressions, {} in proof blocks",
            decls.count(),
            exprs.count(),
            block_exprs
        ));
    }
    Ok(Closed {
        st,
        roots: n_roots,
        decls,
        exprs,
        names,
        levels,
        block_exprs,
        axioms,
    })
}

pub(crate) struct Clock {
    pub(crate) what: &'static str,
    pub(crate) on: bool,
    pub(crate) t: std::time::Instant,
}

impl Clock {
    pub(crate) fn lap(&mut self, what: impl fmt::Display) {
        if self.on {
            eprintln!(
                "{}: {what} ({:.1} s)",
                self.what,
                self.t.elapsed().as_secs_f64()
            );
            self.t = std::time::Instant::now();
        }
    }
}
