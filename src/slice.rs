//! Slicing: a Susz file that holds only some declarations (the roots) and
//! everything they depend on, in the original declaration order.
//!
//! Three passes over MAIN, none of them over PROOFS; a proof block is only
//! decoded when its theorem is needed.
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
//!    (spec A.9). Then the tables are dropped.
//! 3. Names and levels: MAIN again, marking the names and levels the needed
//!    records use, then their prefixes and parts.
//! 4. Output: MAIN again, the needed records (and the needed blocks, right
//!    before their theorems, as `unpack` writes them) handed to the packer's
//!    own reader state (`pack::pk::Pk`) and written by the packer's writer.
//!    So the output is the canonical Susz file of the export that keeps
//!    only those records, in their order: slicing every declaration of a
//!    canonical file gives back its bytes.
//!
//! New ids are ranks in bit sets (about 1.5 bits per name, level and MAIN
//! expression of the input), so no id map grows with the input.

use crate::canon::{Part, ANON};
use crate::pack::json::J;
use crate::pack::pk::Pk;
use crate::pack::{self, Options, PackError, Stats};
use crate::read::{
    decode, decode_block, BlockRef, Component, Decl, Expr, Failure, File, Head, Hints, Ids, Level,
    Ref, State, Stop, Visit,
};
use std::convert::Infallible;
use std::fmt;

/// What to keep.
#[derive(Debug, Clone, Default)]
pub struct SliceOptions {
    /// Declarations named exactly so (dotted form, as `verify` prints names).
    pub roots: Vec<String>,
    /// Every declaration whose dotted name starts with one of these strings.
    pub prefixes: Vec<String>,
    /// Write the INDEX section.
    pub index: bool,
    /// Threads of the writer (the output does not depend on it).
    pub threads: usize,
    /// Report each phase on stderr.
    pub progress: bool,
}

#[derive(Debug)]
pub enum SliceError {
    /// The input failed a check (rejected or declined).
    File(Failure),
    /// Roots that name no declaration.
    NotFound(Vec<String>),
    /// No root given, or no declaration matched the prefixes.
    Empty,
    /// The packer refused what the slice holds, or could not write it.
    Pack(PackError),
}

impl fmt::Display for SliceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SliceError::File(e) => write!(f, "{e}"),
            SliceError::NotFound(xs) => write!(f, "no declaration named {}", xs.join(", ")),
            SliceError::Empty => write!(f, "no declaration to keep"),
            SliceError::Pack(e) => write!(f, "{e}"),
        }
    }
}

impl std::error::Error for SliceError {}

impl From<Failure> for SliceError {
    fn from(e: Failure) -> Self {
        SliceError::File(e)
    }
}
impl From<PackError> for SliceError {
    fn from(e: PackError) -> Self {
        SliceError::Pack(e)
    }
}

/// What a slice kept, out of what the input holds.
#[derive(Debug, Clone, Default)]
pub struct SliceStats {
    pub roots: u64,
    pub decls: (u64, u64),
    pub main_exprs: (u64, u64),
    pub block_exprs: u64,
    pub names: (u64, u64),
    pub levels: (u64, u64),
    /// What the writer wrote.
    pub written: Stats,
}

impl fmt::Display for SliceStats {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "kept {} roots: declarations {} of {}, MAIN expressions {} of {} (+ {} from proof blocks), names {} of {}, levels {} of {}\n{}",
            self.roots,
            self.decls.0,
            self.decls.1,
            self.main_exprs.0,
            self.main_exprs.1,
            self.block_exprs,
            self.names.0,
            self.names.1,
            self.levels.0,
            self.levels.1,
            self.written
        )
    }
}

// ---------------------------------------------------------------------------
// Bit sets and ranks

struct Bits(Vec<u64>);

impl Bits {
    fn new(n: usize) -> Bits {
        Bits(vec![0; n.div_ceil(64)])
    }
    #[inline(always)]
    fn get(&self, i: u32) -> bool {
        self.0[(i >> 6) as usize] >> (i & 63) & 1 != 0
    }
    /// Sets bit i; true when it was not set before.
    #[inline(always)]
    fn set(&mut self, i: u32) -> bool {
        let w = &mut self.0[(i >> 6) as usize];
        let m = 1u64 << (i & 63);
        let new = *w & m == 0;
        *w |= m;
        new
    }
    fn clear(&mut self, i: u32) {
        self.0[(i >> 6) as usize] &= !(1u64 << (i & 63));
    }
    fn count(&self) -> u64 {
        self.0.iter().map(|w| w.count_ones() as u64).sum()
    }
}

// The rank of i: how many set bits are below it.
struct Rank {
    bits: Bits,
    cum: Vec<u32>,
}

impl Rank {
    fn new(bits: Bits) -> Rank {
        let mut cum = Vec::with_capacity(bits.0.len());
        let mut n = 0u32;
        for w in &bits.0 {
            cum.push(n);
            n += w.count_ones();
        }
        Rank { bits, cum }
    }
    #[inline(always)]
    fn rank(&self, i: u32) -> u32 {
        let w = (i >> 6) as usize;
        self.cum[w] + (self.bits.0[w] & ((1u64 << (i & 63)) - 1)).count_ones()
    }
    #[inline(always)]
    fn get(&self, i: u32) -> bool {
        self.bits.get(i)
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
fn decl_dep_names(d: &Decl, f: &mut impl FnMut(u32)) {
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

fn heads<'d, 'a>(d: &'d Decl<'a>, f: &mut impl FnMut(&'d Head<'a>)) {
    match d {
        Decl::Axiom { head, .. }
        | Decl::Quot { head, .. }
        | Decl::ThmBlock { head, .. }
        | Decl::Defn { head, .. }
        | Decl::Thm { head, .. }
        | Decl::Opaque { head, .. } => f(head),
        Decl::Inductive(ind) => {
            ind.types.iter().for_each(|t| f(&t.head));
            ind.ctors.iter().for_each(|c| f(&c.head));
            ind.recs.iter().for_each(|r| f(&r.head));
        }
    }
}

// Every name a declaration record holds.
fn decl_names(d: &Decl, f: &mut impl FnMut(u32)) {
    heads(d, &mut |h| {
        f(h.name);
        h.params.iter().for_each(&mut *f);
    });
    decl_dep_names(d, f);
}

// The names and levels an expression holds.
fn expr_marks(e: &Expr, names: &mut Bits, levels: &mut Bits) {
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
        if let Decl::Quot { .. } = d {
            self.quots.push(index);
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

// The declarations the options name, as a bit set over declarations.
fn find_roots(
    bytes: &[u8],
    st: &State,
    opts: &SliceOptions,
    decls: &mut Bits,
) -> Result<u64, SliceError> {
    let mut found = vec![false; opts.roots.len()];
    let mut n = 0u64;
    let mut keep = |d: u32, decls: &mut Bits| {
        if decls.set(d) {
            n += 1;
        }
    };
    // a root whose components are all strings: looked up directly
    for (i, r) in opts.roots.iter().enumerate() {
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
    if !opts.prefixes.is_empty() || found.iter().any(|f| !f) {
        let want: std::collections::HashMap<&str, usize> = opts
            .roots
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
            if opts.prefixes.iter().any(|p| s.starts_with(p.as_str())) {
                keep(d, decls);
            }
        }
    }
    let missing: Vec<String> = opts
        .roots
        .iter()
        .zip(&found)
        .filter(|(_, f)| !**f)
        .map(|(r, _)| r.clone())
        .collect();
    if !missing.is_empty() {
        return Err(SliceError::NotFound(missing));
    }
    if n == 0 {
        return Err(SliceError::Empty);
    }
    Ok(n)
}

// ---------------------------------------------------------------------------
// Pass 3: names and levels

struct Mark<'c> {
    exprs: &'c Bits,
    decls: &'c Bits,
    names: &'c mut Bits,
    levels: &'c mut Bits,
    name_pre: Vec<u32>,
    // level id to (kind, a, b): kind 0 succ, 1 max, 2 imax, 3 param (a name)
    lk: Vec<u8>,
    la: Vec<u32>,
    lb: Vec<u32>,
}

impl<'a> Visit<'a> for Mark<'_> {
    type Error = Infallible;
    fn name(&mut self, _: u32, prefix: u32, _: Component<'a>) -> Result<(), Infallible> {
        self.name_pre.push(prefix);
        Ok(())
    }
    fn level(&mut self, _: u32, l: Level) -> Result<(), Infallible> {
        let (k, a, b) = match l {
            Level::Succ(a) => (0, a, 0),
            Level::Max(a, b) => (1, a, b),
            Level::IMax(a, b) => (2, a, b),
            Level::Param(n) => (3, n, 0),
        };
        self.lk.push(k);
        self.la.push(a);
        self.lb.push(b);
        Ok(())
    }
    #[inline]
    fn expr(&mut self, id: u32, e: &Expr<'a>) -> Result<(), Infallible> {
        if self.exprs.get(id) {
            expr_marks(e, self.names, self.levels);
        }
        Ok(())
    }
    fn open_block(&mut self, _: &BlockRef) -> bool {
        false
    }
    fn decl(&mut self, index: u32, _: u64, d: &Decl<'a>) -> Result<(), Infallible> {
        if self.decls.get(index) {
            decl_names(d, &mut |n| {
                self.names.set(n);
            });
        }
        Ok(())
    }
}

impl Mark<'_> {
    // Records only refer back: one sweep down marks every part.
    fn close(&mut self) {
        for l in (1..self.lk.len()).rev() {
            if !self.levels.get(l as u32) {
                continue;
            }
            match self.lk[l] {
                0 => {
                    self.levels.set(self.la[l]);
                }
                1 | 2 => {
                    self.levels.set(self.la[l]);
                    self.levels.set(self.lb[l]);
                }
                _ => {
                    self.names.set(self.la[l]);
                }
            }
        }
        for n in (1..self.name_pre.len()).rev() {
            if self.names.get(n as u32) {
                self.names.set(self.name_pre[n]);
            }
        }
        // the anonymous name and level zero are implicit
        self.names.clear(0);
        self.levels.clear(0);
    }
}

// ---------------------------------------------------------------------------
// Pass 4: the output

struct Emit<'c> {
    pk: &'c mut Pk,
    names: Rank,
    levels: Rank,
    exprs: Rank,
    decls: &'c Bits,
    // the next expression id of the output
    next: u64,
    // MAIN expressions written so far
    main_done: u32,
    // (MAIN expressions written before a block, block expressions written
    // up to and with it): a MAIN expression's output id is its rank plus
    // the block expressions written before it
    shifts: Vec<(u32, u64)>,
    in_blocks: u64,
    // the output id of the open block's first expression
    bstart: u64,
}

fn kv(k: &str, v: J) -> (Vec<u8>, J) {
    (k.as_bytes().to_vec(), v)
}

impl Emit<'_> {
    #[inline(always)]
    fn nid(&self, n: u32) -> u64 {
        if n == 0 {
            0
        } else {
            1 + self.names.rank(n) as u64
        }
    }
    #[inline(always)]
    fn lid(&self, l: u32) -> u64 {
        if l == 0 {
            0
        } else {
            1 + self.levels.rank(l) as u64
        }
    }
    #[inline(always)]
    fn main(&self, i: u32) -> u64 {
        let r = self.exprs.rank(i);
        let j = self.shifts.partition_point(|x| x.0 <= r);
        r as u64 + if j == 0 { 0 } else { self.shifts[j - 1].1 }
    }
    #[inline(always)]
    fn eref(&self, x: &Ref) -> u64 {
        match x {
            Ref::Main(i) => self.main(*i),
            Ref::Block(k) => self.bstart + *k as u64,
        }
    }
    fn levels_of(&self, us: &Ids) -> Vec<u64> {
        us.iter().map(|u| self.lid(u)).collect()
    }
    fn names_of(&self, xs: &Ids) -> Vec<u64> {
        xs.iter().map(|n| self.nid(n)).collect()
    }
    fn jnames(&self, xs: &Ids) -> J {
        J::Arr(xs.iter().map(|n| J::Int(self.nid(n))).collect())
    }

    fn feed(&mut self, e: &Expr) -> Result<(), PackError> {
        let ie = self.next;
        match e {
            Expr::BVar(k) => self.pk.bvar(ie, *k)?,
            Expr::Sort(l) => self.pk.sort(ie, self.lid(*l))?,
            Expr::Const(n, us) => {
                let us = self.levels_of(us);
                self.pk.cnst(ie, self.nid(*n), &us)?
            }
            Expr::App(f, a) => self.pk.app(ie, self.eref(f), self.eref(a))?,
            Expr::Lam(bi, n, t, b) | Expr::Pi(bi, n, t, b) => {
                let lam = matches!(e, Expr::Lam(..));
                let (n, t, b) = (self.nid(*n), self.eref(t), self.eref(b));
                self.pk.bind(ie, lam, *bi as u32, n, t, b)?
            }
            Expr::Let(n, t, v, b) => {
                let (n, t, v, b) = (self.nid(*n), self.eref(t), self.eref(v), self.eref(b));
                self.pk.let_e(ie, n, t, v, b)?
            }
            Expr::Nat(b) => self.pk.nat_le(ie, b)?,
            Expr::Str(s) => self.pk.strv(ie, s.as_bytes())?,
            Expr::Proj(n, i, x) => {
                let (n, x) = (self.nid(*n), self.eref(x));
                self.pk.proj(ie, n, *i, x)?
            }
        }
        self.next += 1;
        Ok(())
    }

    fn head(&self, h: &Head) -> Vec<(Vec<u8>, J)> {
        vec![
            kv("levelParams", self.jnames(&h.params)),
            kv("name", J::Int(self.nid(h.name))),
            kv("type", J::Int(self.main(h.ty))),
        ]
    }

    fn decl(&mut self, d: &Decl) -> Result<(), PackError> {
        match d {
            Decl::Axiom { head, is_unsafe } => {
                let mut o = self.head(head);
                o.push(kv("isUnsafe", J::Bool(*is_unsafe)));
                self.pk.decl_obj(b"axiom", &o)
            }
            Decl::Defn {
                head,
                value,
                hints,
                safety,
                all,
            } => {
                let (hk, h) = match hints {
                    Hints::Opaque => (0u8, 0u64),
                    Hints::Abbrev => (1, 0),
                    Hints::Regular(h) => (2, *h),
                };
                let (n, ps, ty, v, all) = (
                    self.nid(head.name),
                    self.names_of(&head.params),
                    self.main(head.ty),
                    self.main(*value),
                    self.names_of(all),
                );
                self.pk.defn(n, &ps, ty, v, hk, h, *safety, &all)
            }
            Decl::Thm { head, value, all } => {
                let v = self.main(*value);
                self.thm(head, v, all)
            }
            Decl::ThmBlock { head, block, all } => {
                let v = self.bstart + block.exprs - 1;
                self.thm(head, v, all)?;
                self.in_blocks += block.exprs;
                self.shifts.push((self.main_done, self.in_blocks));
                Ok(())
            }
            Decl::Opaque {
                head,
                value,
                is_unsafe,
                all,
            } => {
                let mut o = self.head(head);
                o.push(kv("value", J::Int(self.main(*value))));
                o.push(kv("isUnsafe", J::Bool(*is_unsafe)));
                o.push(kv("all", self.jnames(all)));
                self.pk.decl_obj(b"opaque", &o)
            }
            Decl::Quot { head, kind } => {
                let mut o = self.head(head);
                let k = ["type", "ctor", "lift", "ind"][*kind as usize];
                o.push(kv("kind", J::Str(k.as_bytes().to_vec())));
                self.pk.decl_obj(b"quot", &o)
            }
            Decl::Inductive(ind) => {
                let types = ind
                    .types
                    .iter()
                    .map(|t| {
                        let mut o = self.head(&t.head);
                        o.extend([
                            kv("isUnsafe", J::Bool(t.is_unsafe)),
                            kv("numParams", J::Int(t.num_params)),
                            kv("numIndices", J::Int(t.num_indices)),
                            kv("all", self.jnames(&t.all)),
                            kv("ctors", self.jnames(&t.ctors)),
                            kv("numNested", J::Int(t.num_nested)),
                            kv("isRec", J::Bool(t.is_rec)),
                            kv("isReflexive", J::Bool(t.is_reflexive)),
                        ]);
                        J::Obj(o)
                    })
                    .collect();
                let ctors = ind
                    .ctors
                    .iter()
                    .map(|c| {
                        let mut o = self.head(&c.head);
                        o.extend([
                            kv("isUnsafe", J::Bool(c.is_unsafe)),
                            kv("induct", J::Int(self.nid(c.induct))),
                            kv("cidx", J::Int(c.cidx)),
                            kv("numParams", J::Int(c.num_params)),
                            kv("numFields", J::Int(c.num_fields)),
                        ]);
                        J::Obj(o)
                    })
                    .collect();
                let recs = ind
                    .recs
                    .iter()
                    .map(|r| {
                        let mut o = self.head(&r.head);
                        let rules = r
                            .rules
                            .iter()
                            .map(|x| {
                                J::Obj(vec![
                                    kv("ctor", J::Int(self.nid(x.ctor))),
                                    kv("nfields", J::Int(x.nfields)),
                                    kv("rhs", J::Int(self.main(x.rhs))),
                                ])
                            })
                            .collect();
                        o.extend([
                            kv("isUnsafe", J::Bool(r.is_unsafe)),
                            kv("all", self.jnames(&r.all)),
                            kv("numParams", J::Int(r.num_params)),
                            kv("numIndices", J::Int(r.num_indices)),
                            kv("numMotives", J::Int(r.num_motives)),
                            kv("numMinors", J::Int(r.num_minors)),
                            kv("rules", J::Arr(rules)),
                            kv("k", J::Bool(r.k)),
                        ]);
                        J::Obj(o)
                    })
                    .collect();
                let o = vec![
                    kv("types", J::Arr(types)),
                    kv("ctors", J::Arr(ctors)),
                    kv("recs", J::Arr(recs)),
                ];
                self.pk.decl_obj(b"inductive", &o)
            }
        }
    }

    fn thm(&mut self, head: &Head, v: u64, all: &Ids) -> Result<(), PackError> {
        let (n, ps, ty, all) = (
            self.nid(head.name),
            self.names_of(&head.params),
            self.main(head.ty),
            self.names_of(all),
        );
        self.pk.thm(n, &ps, ty, v, &all)
    }
}

impl<'a> Visit<'a> for Emit<'_> {
    type Error = PackError;
    fn name(&mut self, id: u32, prefix: u32, part: Component<'a>) -> Result<(), PackError> {
        if self.names.get(id) {
            let (i, p) = (self.nid(id), self.nid(prefix));
            match part {
                Component::Str(s) => self.pk.name_str(i, p, s.as_bytes())?,
                Component::Num(k) => self.pk.name_num(i, p, k)?,
            }
        }
        Ok(())
    }
    fn level(&mut self, id: u32, l: Level) -> Result<(), PackError> {
        if self.levels.get(id) {
            let i = self.lid(id);
            match l {
                Level::Succ(a) => self.pk.succ(i, self.lid(a))?,
                Level::Max(a, b) => self.pk.pair(i, self.lid(a), self.lid(b), true)?,
                Level::IMax(a, b) => self.pk.pair(i, self.lid(a), self.lid(b), false)?,
                Level::Param(n) => self.pk.param(i, self.nid(n))?,
            }
        }
        Ok(())
    }
    #[inline]
    fn expr(&mut self, id: u32, e: &Expr<'a>) -> Result<(), PackError> {
        if self.exprs.get(id) {
            debug_assert_eq!(self.main(id), self.next);
            self.feed(e)?;
            self.main_done += 1;
        }
        Ok(())
    }
    fn open_block(&mut self, b: &BlockRef) -> bool {
        self.bstart = self.next;
        self.decls.get(b.decl)
    }
    fn block_expr(&mut self, _: u32, e: &Expr<'_>) -> Result<(), PackError> {
        self.feed(e)
    }
    fn decl(&mut self, index: u32, _: u64, d: &Decl<'a>) -> Result<(), PackError> {
        if self.decls.get(index) {
            self.decl(d)?;
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------

fn file_err<E>(s: Stop<E>, f: impl FnOnce(E) -> SliceError) -> SliceError {
    match s {
        Stop::File(e) => SliceError::File(e),
        Stop::Visitor(e) => f(e),
    }
}

struct Clock {
    on: bool,
    t: std::time::Instant,
}

impl Clock {
    fn lap(&mut self, what: impl fmt::Display) {
        if self.on {
            eprintln!("slice: {what} ({:.1} s)", self.t.elapsed().as_secs_f64());
            self.t = std::time::Instant::now();
        }
    }
}

// The packer's state holding the slice.
fn slice_pk(bytes: &[u8], opts: &SliceOptions) -> Result<(Pk, SliceStats), SliceError> {
    let mut clock = Clock {
        on: opts.progress,
        t: std::time::Instant::now(),
    };
    let f = File::open(bytes)?;
    let main_len = f.section(crate::format::SEC_MAIN).map_or(0, |s| s.length);
    let hint = |c: u32, per: u64| (c as u64).min(main_len / per) as usize;
    let mut stats = SliceStats::default();

    // 1. the tables
    let mut scan = Scan::new(hint(f.counts[2], 2), hint(f.counts[3], 8));
    let st = decode(&f, &mut scan)
        .map_err(|s| file_err(s, |x| match x {}))?
        .state;
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
    stats.roots = find_roots(bytes, &st, opts, &mut cl.decls)?;
    for (w, &x) in cl.decls.0.iter().enumerate() {
        let mut x = x;
        while x != 0 {
            cl.dstack.push((w * 64) as u32 + x.trailing_zeros());
            x &= x - 1;
        }
    }
    cl.dstack.reverse();
    cl.run()?;
    let Closure {
        decls,
        exprs,
        mut names,
        mut levels,
        block_exprs,
        ..
    } = cl;
    drop(scan);
    drop(st);
    stats.decls = (decls.count(), n_decls as u64);
    stats.main_exprs = (exprs.count(), n_exprs as u64);
    stats.block_exprs = block_exprs;
    clock.lap(format_args!(
        "closure: {} declarations, {} MAIN expressions, {} in proof blocks",
        stats.decls.0, stats.main_exprs.0, block_exprs
    ));

    // 3. names and levels
    let mut mark = Mark {
        exprs: &exprs,
        decls: &decls,
        names: &mut names,
        levels: &mut levels,
        name_pre: vec![0],
        lk: vec![0],
        la: vec![0],
        lb: vec![0],
    };
    decode(&f, &mut mark).map_err(|s| file_err(s, |x| match x {}))?;
    mark.close();
    drop(mark);
    stats.names = (names.count(), n_names as u64 - 1);
    stats.levels = (levels.count(), n_levels as u64 - 1);
    clock.lap(format_args!(
        "names {}, levels {}",
        stats.names.0, stats.levels.0
    ));

    // 4. the output
    let total = stats.main_exprs.0 + block_exprs;
    let mut pk = Pk::new((total as usize + stats.names.0 as usize + 64) * 32);
    pk.reserve_all((total as usize + 1) * 16);
    pk.meta = f.source().unwrap_or(b"{}").to_vec();
    let mut emit = Emit {
        pk: &mut pk,
        names: Rank::new(names),
        levels: Rank::new(levels),
        exprs: Rank::new(exprs),
        decls: &decls,
        next: 0,
        main_done: 0,
        shifts: Vec::new(),
        in_blocks: 0,
        bstart: 0,
    };
    decode(&f, &mut emit).map_err(|s| file_err(s, SliceError::Pack))?;
    if emit.next != total {
        return Err(PackError::cannot("internal: the slice's expression count disagrees").into());
    }
    pk.finish();
    clock.lap("records handed to the writer");
    Ok((pk, stats))
}

fn pack_opts(opts: &SliceOptions) -> Options {
    Options {
        index: opts.index,
        threads: opts.threads.max(1),
    }
}

/// Slices the Susz file `bytes` into `output` (written under a temporary
/// name, renamed when complete).
pub fn slice_file(
    bytes: &[u8],
    output: &str,
    opts: &SliceOptions,
) -> Result<SliceStats, SliceError> {
    let (pk, mut stats) = slice_pk(bytes, opts)?;
    stats.written = pack::write_file(pk, output, &pack_opts(opts))?;
    Ok(stats)
}

/// Slices the Susz file `bytes` into bytes in memory.
pub fn slice_to_vec(
    bytes: &[u8],
    opts: &SliceOptions,
) -> Result<(Vec<u8>, SliceStats), SliceError> {
    let (pk, mut stats) = slice_pk(bytes, opts)?;
    let (out, st) = pack::write_vec(pk, &pack_opts(opts))?;
    stats.written = st;
    Ok((out, stats))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ranks() {
        for n in [1usize, 63, 64, 65, 200, 1000] {
            let mut b = Bits::new(n);
            let set: Vec<u32> = (0..n as u32).filter(|i| i % 3 == 0 || i % 7 == 1).collect();
            for &i in &set {
                assert!(b.set(i));
                assert!(!b.set(i));
            }
            assert_eq!(b.count(), set.len() as u64);
            let r = Rank::new(b);
            for i in 0..n as u32 {
                assert_eq!(r.rank(i) as usize, set.iter().filter(|&&x| x < i).count());
                assert_eq!(r.get(i), set.contains(&i));
            }
        }
    }
}
