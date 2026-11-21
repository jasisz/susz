//! The digest of the declarations a file holds (spec 9.3): every
//! declaration in order, with names, levels and expressions hashed by
//! structure with SHA-256, so the export's ids, the Susz layout, proof
//! blocks, `mdata` and `letE.nondep` do not count. Computed from a Susz file
//! ([`susz`], read directly with the reader) and from an ndjson export
//! ([`ndjson`], read with a parser of its own, which shares no code with the
//! packer's), so that comparing the two shows whether a Susz file holds the
//! declarations of an export, and which declaration differs if not.
//!
//! Memory: one 16-byte hash for each name, level and expression id, in
//! tables grown a page at a time (no copies on growth). With names asked
//! for, the ndjson side also keeps each name's prefix and component.

use crate::read::{self, Block, Component, Event, Expr, Failure, File, Ref};
use sha2::{Digest, Sha256};
use std::borrow::Cow;
use std::fmt;
use std::io::{self, BufRead};

/// A node's hash: the first 16 bytes of SHA-256 of its encoding.
pub type Node = [u8; 16];
/// A declaration's digest, and the file's: a whole SHA-256.
pub type Hash = [u8; 32];

/// The encodings' tag bytes (spec 9.3).
pub mod tag {
    pub const NAME_ANON: u8 = 0x01;
    pub const NAME_STR: u8 = 0x02;
    pub const NAME_NUM: u8 = 0x03;
    pub const LEVEL_ZERO: u8 = 0x10;
    pub const LEVEL_SUCC: u8 = 0x11;
    pub const LEVEL_MAX: u8 = 0x12;
    pub const LEVEL_IMAX: u8 = 0x13;
    pub const LEVEL_PARAM: u8 = 0x14;
    pub const BVAR: u8 = 0x20;
    pub const SORT: u8 = 0x21;
    pub const CONST: u8 = 0x22;
    pub const APP: u8 = 0x23;
    pub const LAM: u8 = 0x24;
    pub const FORALL: u8 = 0x25;
    pub const LET: u8 = 0x26;
    pub const NAT: u8 = 0x27;
    pub const STR: u8 = 0x28;
    pub const PROJ: u8 = 0x29;
    pub const AXIOM: u8 = 0x40;
    pub const DEF: u8 = 0x41;
    pub const THM: u8 = 0x42;
    pub const OPAQUE: u8 = 0x43;
    pub const QUOT: u8 = 0x44;
    pub const INDUCTIVE: u8 = 0x45;
}

/// The declaration kinds, as lean4export names them (a theorem whose proof
/// sits in a block is a `thm`).
pub const KINDS: [&str; 6] = ["axiom", "def", "thm", "opaque", "quot", "inductive"];

/// How the anonymous name is displayed (as the reader displays it).
const ANONYMOUS: &str = "[anonymous]";

fn sha(b: &[u8]) -> Hash {
    Sha256::digest(b).into()
}

fn node(b: &[u8]) -> Node {
    let h = sha(b);
    let mut n = [0u8; 16];
    n.copy_from_slice(&h[..16]);
    n
}

/// Lowercase hex.
pub fn hex(b: &[u8]) -> String {
    const D: &[u8; 16] = b"0123456789abcdef";
    let mut s = String::with_capacity(2 * b.len());
    for &x in b {
        s.push(D[(x >> 4) as usize] as char);
        s.push(D[(x & 15) as usize] as char);
    }
    s
}

// ---------------------------------------------------------------------------
// The canonical encoding (spec 9.3), shared by both sides: each side turns
// its records into these calls, so the bytes hashed are built in one place.

/// Builds encodings in a reused buffer and hashes them.
pub struct Enc {
    b: Vec<u8>,
}

impl Default for Enc {
    fn default() -> Self {
        Self::new()
    }
}

#[inline]
fn put_u64(b: &mut Vec<u8>, x: u64) {
    b.extend_from_slice(&x.to_le_bytes());
}
#[inline]
fn put_bytes(b: &mut Vec<u8>, s: &[u8]) {
    put_u64(b, s.len() as u64);
    b.extend_from_slice(s);
}
#[inline]
fn put_nodes(b: &mut Vec<u8>, xs: &[Node]) {
    put_u64(b, xs.len() as u64);
    for x in xs {
        b.extend_from_slice(x);
    }
}

impl Enc {
    pub fn new() -> Enc {
        Enc {
            b: Vec::with_capacity(256),
        }
    }
    #[inline]
    fn start(&mut self, t: u8) -> &mut Vec<u8> {
        self.b.clear();
        self.b.push(t);
        &mut self.b
    }
    #[inline]
    fn done(&self) -> Node {
        node(&self.b)
    }
    pub fn anon(&mut self) -> Node {
        self.start(tag::NAME_ANON);
        self.done()
    }
    pub fn name_str(&mut self, prefix: &Node, s: &[u8]) -> Node {
        let b = self.start(tag::NAME_STR);
        b.extend_from_slice(prefix);
        put_bytes(b, s);
        self.done()
    }
    pub fn name_num(&mut self, prefix: &Node, k: u64) -> Node {
        let b = self.start(tag::NAME_NUM);
        b.extend_from_slice(prefix);
        put_u64(b, k);
        self.done()
    }
    pub fn zero(&mut self) -> Node {
        self.start(tag::LEVEL_ZERO);
        self.done()
    }
    pub fn succ(&mut self, l: &Node) -> Node {
        self.start(tag::LEVEL_SUCC).extend_from_slice(l);
        self.done()
    }
    /// `max`, or `imax` when `imax` is true.
    pub fn max(&mut self, imax: bool, a: &Node, c: &Node) -> Node {
        let b = self.start(if imax {
            tag::LEVEL_IMAX
        } else {
            tag::LEVEL_MAX
        });
        b.extend_from_slice(a);
        b.extend_from_slice(c);
        self.done()
    }
    pub fn param(&mut self, n: &Node) -> Node {
        self.start(tag::LEVEL_PARAM).extend_from_slice(n);
        self.done()
    }
    pub fn bvar(&mut self, i: u64) -> Node {
        put_u64(self.start(tag::BVAR), i);
        self.done()
    }
    pub fn sort(&mut self, l: &Node) -> Node {
        self.start(tag::SORT).extend_from_slice(l);
        self.done()
    }
    /// `const`: [`Enc::const_start`] with the name and the number of
    /// levels, each level with [`Enc::push`], then [`Enc::const_end`].
    pub fn const_start(&mut self, n: &Node, count: u64) {
        let b = self.start(tag::CONST);
        b.extend_from_slice(n);
        put_u64(b, count);
    }
    #[inline]
    pub fn push(&mut self, x: &Node) {
        self.b.extend_from_slice(x);
    }
    pub fn const_end(&mut self) -> Node {
        self.done()
    }
    pub fn app(&mut self, f: &Node, a: &Node) -> Node {
        let b = self.start(tag::APP);
        b.extend_from_slice(f);
        b.extend_from_slice(a);
        self.done()
    }
    /// `lam`, or `forallE` when `pi` is true. Binder: 0 default,
    /// 1 implicit, 2 strict implicit, 3 instance implicit.
    pub fn binder(&mut self, pi: bool, bi: u8, n: &Node, t: &Node, body: &Node) -> Node {
        let b = self.start(if pi { tag::FORALL } else { tag::LAM });
        b.push(bi);
        b.extend_from_slice(n);
        b.extend_from_slice(t);
        b.extend_from_slice(body);
        self.done()
    }
    pub fn let_e(&mut self, n: &Node, t: &Node, v: &Node, body: &Node) -> Node {
        let b = self.start(tag::LET);
        b.extend_from_slice(n);
        b.extend_from_slice(t);
        b.extend_from_slice(v);
        b.extend_from_slice(body);
        self.done()
    }
    /// A Nat literal, in canonical decimal: ASCII digits, no leading zero,
    /// `0` for zero.
    pub fn nat(&mut self, decimal: &[u8]) -> Node {
        debug_assert!(
            !decimal.is_empty() && (decimal == b"0" || decimal[0] != b'0'),
            "not canonical decimal"
        );
        put_bytes(self.start(tag::NAT), decimal);
        self.done()
    }
    pub fn str_lit(&mut self, s: &[u8]) -> Node {
        put_bytes(self.start(tag::STR), s);
        self.done()
    }
    pub fn proj(&mut self, n: &Node, idx: u64, x: &Node) -> Node {
        let b = self.start(tag::PROJ);
        b.extend_from_slice(n);
        put_u64(b, idx);
        b.extend_from_slice(x);
        self.done()
    }
}

/// A declaration's head.
#[derive(Clone, Default)]
pub struct Head {
    pub name: Node,
    pub params: Vec<Node>,
    pub ty: Node,
}

pub struct IndType {
    pub head: Head,
    pub is_unsafe: bool,
    pub num_params: u64,
    pub num_indices: u64,
    pub all: Vec<Node>,
    pub ctors: Vec<Node>,
    pub num_nested: u64,
    pub is_rec: bool,
    pub is_reflexive: bool,
}

pub struct Ctor {
    pub head: Head,
    pub is_unsafe: bool,
    pub induct: Node,
    pub cidx: u64,
    pub num_params: u64,
    pub num_fields: u64,
}

pub struct RecRule {
    pub ctor: Node,
    pub nfields: u64,
    pub rhs: Node,
}

pub struct Rec {
    pub head: Head,
    pub is_unsafe: bool,
    pub all: Vec<Node>,
    pub num_params: u64,
    pub num_indices: u64,
    pub num_motives: u64,
    pub num_minors: u64,
    pub rules: Vec<RecRule>,
    pub k: bool,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Hints {
    Opaque,
    Abbrev,
    Regular(u64),
}

/// A declaration, every reference already a hash.
pub enum DeclV {
    Axiom {
        head: Head,
        is_unsafe: bool,
    },
    /// `safety`: 0 safe, 1 unsafe, 2 partial.
    Def {
        head: Head,
        value: Node,
        hints: Hints,
        safety: u8,
        all: Vec<Node>,
    },
    Thm {
        head: Head,
        value: Node,
        all: Vec<Node>,
    },
    Opaque {
        head: Head,
        value: Node,
        is_unsafe: bool,
        all: Vec<Node>,
    },
    /// `kind`: 0 type, 1 ctor, 2 lift, 3 ind.
    Quot {
        head: Head,
        kind: u8,
    },
    Inductive {
        types: Vec<IndType>,
        ctors: Vec<Ctor>,
        recs: Vec<Rec>,
    },
}

impl DeclV {
    /// The kind, an index into [`KINDS`].
    pub fn kind(&self) -> u8 {
        match self {
            DeclV::Axiom { .. } => 0,
            DeclV::Def { .. } => 1,
            DeclV::Thm { .. } => 2,
            DeclV::Opaque { .. } => 3,
            DeclV::Quot { .. } => 4,
            DeclV::Inductive { .. } => 5,
        }
    }
}

fn put_head(b: &mut Vec<u8>, h: &Head) {
    b.extend_from_slice(&h.name);
    put_nodes(b, &h.params);
    b.extend_from_slice(&h.ty);
}

fn put_type(b: &mut Vec<u8>, t: &IndType) {
    put_head(b, &t.head);
    b.push(t.is_unsafe as u8);
    put_u64(b, t.num_params);
    put_u64(b, t.num_indices);
    put_nodes(b, &t.all);
    put_nodes(b, &t.ctors);
    put_u64(b, t.num_nested);
    b.push(t.is_rec as u8);
    b.push(t.is_reflexive as u8);
}

fn put_ctor(b: &mut Vec<u8>, c: &Ctor) {
    put_head(b, &c.head);
    b.push(c.is_unsafe as u8);
    b.extend_from_slice(&c.induct);
    put_u64(b, c.cidx);
    put_u64(b, c.num_params);
    put_u64(b, c.num_fields);
}

fn put_rec(b: &mut Vec<u8>, r: &Rec) {
    put_head(b, &r.head);
    b.push(r.is_unsafe as u8);
    put_nodes(b, &r.all);
    put_u64(b, r.num_params);
    put_u64(b, r.num_indices);
    put_u64(b, r.num_motives);
    put_u64(b, r.num_minors);
    put_u64(b, r.rules.len() as u64);
    for x in &r.rules {
        b.extend_from_slice(&x.ctor);
        put_u64(b, x.nfields);
        b.extend_from_slice(&x.rhs);
    }
    b.push(r.k as u8);
}

impl Enc {
    /// A declaration's digest: SHA-256 of its encoding, all 32 bytes.
    pub fn decl(&mut self, d: &DeclV) -> Hash {
        match d {
            DeclV::Axiom { head, is_unsafe } => {
                let b = self.start(tag::AXIOM);
                put_head(b, head);
                b.push(*is_unsafe as u8);
            }
            DeclV::Def {
                head,
                value,
                hints,
                safety,
                all,
            } => {
                let b = self.start(tag::DEF);
                put_head(b, head);
                b.extend_from_slice(value);
                match hints {
                    Hints::Opaque => b.push(0),
                    Hints::Abbrev => b.push(1),
                    Hints::Regular(h) => {
                        b.push(2);
                        put_u64(b, *h);
                    }
                }
                b.push(*safety);
                put_nodes(b, all);
            }
            DeclV::Thm { head, value, all } => {
                let b = self.start(tag::THM);
                put_head(b, head);
                b.extend_from_slice(value);
                put_nodes(b, all);
            }
            DeclV::Opaque {
                head,
                value,
                is_unsafe,
                all,
            } => {
                let b = self.start(tag::OPAQUE);
                put_head(b, head);
                b.extend_from_slice(value);
                b.push(*is_unsafe as u8);
                put_nodes(b, all);
            }
            DeclV::Quot { head, kind } => {
                let b = self.start(tag::QUOT);
                put_head(b, head);
                b.push(*kind);
            }
            DeclV::Inductive { types, ctors, recs } => {
                let b = self.start(tag::INDUCTIVE);
                put_u64(b, types.len() as u64);
                for t in types {
                    put_type(b, t);
                }
                put_u64(b, ctors.len() as u64);
                for c in ctors {
                    put_ctor(b, c);
                }
                put_u64(b, recs.len() as u64);
                for r in recs {
                    put_rec(b, r);
                }
            }
        }
        sha(&self.b)
    }
}

// ---------------------------------------------------------------------------
// Tables by id, a page at a time

// 16 MiB for a page of 16-byte hashes: big enough that the system
// allocator maps it on its own and gives it back when it is freed (with
// 1 MiB pages, macOS kept the freed ones, and comparing two files took the
// memory of both)
const PAGE_BITS: u32 = 20;
const PAGE: usize = 1 << PAGE_BITS;
/// Ids are below 2^32 (spec 7.1; the ndjson side declines larger ones).
const PAGES: usize = 1 << (32 - PAGE_BITS);

struct Page<T> {
    v: Box<[T]>,
    set: Box<[u64]>,
}

/// A table from ids below 2^32 to values, allocated a page of 2^20 entries
/// at a time, each page exactly once: growing never copies.
struct Paged<T> {
    dir: Vec<Option<Box<Page<T>>>>,
    pages: u64,
    defined: u64,
}

enum SetError {
    Twice,
    TooLarge,
    Sparse,
}

impl<T: Copy + Default> Paged<T> {
    fn new() -> Paged<T> {
        Paged {
            dir: (0..PAGES).map(|_| None).collect(),
            pages: 0,
            defined: 0,
        }
    }
    #[inline]
    fn get(&self, id: u64) -> Option<T> {
        if id >> 32 != 0 {
            return None;
        }
        let p = self.dir[(id >> PAGE_BITS) as usize].as_deref()?;
        let k = id as usize & (PAGE - 1);
        if p.set[k >> 6] >> (k & 63) & 1 == 0 {
            return None;
        }
        Some(p.v[k])
    }
    #[inline]
    fn set(&mut self, id: u64, x: T) -> Result<(), SetError> {
        if id >> 32 != 0 {
            return Err(SetError::TooLarge);
        }
        let slot = (id >> PAGE_BITS) as usize;
        if self.dir[slot].is_none() {
            // ids may come in any order, but the pages hold at most 16
            // entries for each one defined, plus 4 pages
            if (self.pages + 1) * PAGE as u64 > 16 * self.defined + 4 * PAGE as u64 {
                return Err(SetError::Sparse);
            }
            self.dir[slot] = Some(Box::new(Page {
                v: vec![T::default(); PAGE].into_boxed_slice(),
                set: vec![0u64; PAGE / 64].into_boxed_slice(),
            }));
            self.pages += 1;
        }
        let p = self.dir[slot].as_deref_mut().unwrap();
        let k = id as usize & (PAGE - 1);
        let w = &mut p.set[k >> 6];
        if *w >> (k & 63) & 1 != 0 {
            return Err(SetError::Twice);
        }
        *w |= 1 << (k & 63);
        p.v[k] = x;
        self.defined += 1;
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Results

/// One declaration's digest. `name` is the dotted name the declaration
/// declares (an inductive block: its first type's), empty unless names were
/// asked for.
pub struct Entry<'a> {
    /// Its index in the file, from 0.
    pub index: u64,
    pub digest: Hash,
    /// An index into [`KINDS`].
    pub kind: u8,
    pub name: &'a str,
}

/// What a digest run found.
#[derive(Debug, Clone, Default)]
pub struct Summary {
    /// The file digest.
    pub digest: Hash,
    pub decls: u64,
    /// Declarations by kind, as in [`KINDS`].
    pub kinds: [u64; 6],
    /// Name, level and expression records read (not counting the implicit
    /// anonymous name and level zero). Susz: MAIN and proof-block
    /// expressions. ndjson: `mdata` records included.
    pub names: u64,
    pub levels: u64,
    pub exprs: u64,
    /// Susz: expressions in proof blocks. ndjson: `mdata` records.
    pub extra: u64,
}

impl Summary {
    /// `N declarations: a axiom, d def, ...`: the same for both forms of
    /// one export.
    pub fn declarations_line(&self) -> String {
        let mut s = format!("{} declarations:", self.decls);
        for (i, k) in KINDS.iter().enumerate() {
            s.push_str(if i == 0 { " " } else { ", " });
            s.push_str(&format!("{} {k}", self.kinds[i]));
        }
        s
    }
}

#[derive(Debug)]
pub enum Error {
    /// The Susz file is malformed, or the reader declines it.
    Susz(Failure),
    /// The ndjson is not a valid export (a packer refuses it with exit 1).
    Invalid {
        line: u64,
        msg: String,
    },
    /// The ndjson holds something this reader does not know, or goes past
    /// one of its limits (a packer refuses it with exit 2).
    Cannot {
        line: u64,
        msg: String,
    },
    Io(io::Error),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::Susz(e) => write!(f, "{e}"),
            Error::Invalid { line, msg } => write!(f, "not a valid export: line {line}: {msg}"),
            Error::Cannot { line, msg } => write!(f, "cannot digest: line {line}: {msg}"),
            Error::Io(e) => write!(f, "{e}"),
        }
    }
}

impl std::error::Error for Error {}

impl From<Failure> for Error {
    fn from(e: Failure) -> Self {
        Error::Susz(e)
    }
}
impl From<io::Error> for Error {
    fn from(e: io::Error) -> Self {
        Error::Io(e)
    }
}

/// Called with each declaration's digest, in file order. An error stops the
/// run with [`Error::Io`].
pub type Each<'f> = dyn FnMut(Entry<'_>) -> io::Result<()> + 'f;

struct Acc {
    file: Sha256,
    sum: Summary,
}

impl Acc {
    fn new() -> Acc {
        Acc {
            file: Sha256::new(),
            sum: Summary::default(),
        }
    }
    fn decl(&mut self, d: Hash, kind: u8, name: &str, each: &mut Each<'_>) -> io::Result<()> {
        self.file.update(d);
        let index = self.sum.decls;
        self.sum.decls += 1;
        self.sum.kinds[kind as usize] += 1;
        each(Entry {
            index,
            digest: d,
            kind,
            name,
        })
    }
    fn end(mut self) -> Summary {
        self.sum.digest = self.file.finalize().into();
        self.sum
    }
}

/// A name for one line of text: control characters as `\xHH`.
pub fn printable(name: &str) -> Cow<'_, str> {
    if !name.chars().any(char::is_control) {
        return Cow::Borrowed(name);
    }
    let mut s = String::with_capacity(name.len() + 8);
    for c in name.chars() {
        if c.is_control() {
            // every control character is below U+0100
            s.push_str(&format!("\\x{:02x}", c as u32));
        } else {
            s.push(c);
        }
    }
    Cow::Owned(s)
}

// ---------------------------------------------------------------------------
// Susz

/// The digest of a Susz file, read directly (not through unpack), with
/// every structural check of the reader. Rule P is not checked: a file that
/// breaks it still holds its export's declarations (spec 2). With `names`,
/// each entry carries its declaration's dotted name.
pub fn susz(bytes: &[u8], names: bool, each: &mut Each<'_>) -> Result<Summary, Error> {
    let f = File::open(bytes)?;
    let mut m = f.main();
    let mut enc = Enc::new();
    let mut nm: Paged<Node> = Paged::new();
    let mut lv: Paged<Node> = Paged::new();
    let mut ex: Paged<Node> = Paged::new();
    let _ = nm.set(0, enc.anon());
    let _ = lv.set(0, enc.zero());
    let mut local: Vec<Node> = Vec::new();
    let mut acc = Acc::new();
    let mut nname = String::new();
    while let Some(ev) = m.next() {
        match ev? {
            Event::Name { id, prefix, part } => {
                let p = g(&nm, prefix);
                let h = match part {
                    Component::Str(s) => enc.name_str(&p, s.as_bytes()),
                    Component::Num(k) => enc.name_num(&p, k),
                };
                let _ = nm.set(id as u64, h);
                acc.sum.names += 1;
            }
            Event::Level { id, level } => {
                let h = match level {
                    read::Level::Succ(a) => enc.succ(&g(&lv, a)),
                    read::Level::Max(a, b) => enc.max(false, &g(&lv, a), &g(&lv, b)),
                    read::Level::IMax(a, b) => enc.max(true, &g(&lv, a), &g(&lv, b)),
                    read::Level::Param(n) => enc.param(&g(&nm, n)),
                };
                let _ = lv.set(id as u64, h);
                acc.sum.levels += 1;
            }
            Event::Expr { id, expr } => {
                let h = susz_expr(&mut enc, &expr, &nm, &lv, &ex, &[]);
                let _ = ex.set(id as u64, h);
                acc.sum.exprs += 1;
            }
            Event::Frontier { .. } => {}
            Event::Decl { decl, .. } => {
                let value = |v: u32| g(&ex, v);
                let d = match &decl {
                    read::Decl::ThmBlock { head, block, all } => {
                        local.clear();
                        for r in Block::new(bytes, m.state(), *block).without_rule_p() {
                            let (_, e) = r?;
                            let x = susz_expr(&mut enc, &e, &nm, &lv, &ex, &local);
                            local.push(x);
                        }
                        acc.sum.exprs += local.len() as u64;
                        acc.sum.extra += local.len() as u64;
                        DeclV::Thm {
                            head: susz_head(&nm, &ex, head),
                            value: *local.last().expect("a block holds an expression"),
                            all: list(&nm, all),
                        }
                    }
                    d => susz_decl(&nm, &ex, d, value),
                };
                let h = enc.decl(&d);
                nname.clear();
                if names {
                    match first_name(&decl) {
                        Some(n) => nname.push_str(&m.state().name_display(bytes, n)),
                        None => nname.push_str(ANONYMOUS),
                    }
                }
                acc.decl(h, d.kind(), &nname, each)?;
            }
        }
    }
    Ok(acc.end())
}

// The reader checked every id: each lookup succeeds.
#[inline]
fn g(t: &Paged<Node>, id: u32) -> Node {
    t.get(id as u64).expect("an id the reader checked")
}

fn list(t: &Paged<Node>, ids: &read::Ids) -> Vec<Node> {
    ids.iter().map(|x| g(t, x)).collect()
}

fn susz_head(nm: &Paged<Node>, ex: &Paged<Node>, h: &read::Head) -> Head {
    Head {
        name: g(nm, h.name),
        params: list(nm, &h.params),
        ty: g(ex, h.ty),
    }
}

/// The name a declaration record declares first.
fn first_name(d: &read::Decl) -> Option<u32> {
    use read::Decl as D;
    match d {
        D::Axiom { head, .. }
        | D::Defn { head, .. }
        | D::Thm { head, .. }
        | D::Opaque { head, .. }
        | D::Quot { head, .. }
        | D::ThmBlock { head, .. } => Some(head.name),
        D::Inductive(ind) => ind
            .types
            .first()
            .map(|t| t.head.name)
            .or(ind.ctors.first().map(|c| c.head.name))
            .or(ind.recs.first().map(|r| r.head.name)),
    }
}

fn susz_decl(
    nm: &Paged<Node>,
    ex: &Paged<Node>,
    d: &read::Decl,
    value: impl Fn(u32) -> Node,
) -> DeclV {
    use read::Decl as D;
    let head = |h: &read::Head| susz_head(nm, ex, h);
    match d {
        D::Axiom { head: h, is_unsafe } => DeclV::Axiom {
            head: head(h),
            is_unsafe: *is_unsafe,
        },
        D::Defn {
            head: h,
            value: v,
            hints,
            safety,
            all,
        } => DeclV::Def {
            head: head(h),
            value: value(*v),
            hints: match hints {
                read::Hints::Opaque => Hints::Opaque,
                read::Hints::Abbrev => Hints::Abbrev,
                read::Hints::Regular(k) => Hints::Regular(*k),
            },
            safety: *safety,
            all: list(nm, all),
        },
        D::Thm {
            head: h,
            value: v,
            all,
        } => DeclV::Thm {
            head: head(h),
            value: value(*v),
            all: list(nm, all),
        },
        D::Opaque {
            head: h,
            value: v,
            is_unsafe,
            all,
        } => DeclV::Opaque {
            head: head(h),
            value: value(*v),
            is_unsafe: *is_unsafe,
            all: list(nm, all),
        },
        D::Quot { head: h, kind } => DeclV::Quot {
            head: head(h),
            kind: *kind,
        },
        D::Inductive(ind) => DeclV::Inductive {
            types: ind
                .types
                .iter()
                .map(|t| IndType {
                    head: head(&t.head),
                    is_unsafe: t.is_unsafe,
                    num_params: t.num_params,
                    num_indices: t.num_indices,
                    all: list(nm, &t.all),
                    ctors: list(nm, &t.ctors),
                    num_nested: t.num_nested,
                    is_rec: t.is_rec,
                    is_reflexive: t.is_reflexive,
                })
                .collect(),
            ctors: ind
                .ctors
                .iter()
                .map(|c| Ctor {
                    head: head(&c.head),
                    is_unsafe: c.is_unsafe,
                    induct: g(nm, c.induct),
                    cidx: c.cidx,
                    num_params: c.num_params,
                    num_fields: c.num_fields,
                })
                .collect(),
            recs: ind
                .recs
                .iter()
                .map(|r| Rec {
                    head: head(&r.head),
                    is_unsafe: r.is_unsafe,
                    all: list(nm, &r.all),
                    num_params: r.num_params,
                    num_indices: r.num_indices,
                    num_motives: r.num_motives,
                    num_minors: r.num_minors,
                    rules: r
                        .rules
                        .iter()
                        .map(|x| RecRule {
                            ctor: g(nm, x.ctor),
                            nfields: x.nfields,
                            rhs: value(x.rhs),
                        })
                        .collect(),
                    k: r.k,
                })
                .collect(),
        },
        D::ThmBlock { .. } => unreachable!("read with its block"),
    }
}

fn susz_expr(
    enc: &mut Enc,
    e: &Expr,
    nm: &Paged<Node>,
    lv: &Paged<Node>,
    ex: &Paged<Node>,
    local: &[Node],
) -> Node {
    let r = |x: &Ref| match x {
        Ref::Main(i) => g(ex, *i),
        Ref::Block(k) => local[*k as usize],
    };
    match e {
        Expr::BVar(i) => enc.bvar(*i),
        Expr::Sort(l) => enc.sort(&g(lv, *l)),
        Expr::Const(n, us) => {
            enc.const_start(&g(nm, *n), us.len());
            for u in us.iter() {
                enc.push(&g(lv, u));
            }
            enc.const_end()
        }
        Expr::App(f, a) => enc.app(&r(f), &r(a)),
        Expr::Lam(bi, n, t, b) => enc.binder(false, *bi, &g(nm, *n), &r(t), &r(b)),
        Expr::Pi(bi, n, t, b) => enc.binder(true, *bi, &g(nm, *n), &r(t), &r(b)),
        Expr::Let(n, t, v, b) => enc.let_e(&g(nm, *n), &r(t), &r(v), &r(b)),
        // minimal little-endian bytes to canonical decimal
        Expr::Nat(b) => enc.nat(crate::format::nat_to_decimal(b).as_bytes()),
        Expr::Str(s) => enc.str_lit(s.as_bytes()),
        Expr::Proj(n, i, x) => enc.proj(&g(nm, *n), *i, &r(x)),
    }
}

/// The file digest of a Susz file.
pub fn of_susz(bytes: &[u8]) -> Result<Hash, Error> {
    susz(bytes, false, &mut |_| Ok(())).map(|s| s.digest)
}

// ---------------------------------------------------------------------------
// ndjson: a reader of its own, sharing no code with the packer's. It reads
// the dialect of spec 9.2 and is strict: a record kind or key it does not
// know is an error, never skipped.

enum Bad {
    Invalid(String),
    Cannot(String),
    Io(io::Error),
}

type R<T> = Result<T, Bad>;

fn inv(m: impl Into<String>) -> Bad {
    Bad::Invalid(m.into())
}
fn cant(m: impl Into<String>) -> Bad {
    Bad::Cannot(m.into())
}

/// How deep values may nest in what the reader skips (`mdata`'s data, the
/// header's `meta`).
const MAX_DEPTH: u32 = 256;

struct P<'a> {
    s: &'a [u8],
    i: usize,
}

impl<'a> P<'a> {
    #[inline]
    fn ws(&mut self) {
        while let Some(&c) = self.s.get(self.i) {
            if c == b' ' || c == b'\t' || c == b'\r' || c == b'\n' {
                self.i += 1;
            } else {
                break;
            }
        }
    }
    #[inline]
    fn peek(&self) -> Option<u8> {
        self.s.get(self.i).copied()
    }
    #[inline]
    fn eat(&mut self, c: u8) -> R<()> {
        self.ws();
        if self.peek() == Some(c) {
            self.i += 1;
            Ok(())
        } else {
            Err(self.unexpected(&format!("'{}'", c as char)))
        }
    }
    #[cold]
    fn unexpected(&self, want: &str) -> Bad {
        match self.peek() {
            None => inv(format!(
                "expected {want}, the line ends at column {}",
                self.i + 1
            )),
            Some(_) => inv(format!("expected {want} at column {}", self.i + 1)),
        }
    }
    /// A non-negative integer (leading zeros allowed).
    #[inline]
    fn int(&mut self) -> R<u64> {
        self.ws();
        let st = self.i;
        let mut v: u64 = 0;
        let mut big = false;
        while let Some(c) = self.peek() {
            if !c.is_ascii_digit() {
                break;
            }
            match v
                .checked_mul(10)
                .and_then(|x| x.checked_add((c - b'0') as u64))
            {
                Some(x) => v = x,
                None => big = true,
            }
            self.i += 1;
        }
        if self.i == st {
            return Err(self.unexpected("a non-negative integer"));
        }
        if big {
            return Err(cant(format!(
                "an integer of {} digits does not fit 64 bits",
                self.i - st
            )));
        }
        Ok(v)
    }
    fn boolean(&mut self) -> R<bool> {
        self.ws();
        let r = &self.s[self.i..];
        if r.starts_with(b"true") {
            self.i += 4;
            Ok(true)
        } else if r.starts_with(b"false") {
            self.i += 5;
            Ok(false)
        } else {
            Err(self.unexpected("true or false"))
        }
    }
    /// A string's bytes, unescaped and checked to be UTF-8; borrowed from
    /// the line when it has no escape. Raw control characters are allowed
    /// (spec 9.2).
    fn string(&mut self) -> R<Cow<'a, [u8]>> {
        self.eat(b'"')?;
        let s: &'a [u8] = self.s;
        let st = self.i;
        let mut j = st;
        while j < s.len() && s[j] != b'"' && s[j] != b'\\' {
            j += 1;
        }
        if j >= s.len() {
            return Err(inv("a string runs past the end of the line"));
        }
        if s[j] == b'"' {
            self.i = j + 1;
            let r = &s[st..j];
            utf8(r)?;
            return Ok(Cow::Borrowed(r));
        }
        let mut out = s[st..j].to_vec();
        self.i = j;
        loop {
            let Some(c) = self.peek() else {
                return Err(inv("a string runs past the end of the line"));
            };
            self.i += 1;
            match c {
                b'"' => break,
                b'\\' => {
                    let Some(e) = self.peek() else {
                        return Err(inv("a string runs past the end of the line"));
                    };
                    self.i += 1;
                    match e {
                        b'"' => out.push(b'"'),
                        b'\\' => out.push(b'\\'),
                        b'/' => out.push(b'/'),
                        b'b' => out.push(8),
                        b'f' => out.push(12),
                        b'n' => out.push(b'\n'),
                        b'r' => out.push(b'\r'),
                        b't' => out.push(b'\t'),
                        b'u' => {
                            let hi = self.hex4()?;
                            let cp = if (0xD800..0xDC00).contains(&hi) {
                                if !self.s[self.i..].starts_with(b"\\u") {
                                    return Err(inv("a lone surrogate in a \\u escape"));
                                }
                                self.i += 2;
                                let lo = self.hex4()?;
                                if !(0xDC00..0xE000).contains(&lo) {
                                    return Err(inv("a lone surrogate in a \\u escape"));
                                }
                                0x10000 + ((hi - 0xD800) << 10) + (lo - 0xDC00)
                            } else {
                                hi
                            };
                            // a low surrogate alone is not a char
                            let Some(ch) = char::from_u32(cp) else {
                                return Err(inv("a lone surrogate in a \\u escape"));
                            };
                            let mut t = [0u8; 4];
                            out.extend_from_slice(ch.encode_utf8(&mut t).as_bytes());
                        }
                        _ => return Err(inv(format!("a bad escape at column {}", self.i))),
                    }
                }
                c => out.push(c),
            }
        }
        utf8(&out)?;
        Ok(Cow::Owned(out))
    }
    fn hex4(&mut self) -> R<u32> {
        let mut v = 0u32;
        for _ in 0..4 {
            let d = match self.peek() {
                Some(c @ b'0'..=b'9') => c - b'0',
                Some(c @ b'a'..=b'f') => c - b'a' + 10,
                Some(c @ b'A'..=b'F') => c - b'A' + 10,
                _ => return Err(inv("a bad \\u escape")),
            };
            v = v * 16 + d as u32;
            self.i += 1;
        }
        Ok(v)
    }
    /// The members of an object: `f` reads each value after its key. A
    /// trailing comma is allowed (spec 9.2).
    #[inline]
    fn members(&mut self, mut f: impl FnMut(&mut P<'a>, &[u8]) -> R<()>) -> R<()> {
        self.eat(b'{')?;
        self.ws();
        if self.peek() == Some(b'}') {
            self.i += 1;
            return Ok(());
        }
        loop {
            if self.peek() != Some(b'"') {
                return Err(self.unexpected("a key"));
            }
            let k = self.string()?;
            self.eat(b':')?;
            f(self, &k)?;
            self.ws();
            match self.peek() {
                Some(b',') => {
                    self.i += 1;
                    self.ws();
                    if self.peek() == Some(b'}') {
                        self.i += 1;
                        return Ok(());
                    }
                }
                Some(b'}') => {
                    self.i += 1;
                    return Ok(());
                }
                _ => return Err(self.unexpected("',' or '}'")),
            }
        }
    }
    /// The elements of an array (no trailing comma).
    fn elements(&mut self, mut f: impl FnMut(&mut P<'a>) -> R<()>) -> R<()> {
        self.eat(b'[')?;
        self.ws();
        if self.peek() == Some(b']') {
            self.i += 1;
            return Ok(());
        }
        loop {
            f(self)?;
            self.ws();
            match self.peek() {
                Some(b',') => self.i += 1,
                Some(b']') => {
                    self.i += 1;
                    return Ok(());
                }
                _ => return Err(self.unexpected("',' or ']'")),
            }
        }
    }
    fn ints(&mut self, out: &mut Vec<u64>) -> R<()> {
        out.clear();
        self.elements(|p| {
            out.push(p.int()?);
            Ok(())
        })
    }
    /// Any value, read and thrown away (`mdata`'s data, the header).
    fn skip(&mut self, depth: u32) -> R<()> {
        if depth > MAX_DEPTH {
            return Err(cant(format!("values nested more than {MAX_DEPTH} deep")));
        }
        self.ws();
        match self.peek() {
            Some(b'{') => self.members(|p, _| p.skip(depth + 1)),
            Some(b'[') => self.elements(|p| p.skip(depth + 1)),
            Some(b'"') => self.string().map(|_| ()),
            Some(b't') | Some(b'f') => self.boolean().map(|_| ()),
            Some(b'n') if self.s[self.i..].starts_with(b"null") => {
                self.i += 4;
                Ok(())
            }
            Some(c) if c.is_ascii_digit() => {
                while self.peek().is_some_and(|c| c.is_ascii_digit()) {
                    self.i += 1;
                }
                Ok(())
            }
            _ => Err(self.unexpected("a value")),
        }
    }
    fn end(&mut self) -> R<()> {
        self.ws();
        if self.i < self.s.len() {
            return Err(inv(format!("trailing content at column {}", self.i + 1)));
        }
        Ok(())
    }
}

fn utf8(b: &[u8]) -> R<()> {
    if b.is_ascii() || std::str::from_utf8(b).is_ok() {
        Ok(())
    } else {
        Err(inv("a string is not UTF-8"))
    }
}

fn lossy(b: &[u8]) -> Cow<'_, str> {
    String::from_utf8_lossy(b)
}

/// The keys of one object: each one known, none twice, all present.
struct Keys {
    want: &'static [&'static str],
    seen: u32,
}

impl Keys {
    fn of(want: &'static [&'static str]) -> Keys {
        debug_assert!(want.len() <= 32);
        Keys { want, seen: 0 }
    }
    /// The index of `k` among the keys wanted.
    #[inline]
    fn see(&mut self, k: &[u8]) -> R<usize> {
        let Some(i) = self.want.iter().position(|w| w.as_bytes() == k) else {
            return Err(cant(format!("unknown key '{}'", lossy(k))));
        };
        if self.seen >> i & 1 != 0 {
            return Err(inv(format!("key '{}' given twice", self.want[i])));
        }
        self.seen |= 1 << i;
        Ok(i)
    }
    fn all(&self) -> R<()> {
        for (i, w) in self.want.iter().enumerate() {
            if self.seen >> i & 1 == 0 {
                return Err(inv(format!("missing key '{w}'")));
            }
        }
        Ok(())
    }
}

/// One name, for display: its prefix and its component.
#[derive(Clone, Copy, Default)]
struct NameRec {
    prefix: u32,
    /// The number `val`; otherwise a string at `val` in the arena.
    num: bool,
    val: u64,
}

/// Bytes kept in chunks that are never moved.
struct Arena {
    chunks: Vec<Vec<u8>>,
}

const CHUNK: usize = 1 << 24;

impl Arena {
    fn new() -> Arena {
        Arena { chunks: Vec::new() }
    }
    /// Where `s` is kept: chunk << 32 | offset (a string is never split).
    fn push(&mut self, s: &[u8]) -> u64 {
        let need = s.len() + 4;
        let fits = self
            .chunks
            .last()
            .is_some_and(|c| c.capacity() - c.len() >= need);
        if !fits {
            self.chunks.push(Vec::with_capacity(need.max(CHUNK)));
        }
        let k = self.chunks.len() - 1;
        let c = &mut self.chunks[k];
        let at = c.len();
        c.extend_from_slice(&(s.len() as u32).to_le_bytes());
        c.extend_from_slice(s);
        (k as u64) << 32 | at as u64
    }
    fn get(&self, at: u64) -> &[u8] {
        let c = &self.chunks[(at >> 32) as usize];
        let o = at as u32 as usize;
        let n = u32::from_le_bytes(c[o..o + 4].try_into().unwrap()) as usize;
        &c[o + 4..o + 4 + n]
    }
}

struct Nd {
    enc: Enc,
    names: Paged<Node>,
    levels: Paged<Node>,
    exprs: Paged<Node>,
    /// With names asked for: each name's prefix and component.
    show: Option<(Paged<NameRec>, Arena)>,
    ids: Vec<u64>,
    sum: Summary,
}

/// What one line defines.
enum Line<'a> {
    Name(Node, NameRec, Option<Cow<'a, [u8]>>),
    Level(Node),
    /// The hash, and whether the record is an `mdata`.
    Expr(Node, bool),
    /// The declaration and the name it declares first.
    Decl(DeclV, Option<u64>),
}

impl Nd {
    fn name(&self, id: u64) -> R<Node> {
        self.names
            .get(id)
            .ok_or_else(|| inv(format!("name {id} is not defined before")))
    }
    fn level(&self, id: u64) -> R<Node> {
        self.levels
            .get(id)
            .ok_or_else(|| inv(format!("level {id} is not defined before")))
    }
    fn expr(&self, id: u64) -> R<Node> {
        self.exprs
            .get(id)
            .ok_or_else(|| inv(format!("expression {id} is not defined before")))
    }
    fn name_list(&self, ids: &[u64]) -> R<Vec<Node>> {
        ids.iter().map(|&x| self.name(x)).collect()
    }
    fn head(&self, name: u64, params: &[u64], ty: u64) -> R<Head> {
        Ok(Head {
            name: self.name(name)?,
            params: self.name_list(params)?,
            ty: self.expr(ty)?,
        })
    }

    /// The dotted name of name `id`, as the Susz reader displays names.
    fn display(&self, id: u64) -> String {
        let Some((t, a)) = &self.show else {
            return String::new();
        };
        let mut chain = Vec::new();
        let mut x = id;
        while x != 0 {
            let Some(r) = t.get(x) else { break };
            chain.push(r);
            x = r.prefix as u64;
        }
        if chain.is_empty() {
            return ANONYMOUS.into();
        }
        let mut s = String::new();
        for (i, r) in chain.iter().rev().enumerate() {
            if i > 0 {
                s.push('.');
            }
            if r.num {
                s.push_str(&r.val.to_string());
            } else {
                s.push_str(&lossy(a.get(r.val)));
            }
        }
        s
    }

    // The value of a line's kind key.
    fn kind<'a>(&mut self, p: &mut P<'a>, k: &[u8]) -> R<Line<'a>> {
        Ok(match k {
            // names
            b"str" | b"num" => {
                let num = k == b"num";
                let mut keys = Keys::of(if num { &["pre", "i"] } else { &["pre", "str"] });
                let (mut pre, mut v, mut s) = (0u64, 0u64, None);
                p.members(|p, k| {
                    match keys.see(k)? {
                        0 => pre = p.int()?,
                        _ if num => v = p.int()?,
                        _ => s = Some(p.string()?),
                    }
                    Ok(())
                })?;
                keys.all()?;
                let ph = self.name(pre)?;
                // defined, so below 2^32
                let r = NameRec {
                    prefix: pre as u32,
                    num,
                    val: v,
                };
                match s {
                    None => Line::Name(self.enc.name_num(&ph, v), r, None),
                    Some(s) => Line::Name(self.enc.name_str(&ph, &s), r, Some(s)),
                }
            }
            // levels
            b"succ" => {
                let l = self.level(p.int()?)?;
                Line::Level(self.enc.succ(&l))
            }
            b"param" => {
                let n = self.name(p.int()?)?;
                Line::Level(self.enc.param(&n))
            }
            b"max" | b"imax" => {
                let mut ids = std::mem::take(&mut self.ids);
                p.ints(&mut ids)?;
                if ids.len() != 2 {
                    return Err(inv("max and imax take exactly two levels"));
                }
                let (a, b) = (self.level(ids[0])?, self.level(ids[1])?);
                self.ids = ids;
                Line::Level(self.enc.max(k == b"imax", &a, &b))
            }
            // expressions
            b"bvar" => Line::Expr(self.enc.bvar(p.int()?), false),
            b"sort" => {
                let l = self.level(p.int()?)?;
                Line::Expr(self.enc.sort(&l), false)
            }
            b"const" => {
                let mut keys = Keys::of(&["name", "us"]);
                let mut n = 0u64;
                let mut ids = std::mem::take(&mut self.ids);
                p.members(|p, k| {
                    match keys.see(k)? {
                        0 => n = p.int()?,
                        _ => p.ints(&mut ids)?,
                    }
                    Ok(())
                })?;
                keys.all()?;
                let nh = self.name(n)?;
                let mut us = Vec::with_capacity(ids.len());
                for &u in &ids {
                    us.push(self.level(u)?);
                }
                self.ids = ids;
                self.enc.const_start(&nh, us.len() as u64);
                for u in &us {
                    self.enc.push(u);
                }
                Line::Expr(self.enc.const_end(), false)
            }
            b"app" => {
                let mut keys = Keys::of(&["fn", "arg"]);
                let mut x = [0u64; 2];
                p.members(|p, k| {
                    x[keys.see(k)?] = p.int()?;
                    Ok(())
                })?;
                keys.all()?;
                let (f, a) = (self.expr(x[0])?, self.expr(x[1])?);
                Line::Expr(self.enc.app(&f, &a), false)
            }
            b"lam" | b"forallE" => {
                let mut keys = Keys::of(&["binderInfo", "name", "type", "body"]);
                let mut x = [0u64; 3];
                let mut bi = 0u8;
                p.members(|p, k| {
                    match keys.see(k)? {
                        0 => {
                            bi = match &*p.string()? {
                                b"default" => 0,
                                b"implicit" => 1,
                                b"strictImplicit" => 2,
                                b"instImplicit" => 3,
                                o => {
                                    return Err(cant(format!("unknown binderInfo '{}'", lossy(o))))
                                }
                            }
                        }
                        i => x[i - 1] = p.int()?,
                    }
                    Ok(())
                })?;
                keys.all()?;
                let (n, t, b) = (self.name(x[0])?, self.expr(x[1])?, self.expr(x[2])?);
                Line::Expr(self.enc.binder(k == b"forallE", bi, &n, &t, &b), false)
            }
            b"letE" => {
                let mut keys = Keys::of(&["name", "type", "value", "body", "nondep"]);
                let mut x = [0u64; 4];
                p.members(|p, k| {
                    match keys.see(k)? {
                        // elaboration only: read, not hashed (spec 9.1)
                        4 => {
                            p.boolean()?;
                        }
                        i => x[i] = p.int()?,
                    }
                    Ok(())
                })?;
                keys.all()?;
                let (n, t, v, b) = (
                    self.name(x[0])?,
                    self.expr(x[1])?,
                    self.expr(x[2])?,
                    self.expr(x[3])?,
                );
                Line::Expr(self.enc.let_e(&n, &t, &v, &b), false)
            }
            b"natVal" => {
                let d = p.string()?;
                if d.is_empty() || !d.iter().all(u8::is_ascii_digit) {
                    return Err(inv("a Nat literal that is not a decimal natural number"));
                }
                // canonical decimal: no leading zero
                let z = d
                    .iter()
                    .take_while(|&&c| c == b'0')
                    .count()
                    .min(d.len() - 1);
                Line::Expr(self.enc.nat(&d[z..]), false)
            }
            b"strVal" => {
                let s = p.string()?;
                Line::Expr(self.enc.str_lit(&s), false)
            }
            b"proj" => {
                let mut keys = Keys::of(&["typeName", "idx", "struct"]);
                let mut x = [0u64; 3];
                p.members(|p, k| {
                    x[keys.see(k)?] = p.int()?;
                    Ok(())
                })?;
                keys.all()?;
                let (n, e) = (self.name(x[0])?, self.expr(x[2])?);
                Line::Expr(self.enc.proj(&n, x[1], &e), false)
            }
            // the expression it wraps (spec 9.1)
            b"mdata" => {
                let mut keys = Keys::of(&["expr", "data"]);
                let mut e = 0u64;
                p.members(|p, k| {
                    match keys.see(k)? {
                        0 => e = p.int()?,
                        _ => p.skip(0)?,
                    }
                    Ok(())
                })?;
                keys.all()?;
                Line::Expr(self.expr(e)?, true)
            }
            // declarations
            b"inductive" => self.inductive(p)?,
            b"axiom" | b"def" | b"thm" | b"opaque" | b"quot" => self.decl(p, k)?,
            _ => return Err(cant(format!("unknown record kind '{}'", lossy(k)))),
        })
    }

    fn decl<'a>(&mut self, p: &mut P<'a>, k: &[u8]) -> R<Line<'a>> {
        let want: &'static [&'static str] = match k {
            b"axiom" => &["name", "levelParams", "type", "isUnsafe"],
            b"def" => &[
                "name",
                "levelParams",
                "type",
                "value",
                "hints",
                "safety",
                "all",
            ],
            b"thm" => &["name", "levelParams", "type", "value", "all"],
            b"opaque" => &["name", "levelParams", "type", "value", "isUnsafe", "all"],
            _ => &["name", "levelParams", "type", "kind"],
        };
        let mut keys = Keys::of(want);
        let (mut name, mut ty, mut value) = (0u64, 0u64, 0u64);
        let (mut params, mut all) = (Vec::new(), Vec::new());
        let mut flag = false;
        let mut hints = Hints::Opaque;
        let mut byte = 0u8;
        p.members(|p, key| {
            match want[keys.see(key)?] {
                "name" => name = p.int()?,
                "levelParams" => p.ints(&mut params)?,
                "type" => ty = p.int()?,
                "value" => value = p.int()?,
                "isUnsafe" => flag = p.boolean()?,
                "all" => p.ints(&mut all)?,
                "hints" => {
                    p.ws();
                    hints = match p.peek() {
                        Some(b'{') => {
                            let mut hk = Keys::of(&["regular"]);
                            let mut h = 0;
                            p.members(|p, k| {
                                hk.see(k)?;
                                h = p.int()?;
                                Ok(())
                            })?;
                            hk.all()?;
                            Hints::Regular(h)
                        }
                        Some(b'"') => match &*p.string()? {
                            b"opaque" => Hints::Opaque,
                            b"abbrev" => Hints::Abbrev,
                            o => return Err(cant(format!("unknown hints '{}'", lossy(o)))),
                        },
                        _ => return Err(inv("malformed hints")),
                    }
                }
                "safety" => {
                    byte = match &*p.string()? {
                        b"safe" => 0,
                        b"unsafe" => 1,
                        b"partial" => 2,
                        o => return Err(cant(format!("unknown safety '{}'", lossy(o)))),
                    }
                }
                // quot's kind
                _ => {
                    byte = match &*p.string()? {
                        b"type" => 0,
                        b"ctor" => 1,
                        b"lift" => 2,
                        b"ind" => 3,
                        o => return Err(cant(format!("unknown quot kind '{}'", lossy(o)))),
                    }
                }
            }
            Ok(())
        })?;
        keys.all()?;
        let head = self.head(name, &params, ty)?;
        let d = match k {
            b"axiom" => DeclV::Axiom {
                head,
                is_unsafe: flag,
            },
            b"def" => DeclV::Def {
                head,
                value: self.expr(value)?,
                hints,
                safety: byte,
                all: self.name_list(&all)?,
            },
            b"thm" => DeclV::Thm {
                head,
                value: self.expr(value)?,
                all: self.name_list(&all)?,
            },
            b"opaque" => DeclV::Opaque {
                head,
                value: self.expr(value)?,
                is_unsafe: flag,
                all: self.name_list(&all)?,
            },
            _ => DeclV::Quot { head, kind: byte },
        };
        Ok(Line::Decl(d, Some(name)))
    }

    fn inductive<'a>(&mut self, p: &mut P<'a>) -> R<Line<'a>> {
        let mut keys = Keys::of(&["types", "ctors", "recs"]);
        let mut types = Vec::new();
        let mut ctors = Vec::new();
        let mut recs = Vec::new();
        let mut first: [Option<u64>; 3] = [None; 3];
        let this = &*self;
        p.members(|p, k| {
            match keys.see(k)? {
                0 => p.elements(|p| {
                    const W: &[&str] = &[
                        "name",
                        "levelParams",
                        "type",
                        "isUnsafe",
                        "numParams",
                        "numIndices",
                        "all",
                        "ctors",
                        "numNested",
                        "isRec",
                        "isReflexive",
                    ];
                    let mut keys = Keys::of(W);
                    let (mut name, mut ty) = (0u64, 0u64);
                    let (mut params, mut all, mut cs) = (Vec::new(), Vec::new(), Vec::new());
                    let mut n = [0u64; 3];
                    let mut b = [false; 3];
                    p.members(|p, k| {
                        match keys.see(k)? {
                            0 => name = p.int()?,
                            1 => p.ints(&mut params)?,
                            2 => ty = p.int()?,
                            3 => b[0] = p.boolean()?,
                            4 => n[0] = p.int()?,
                            5 => n[1] = p.int()?,
                            6 => p.ints(&mut all)?,
                            7 => p.ints(&mut cs)?,
                            8 => n[2] = p.int()?,
                            9 => b[1] = p.boolean()?,
                            _ => b[2] = p.boolean()?,
                        }
                        Ok(())
                    })?;
                    keys.all()?;
                    first[0].get_or_insert(name);
                    types.push(IndType {
                        head: this.head(name, &params, ty)?,
                        is_unsafe: b[0],
                        num_params: n[0],
                        num_indices: n[1],
                        all: this.name_list(&all)?,
                        ctors: this.name_list(&cs)?,
                        num_nested: n[2],
                        is_rec: b[1],
                        is_reflexive: b[2],
                    });
                    Ok(())
                })?,
                1 => p.elements(|p| {
                    const W: &[&str] = &[
                        "name",
                        "levelParams",
                        "type",
                        "isUnsafe",
                        "induct",
                        "cidx",
                        "numParams",
                        "numFields",
                    ];
                    let mut keys = Keys::of(W);
                    let (mut name, mut ty) = (0u64, 0u64);
                    let mut params = Vec::new();
                    let mut n = [0u64; 4];
                    let mut u = false;
                    p.members(|p, k| {
                        match keys.see(k)? {
                            0 => name = p.int()?,
                            1 => p.ints(&mut params)?,
                            2 => ty = p.int()?,
                            3 => u = p.boolean()?,
                            i => n[i - 4] = p.int()?,
                        }
                        Ok(())
                    })?;
                    keys.all()?;
                    first[1].get_or_insert(name);
                    ctors.push(Ctor {
                        head: this.head(name, &params, ty)?,
                        is_unsafe: u,
                        induct: this.name(n[0])?,
                        cidx: n[1],
                        num_params: n[2],
                        num_fields: n[3],
                    });
                    Ok(())
                })?,
                _ => p.elements(|p| {
                    const W: &[&str] = &[
                        "name",
                        "levelParams",
                        "type",
                        "isUnsafe",
                        "all",
                        "numParams",
                        "numIndices",
                        "numMotives",
                        "numMinors",
                        "rules",
                        "k",
                    ];
                    let mut keys = Keys::of(W);
                    let (mut name, mut ty) = (0u64, 0u64);
                    let (mut params, mut all) = (Vec::new(), Vec::new());
                    let mut n = [0u64; 4];
                    let mut b = [false; 2];
                    let mut rules = Vec::new();
                    p.members(|p, k| {
                        match keys.see(k)? {
                            0 => name = p.int()?,
                            1 => p.ints(&mut params)?,
                            2 => ty = p.int()?,
                            3 => b[0] = p.boolean()?,
                            4 => p.ints(&mut all)?,
                            i @ 5..=8 => n[i - 5] = p.int()?,
                            9 => p.elements(|p| {
                                let mut keys = Keys::of(&["ctor", "nfields", "rhs"]);
                                let mut x = [0u64; 3];
                                p.members(|p, k| {
                                    x[keys.see(k)?] = p.int()?;
                                    Ok(())
                                })?;
                                keys.all()?;
                                rules.push(RecRule {
                                    ctor: this.name(x[0])?,
                                    nfields: x[1],
                                    rhs: this.expr(x[2])?,
                                });
                                Ok(())
                            })?,
                            _ => b[1] = p.boolean()?,
                        }
                        Ok(())
                    })?;
                    keys.all()?;
                    first[2].get_or_insert(name);
                    recs.push(Rec {
                        head: this.head(name, &params, ty)?,
                        is_unsafe: b[0],
                        all: this.name_list(&all)?,
                        num_params: n[0],
                        num_indices: n[1],
                        num_motives: n[2],
                        num_minors: n[3],
                        rules: std::mem::take(&mut rules),
                        k: b[1],
                    });
                    Ok(())
                })?,
            }
            Ok(())
        })?;
        keys.all()?;
        Ok(Line::Decl(
            DeclV::Inductive { types, ctors, recs },
            first[0].or(first[1]).or(first[2]),
        ))
    }

    fn line(&mut self, l: &[u8], acc: &mut Acc, names: bool, each: &mut Each<'_>) -> R<()> {
        let mut p = P { s: l, i: 0 };
        // the id key (0 "in", 1 "il", 2 "ie") and its value; the kind's line
        let mut id: Option<(u8, u64)> = None;
        let mut rec: Option<(u8, Line)> = None;
        p.members(|p, k| {
            let which = match k {
                b"in" => Some(0u8),
                b"il" => Some(1),
                b"ie" => Some(2),
                _ => None,
            };
            if let Some(w) = which {
                if id.is_some() {
                    return Err(cant("a line takes one id"));
                }
                id = Some((w, p.int()?));
                return Ok(());
            }
            if rec.is_some() {
                return Err(cant("a line takes exactly one record kind"));
            }
            let line = self.kind(p, k)?;
            let class = match &line {
                Line::Name(..) => 0,
                Line::Level(_) => 1,
                Line::Expr(..) => 2,
                Line::Decl(..) => 3,
            };
            rec = Some((class, line));
            Ok(())
        })?;
        p.end()?;
        let Some((class, line)) = rec else {
            return Err(cant("unknown record kind"));
        };
        let want = if class == 3 { None } else { Some(class) };
        if id.map(|x| x.0) != want {
            return Err(cant(match want {
                Some(0) => "a name record takes the key 'in'",
                Some(1) => "a level record takes the key 'il'",
                Some(_) => "an expression record takes the key 'ie'",
                None => "a declaration line takes exactly one key",
            }));
        }
        let set_err = |e: SetError, what: &str, i: u64| {
            match e {
            SetError::Twice => inv(format!("{what} {i} is defined twice")),
            SetError::TooLarge => cant(format!("{what} id {i} is 2^32 or more")),
            SetError::Sparse => cant(format!(
                "{what} ids too sparse at {i}: this reader holds at most 16 table entries for each {what} defined"
            )),
        }
        };
        match line {
            Line::Name(h, mut r, s) => {
                let i = id.unwrap().1;
                self.names.set(i, h).map_err(|e| set_err(e, "name", i))?;
                if let Some((t, a)) = &mut self.show {
                    if let Some(s) = s {
                        r.val = a.push(&s);
                    }
                    let _ = t.set(i, r);
                }
                self.sum.names += 1;
            }
            Line::Level(h) => {
                let i = id.unwrap().1;
                self.levels.set(i, h).map_err(|e| set_err(e, "level", i))?;
                self.sum.levels += 1;
            }
            Line::Expr(h, mdata) => {
                let i = id.unwrap().1;
                self.exprs
                    .set(i, h)
                    .map_err(|e| set_err(e, "expression", i))?;
                self.sum.exprs += 1;
                self.sum.extra += mdata as u64;
            }
            Line::Decl(d, first) => {
                let h = self.enc.decl(&d);
                let name = match (names, first) {
                    (false, _) => String::new(),
                    (true, Some(n)) => self.display(n),
                    (true, None) => ANONYMOUS.into(),
                };
                acc.decl(h, d.kind(), &name, each).map_err(Bad::Io)?;
            }
        }
        Ok(())
    }
}

// {"meta":M}, M an object whose format.version is 3.1.x.
fn header(l: &[u8]) -> R<()> {
    let mut p = P { s: l, i: 0 };
    let mut keys = Keys::of(&["meta"]);
    let mut version: Option<Vec<u8>> = None;
    p.members(|p, k| {
        keys.see(k)?;
        p.members(|p, k| {
            if k != b"format" {
                return p.skip(1);
            }
            p.members(|p, k| {
                if k != b"version" {
                    return p.skip(2);
                }
                version = Some(p.string()?.into_owned());
                Ok(())
            })
        })
    })?;
    p.end()?;
    keys.all()?;
    match version {
        Some(v) if v.starts_with(b"3.1.") => Ok(()),
        Some(v) => Err(cant(format!(
            "format version {} is not supported",
            lossy(&v)
        ))),
        None => Err(cant("the header has no format.version")),
    }
}

/// The digest of an ndjson export (lean4export 3.1), read line by line from
/// `r`. With `names`, each entry carries its declaration's dotted name, and
/// the names' components are kept for that.
pub fn ndjson<B: BufRead>(mut r: B, names: bool, each: &mut Each<'_>) -> Result<Summary, Error> {
    let mut nd = Nd {
        enc: Enc::new(),
        names: Paged::new(),
        levels: Paged::new(),
        exprs: Paged::new(),
        show: names.then(|| (Paged::new(), Arena::new())),
        ids: Vec::new(),
        sum: Summary::default(),
    };
    let anon = nd.enc.anon();
    let zero = nd.enc.zero();
    let _ = nd.names.set(0, anon);
    let _ = nd.levels.set(0, zero);
    if let Some((t, _)) = &mut nd.show {
        let _ = t.set(0, NameRec::default());
    }
    let mut acc = Acc::new();
    let mut buf: Vec<u8> = Vec::with_capacity(1 << 16);
    let mut ln: u64 = 0;
    loop {
        buf.clear();
        if r.read_until(b'\n', &mut buf)? == 0 {
            break;
        }
        ln += 1;
        if buf.last() == Some(&b'\n') {
            buf.pop();
        }
        let res = if ln == 1 {
            header(&buf)
        } else if buf.is_empty() {
            Ok(())
        } else {
            nd.line(&buf, &mut acc, names, each)
        };
        match res {
            Ok(()) => {}
            Err(Bad::Invalid(msg)) => return Err(Error::Invalid { line: ln, msg }),
            Err(Bad::Cannot(msg)) => return Err(Error::Cannot { line: ln, msg }),
            Err(Bad::Io(e)) => return Err(Error::Io(e)),
        }
    }
    if ln == 0 {
        return Err(Error::Invalid {
            line: 0,
            msg: "the input is empty".into(),
        });
    }
    let mut s = acc.end();
    s.names = nd.sum.names;
    s.levels = nd.sum.levels;
    s.exprs = nd.sum.exprs;
    s.extra = nd.sum.extra;
    Ok(s)
}

/// The file digest of an ndjson export at `path`.
pub fn of_ndjson(path: &str) -> Result<Hash, Error> {
    let f = std::fs::File::open(path)?;
    ndjson(io::BufReader::with_capacity(1 << 20, f), false, &mut |_| {
        Ok(())
    })
    .map(|s| s.digest)
}

#[cfg(test)]
mod tests {
    use super::*;

    // Pages come as ids come, in any order, within the bound.
    #[test]
    fn paged_tables() {
        let mut t: Paged<u32> = Paged::new();
        assert!(t.get(0).is_none());
        assert!(t.set(70_000, 7).is_ok());
        assert!(t.set(3, 3).is_ok());
        assert_eq!(t.get(70_000), Some(7));
        assert_eq!(t.get(3), Some(3));
        assert_eq!(t.get(4), None);
        assert_eq!(t.get(1 << 40), None);
        assert!(matches!(t.set(3, 1), Err(SetError::Twice)));
        assert!(matches!(t.set(1 << 32, 1), Err(SetError::TooLarge)));
        // one entry a page: 4 pages, then no more
        let mut s: Paged<u8> = Paged::new();
        let mut k = 0u64;
        let r = loop {
            if let Err(e) = s.set(k << PAGE_BITS, 1) {
                break e;
            }
            k += 1;
        };
        assert!(matches!(r, SetError::Sparse));
        assert_eq!(k, 4);
    }

    #[test]
    fn printable_names() {
        assert_eq!(printable("Nat.add"), "Nat.add");
        assert_eq!(printable("a\nb\u{7f}"), "a\\x0ab\\x7f");
        assert_eq!(printable("a\u{85}é"), "a\\x85é");
    }

    // The encoding of a few nodes, byte for byte (spec 9.3).
    #[test]
    fn encodings() {
        let mut e = Enc::new();
        assert_eq!(e.anon(), node(&[0x01]));
        assert_eq!(e.zero(), node(&[0x10]));
        let a = e.anon();
        let mut b = vec![0x02];
        b.extend_from_slice(&a);
        b.extend_from_slice(&3u64.to_le_bytes());
        b.extend_from_slice(b"Nat");
        assert_eq!(e.name_str(&a, b"Nat"), node(&b));
        // the spec's example
        assert_eq!(hex(&a), "4bf5122f344554c53bde2ebb8cd2b7e3");
        assert_eq!(hex(&node(&b)), "68a9193ec9256ad58b3ddf294e10ce13");
        let mut b = vec![0x20];
        b.extend_from_slice(&5u64.to_le_bytes());
        assert_eq!(e.bvar(5), node(&b));
        // SHA-256("") and SHA-256("abc"): the hash is the standard one
        assert_eq!(
            hex(&sha(b"")),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
        assert_eq!(
            hex(&sha(b"abc")),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
    }

    fn nd(text: &str) -> Result<Hash, String> {
        ndjson(text.as_bytes(), false, &mut |_| Ok(()))
            .map(|s| s.digest)
            .map_err(|e| e.to_string())
    }

    // Leading zeros of a natVal do not count, "0" is zero, and the Susz
    // side's conversion gives the same canonical text.
    #[test]
    fn nat_canonical_decimal() {
        let one = |lit: &str| {
            nd(&format!(
                "{{\"meta\":{{\"format\":{{\"version\":\"3.1.0\"}}}}}}\n\
                 {{\"ie\":0,\"natVal\":\"{lit}\"}}\n\
                 {{\"in\":1,\"str\":{{\"pre\":0,\"str\":\"A\"}}}}\n\
                 {{\"axiom\":{{\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"type\":0}}}}\n"
            ))
        };
        assert_eq!(one("0").unwrap(), one("000").unwrap());
        assert_eq!(one("42").unwrap(), one("0042").unwrap());
        assert_ne!(one("42").unwrap(), one("420").unwrap());
        assert!(one("").is_err());
        assert!(one("-1").is_err());
        assert!(one("1e3").is_err());
        let mut e = Enc::new();
        for (le, dec) in [
            (vec![], "0"),
            (vec![1], "1"),
            (vec![0, 1], "256"),
            (vec![0, 0, 0, 0, 0, 0, 0, 0, 1], "18446744073709551616"),
        ] {
            assert_eq!(crate::format::nat_to_decimal(&le), dec);
            assert_eq!(
                e.nat(dec.as_bytes()),
                e.nat(crate::format::nat_to_decimal(&le).as_bytes())
            );
        }
    }

    // The reader's dialect and its strictness.
    #[test]
    fn ndjson_dialect() {
        let h = "{\"meta\":{\"format\":{\"version\":\"3.1.0\"}}}\n";
        let ax = "{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"type\":0}}\n";
        let base = format!(
            "{h}{{\"in\":1,\"str\":{{\"pre\":0,\"str\":\"A\"}}}}\n{{\"ie\":0,\"sort\":0}}\n{ax}"
        );
        let d = nd(&base).unwrap();
        // spacing, key order, escapes, leading zeros, a trailing comma in
        // an object, CRLF, empty lines
        let other = format!(
            "{h}{{ \"str\" : {{\"str\":\"\\u0041\",\"pre\":00}} , \"in\":1, }}\r\n\n{{\"sort\":0,\"ie\":0}}\n{ax}"
        );
        assert_eq!(nd(&other).unwrap(), d);
        let bad = |s: String, want: &str| {
            let e = nd(&s).unwrap_err();
            assert!(e.starts_with(want), "{s:?}: {e}");
        };
        // an unknown key or kind is refused, never skipped
        bad(
            base.replace("\"sort\":0}", "\"sort\":0,\"x\":1}"),
            "cannot digest",
        );
        bad(base.replace("\"sort\"", "\"sorts\""), "cannot digest");
        bad(
            base.replace("\"isUnsafe\":false,", "\"isUnsafe\":false,\"extra\":[],"),
            "cannot digest",
        );
        bad(base.replace("{\"axiom\"", "{\"lemma\""), "cannot digest");
        bad(base.replace("3.1.0", "2.0.0"), "cannot digest");
        // broken exports
        bad(
            base.replace("\"type\":0", "\"type\":7"),
            "not a valid export",
        );
        bad(base.replace("\"pre\":0,", ""), "not a valid export");
        bad(
            base.replace("\"pre\":0,", "\"pre\":0,\"pre\":0,"),
            "not a valid export",
        );
        bad(base.replace("[]", "[],"), "not a valid export");
        bad(base.replace("\"A\"", "\"\\ud800\""), "not a valid export");
        bad(base.replace("\"A\"", "\"\\udc00\""), "not a valid export");
        bad(
            format!("{base}{{\"ie\":0,\"bvar\":0}}\n"),
            "not a valid export",
        );
        bad(
            base.replace("\"sort\":0}", "\"sort\":0} x"),
            "not a valid export",
        );
        bad(base[..base.len() - 3].to_string(), "not a valid export");
        bad(String::new(), "not a valid export");
        // mdata's data is read through, and stands for its expression
        let md = base.replace(
            "{\"ie\":0,\"sort\":0}\n",
            "{\"ie\":5,\"sort\":0}\n{\"ie\":0,\"mdata\":{\"data\":{\"k\":[1,true,null,\"s\",{}]},\"expr\":5}}\n",
        );
        assert_eq!(nd(&md).unwrap(), d);
    }
}
