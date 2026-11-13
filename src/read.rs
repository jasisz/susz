//! The reader: framing (header, trailer, directory), MAIN records, proof
//! blocks by range, and the full structural check ([`verify`]).
//!
//! [`decode`] is the way in for a checker: one pass over the file that hands
//! each record to a [`Visit`] right after checking it, with a theorem's
//! proof block decoded before the theorem, or left for [`decode_block`].
//! [`verify`] is that same pass with a visitor that does nothing. The
//! iterators ([`Main`], [`Block`]) check as they go as well.
//!
//! Every rule of spec sections 3-6 is checked; the first error is reported
//! with its section, absolute byte offset and record number (spec section
//! 8), the same whatever the order blocks are read in.

use crate::canon::Canon;
use crate::format::{self, VarintError};
use std::fmt;

/// The class of a structural error (or of a decline).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Class {
    /// Bad magic.
    Magic,
    /// Another major version (declined).
    Major,
    /// A reserved field is not zero.
    Reserved,
    /// Bad end magic.
    EndMagic,
    /// The trailer length is impossible or disagrees with the section count.
    TrailerLength,
    /// Directory flags: unknown bits, or flags of a known id that differ from the table.
    SectionFlags,
    /// A section id given twice.
    SectionDuplicate,
    /// Sections do not tile the body (gap, overlap, outside the body).
    SectionTiling,
    /// MAIN is missing.
    SectionMissing,
    /// An unknown must-understand section (declined).
    MustUnderstand,
    /// A PAD byte is not zero.
    PadNonZero,
    /// A record or field runs past the end of its section or block.
    Truncated,
    /// A varint that is not minimal.
    VarintNonMinimal,
    /// A varint of more than 10 bytes or not below 2^64.
    VarintOverflow,
    /// A string that is not well-formed UTF-8.
    Utf8,
    /// A `nat` that ends in a zero byte.
    NatNonMinimal,
    /// A bool that is not 0 or 1.
    Bool,
    /// An enum byte out of range.
    Enum,
    /// An unknown or misplaced record tag.
    Tag,
    /// An expression back distance (or block reference) of 0 or past the start.
    BackDistance,
    /// A name id not yet defined.
    NameId,
    /// A level id not yet defined.
    LevelId,
    /// A frontier entry's back distance of 0 or past the start.
    FrontierBack,
    /// An item listed twice in the frontier.
    FrontierDuplicate,
    /// A frontier index in a block not listed before the theorem.
    FrontierIndex,
    /// A name declared twice.
    DuplicateName,
    /// A declaration declares the anonymous name.
    AnonymousName,
    /// A block names a constant not declared before its theorem. This is a
    /// declaration failure, not a structural error (spec section 2).
    RuleP,
    /// `block-exprs` of 0 or more than `block-length / 2`.
    BlockExprs,
    /// Blocks do not fill PROOFS exactly (or PROOFS without blocks).
    ProofsFill,
    /// A block holds fewer or more records than `block-exprs`.
    BlockCount,
    /// The trailer's counts differ from what MAIN defines.
    Counts,
    /// The file goes past one of this reader's own limits (declined).
    Limit,
}

impl Class {
    /// The class's name in test vectors.
    pub fn name(self) -> &'static str {
        use Class::*;
        match self {
            Magic => "magic",
            Major => "major",
            Reserved => "reserved",
            EndMagic => "end-magic",
            TrailerLength => "trailer-length",
            SectionFlags => "section-flags",
            SectionDuplicate => "section-duplicate",
            SectionTiling => "section-tiling",
            SectionMissing => "section-missing",
            MustUnderstand => "must-understand",
            PadNonZero => "pad-nonzero",
            Truncated => "truncated",
            VarintNonMinimal => "varint-nonminimal",
            VarintOverflow => "varint-overflow",
            Utf8 => "utf8",
            NatNonMinimal => "nat-nonminimal",
            Bool => "bool",
            Enum => "enum",
            Tag => "tag",
            BackDistance => "back-distance",
            NameId => "name-id",
            LevelId => "level-id",
            FrontierBack => "frontier-back",
            FrontierDuplicate => "frontier-duplicate",
            FrontierIndex => "frontier-index",
            DuplicateName => "duplicate-name",
            AnonymousName => "anonymous-name",
            RuleP => "rule-p",
            BlockExprs => "block-exprs",
            ProofsFill => "proofs-fill",
            BlockCount => "block-count",
            Counts => "counts",
            Limit => "limit",
        }
    }
    /// Classes that decline instead of rejecting.
    pub fn declines(self) -> bool {
        matches!(self, Class::Major | Class::MustUnderstand | Class::Limit)
    }
    /// Classes that are declaration failures (spec section 2): the file is
    /// well-formed up to the error, and the declaration fails. Every other
    /// rejecting class is a structural error.
    pub fn is_declaration_failure(self) -> bool {
        matches!(self, Class::RuleP)
    }
}

/// Where an error is: the header, the trailer, the directory or a section.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Place {
    Header,
    Trailer,
    Directory,
    Section(u16),
}

impl fmt::Display for Place {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Place::Header => f.write_str("header"),
            Place::Trailer => f.write_str("trailer"),
            Place::Directory => f.write_str("directory"),
            Place::Section(id) => f.write_str(&format::section_name(*id)),
        }
    }
}

/// A located structural error or decline.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Failure {
    pub class: Class,
    pub place: Place,
    /// Absolute byte offset: of the offending record's first byte, or of the
    /// field for header, trailer and directory errors.
    pub offset: u64,
    /// The record's number in its section or block, from 1 (the directory
    /// entry's number for directory errors; 0 when there is none).
    pub record: u64,
    /// For an error in a proof block: the theorem's declaration index.
    pub decl: Option<u32>,
    /// For an error in a proof block: the theorem's name.
    pub theorem: Option<String>,
    pub message: String,
}

impl Failure {
    fn new(
        class: Class,
        place: Place,
        offset: u64,
        record: u64,
        message: impl Into<String>,
    ) -> Failure {
        Failure {
            class,
            place,
            offset,
            record,
            decl: None,
            theorem: None,
            message: message.into(),
        }
    }
}

fn group(n: u64) -> String {
    let s = n.to_string();
    let mut out = String::new();
    for (i, c) in s.chars().enumerate() {
        if i > 0 && (s.len() - i) % 3 == 0 {
            out.push(',');
        }
        out.push(c);
    }
    out
}

impl fmt::Display for Failure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} @ {}: ", self.place, group(self.offset))?;
        if let Some(t) = &self.theorem {
            write!(f, "block of {t}, ")?;
        }
        match self.place {
            Place::Directory if self.record > 0 => write!(f, "entry {}: ", self.record)?,
            Place::Section(_) if self.record > 0 => write!(f, "record {}: ", self.record)?,
            _ => {}
        }
        write!(f, "{} ({})", self.message, self.class.name())
    }
}

impl std::error::Error for Failure {}

/// The result of a full structural check.
#[derive(Debug, Clone)]
pub enum Outcome {
    Accepted(Summary),
    Rejected(Failure),
    Declined(Failure),
}

impl Outcome {
    fn of(f: Failure) -> Outcome {
        if f.class.declines() {
            Outcome::Declined(f)
        } else {
            Outcome::Rejected(f)
        }
    }
}

/// What an accepted file holds.
#[derive(Debug, Clone, Default)]
pub struct Summary {
    /// Names and levels (each with its implicit 0), MAIN expressions, declarations.
    pub counts: [u32; 4],
    pub blocks: u64,
    pub block_exprs: u64,
    pub frontier: [u64; 3],
}

/// A section of the directory.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Section {
    pub id: u16,
    pub flags: u16,
    pub offset: u64,
    pub length: u64,
}

/// A file whose framing (header, trailer, directory, PAD) is verified.
pub struct File<'a> {
    pub bytes: &'a [u8],
    /// The counts of the trailer: names, levels, MAIN expressions, declarations.
    pub counts: [u32; 4],
    pub sections: Vec<Section>,
    /// Absolute offset of the trailer.
    pub trailer: u64,
}

fn u16_at(b: &[u8], p: u64) -> u16 {
    u16::from_le_bytes(b[p as usize..p as usize + 2].try_into().unwrap())
}
fn u32_at(b: &[u8], p: u64) -> u32 {
    u32::from_le_bytes(b[p as usize..p as usize + 4].try_into().unwrap())
}
fn u64_at(b: &[u8], p: u64) -> u64 {
    u64::from_le_bytes(b[p as usize..p as usize + 8].try_into().unwrap())
}

impl<'a> File<'a> {
    /// Checks the header, trailer, directory and PAD sections, in that
    /// order (spec 4 and 8).
    pub fn open(bytes: &'a [u8]) -> Result<File<'a>, Failure> {
        let len = bytes.len() as u64;
        let hd = |c, off, m: &str| Failure::new(c, Place::Header, off, 0, m);
        if len < 8 || bytes[..8] != format::MAGIC {
            return Err(hd(Class::Magic, 0, "not a Susz file (bad magic)"));
        }
        if len < format::HEADER_LEN {
            return Err(hd(Class::Truncated, 8, "the header is cut short"));
        }
        let major = u16_at(bytes, 8);
        if major != format::MAJOR {
            return Err(hd(
                Class::Major,
                8,
                &format!("major version {major}: this reader reads major 1"),
            ));
        }
        if u16_at(bytes, 10) != 0 {
            return Err(hd(Class::Reserved, 10, "reserved header field is not zero"));
        }
        if u32_at(bytes, 12) != 0 {
            return Err(hd(Class::Reserved, 12, "reserved header field is not zero"));
        }
        let tr = |c, off, m: &str| Failure::new(c, Place::Trailer, off, 0, m);
        const MIN_TRAILER: u64 = 16 + 4 + 8;
        if len < format::HEADER_LEN + MIN_TRAILER {
            return Err(tr(
                Class::Truncated,
                format::HEADER_LEN,
                "the file is too short for a trailer",
            ));
        }
        if bytes[len as usize - 4..] != format::END_MAGIC {
            return Err(tr(Class::EndMagic, len - 4, "bad end magic"));
        }
        let tl = u32_at(bytes, len - 8) as u64;
        if tl < MIN_TRAILER || tl > len - format::HEADER_LEN {
            return Err(tr(
                Class::TrailerLength,
                len - 8,
                &format!("trailer length {tl} is impossible"),
            ));
        }
        let ts = len - tl;
        let n = u32_at(bytes, ts + 16) as u64;
        if tl != MIN_TRAILER + format::ENTRY_LEN * n {
            return Err(tr(
                Class::TrailerLength,
                len - 8,
                &format!("trailer length {tl} does not hold {n} directory entries"),
            ));
        }
        let counts = [
            u32_at(bytes, ts),
            u32_at(bytes, ts + 4),
            u32_at(bytes, ts + 8),
            u32_at(bytes, ts + 12),
        ];
        let mut sections: Vec<Section> = Vec::with_capacity(n as usize);
        let mut at = format::HEADER_LEN;
        for i in 0..n {
            let e = ts + 20 + format::ENTRY_LEN * i;
            let dir = |c, off, m: String| Failure::new(c, Place::Directory, off, i + 1, m);
            let id = u16_at(bytes, e);
            let flags = u16_at(bytes, e + 2);
            if u32_at(bytes, e + 4) != 0 {
                return Err(dir(
                    Class::Reserved,
                    e + 4,
                    "reserved entry field is not zero".into(),
                ));
            }
            if flags & !format::MUST_UNDERSTAND != 0 {
                return Err(dir(
                    Class::SectionFlags,
                    e + 2,
                    format!("flags {flags:#x} set reserved bits"),
                ));
            }
            if let Some(k) = format::known_flags(id) {
                if k != flags {
                    return Err(dir(
                        Class::SectionFlags,
                        e + 2,
                        format!(
                            "{} must have flags {k}, not {flags}",
                            format::section_name(id)
                        ),
                    ));
                }
            }
            if sections.iter().any(|s| s.id == id) {
                return Err(dir(
                    Class::SectionDuplicate,
                    e,
                    format!("{} listed twice", format::section_name(id)),
                ));
            }
            let offset = u64_at(bytes, e + 8);
            let length = u64_at(bytes, e + 16);
            if offset != at {
                return Err(dir(
                    Class::SectionTiling,
                    e + 8,
                    format!(
                        "{} starts at {offset}, not where the one before ends ({at})",
                        format::section_name(id)
                    ),
                ));
            }
            match offset.checked_add(length) {
                Some(end) if end <= ts => at = end,
                _ => {
                    return Err(dir(
                        Class::SectionTiling,
                        e + 16,
                        format!("{} runs past the trailer", format::section_name(id)),
                    ))
                }
            }
            sections.push(Section {
                id,
                flags,
                offset,
                length,
            });
        }
        if at != ts {
            let (off, rec) = if n == 0 {
                (ts + 16, 0)
            } else {
                (ts + 20 + format::ENTRY_LEN * (n - 1) + 16, n)
            };
            return Err(Failure::new(
                Class::SectionTiling,
                Place::Directory,
                off,
                rec,
                format!("the sections end at {at}, the trailer starts at {ts}"),
            ));
        }
        if !sections.iter().any(|s| s.id == format::SEC_MAIN) {
            return Err(Failure::new(
                Class::SectionMissing,
                Place::Directory,
                ts + 16,
                0,
                "no MAIN section",
            ));
        }
        for (i, s) in sections.iter().enumerate() {
            if format::known_flags(s.id).is_none() && s.flags & format::MUST_UNDERSTAND != 0 {
                return Err(Failure::new(
                    Class::MustUnderstand,
                    Place::Directory,
                    ts + 20 + format::ENTRY_LEN * i as u64,
                    i as u64 + 1,
                    format!("needs section {}", s.id),
                ));
            }
        }
        for s in &sections {
            if s.id == format::SEC_PAD {
                let body = &bytes[s.offset as usize..(s.offset + s.length) as usize];
                if let Some(k) = body.iter().position(|&x| x != 0) {
                    return Err(Failure::new(
                        Class::PadNonZero,
                        Place::Section(format::SEC_PAD),
                        s.offset + k as u64,
                        0,
                        "PAD holds a non-zero byte",
                    ));
                }
            }
        }
        Ok(File {
            bytes,
            counts,
            sections,
            trailer: ts,
        })
    }

    pub fn section(&self, id: u16) -> Option<Section> {
        self.sections.iter().copied().find(|s| s.id == id)
    }

    /// The bytes of a section.
    pub fn body(&self, s: Section) -> &'a [u8] {
        &self.bytes[s.offset as usize..(s.offset + s.length) as usize]
    }

    /// The SOURCE section's bytes (the export's `meta`), if present.
    pub fn source(&self) -> Option<&'a [u8]> {
        self.section(format::SEC_SOURCE).map(|s| self.body(s))
    }

    /// A reader of MAIN's records.
    pub fn main(&self) -> Main<'a> {
        let s = self.section(format::SEC_MAIN).expect("open checks MAIN");
        let proofs = self.section(format::SEC_PROOFS);
        Main {
            bytes: self.bytes,
            p: s.offset as usize,
            end: (s.offset + s.length) as usize,
            start: s.offset,
            rec: 0,
            done: false,
            counts: self.counts,
            trailer: self.trailer,
            proofs,
            st: State::new(self.counts, s.length),
        }
    }
}

// ---------------------------------------------------------------------------
// Decoded records

/// A name component. A string component is borrowed from the file and is
/// already checked to be well-formed UTF-8.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Component<'a> {
    Str(&'a str),
    Num(u64),
}

/// A list of ids already checked, decoded on demand (through a frontier
/// table inside a block).
#[derive(Clone, Copy)]
pub struct Ids<'a> {
    raw: &'a [u8],
    n: u64,
    map: Option<&'a [u32]>,
}

impl<'a> Ids<'a> {
    pub fn len(&self) -> u64 {
        self.n
    }
    pub fn is_empty(&self) -> bool {
        self.n == 0
    }
    pub fn iter(&self) -> impl Iterator<Item = u32> + 'a {
        let raw = self.raw;
        let map = self.map;
        let mut p = 0usize;
        (0..self.n).map(move |_| {
            // the varints were checked when the list was read
            let mut v = 0u64;
            let mut sh = 0;
            while let Some(&x) = raw.get(p) {
                p += 1;
                v |= ((x & 0x7f) as u64) << (sh & 63);
                if x < 0x80 {
                    break;
                }
                sh += 7;
            }
            match map {
                Some(m) => m[v as usize],
                None => v as u32,
            }
        })
    }
    pub fn to_vec(&self) -> Vec<u32> {
        self.iter().collect()
    }
}

impl fmt::Debug for Ids<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

/// An expression reference: a MAIN expression id, or the k-th expression of
/// the current block.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Ref {
    Main(u32),
    Block(u32),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Level {
    Succ(u32),
    Max(u32, u32),
    IMax(u32, u32),
    Param(u32),
}

/// Binder: 0 default, 1 implicit, 2 strict implicit, 3 instance implicit.
pub type Binder = u8;

#[derive(Debug, Clone, Copy)]
pub enum Expr<'a> {
    BVar(u64),
    Sort(u32),
    Const(u32, Ids<'a>),
    App(Ref, Ref),
    Lam(Binder, u32, Ref, Ref),
    Pi(Binder, u32, Ref, Ref),
    Let(u32, Ref, Ref, Ref),
    /// Minimal little-endian bytes.
    Nat(&'a [u8]),
    Str(&'a str),
    Proj(u32, u64, Ref),
}

#[derive(Debug, Clone, Copy)]
pub struct Head<'a> {
    pub name: u32,
    pub params: Ids<'a>,
    /// MAIN expression id.
    pub ty: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Hints {
    Opaque,
    Abbrev,
    Regular(u64),
}

#[derive(Debug, Clone)]
pub struct IndType<'a> {
    pub head: Head<'a>,
    pub is_unsafe: bool,
    pub num_params: u64,
    pub num_indices: u64,
    pub all: Ids<'a>,
    pub ctors: Ids<'a>,
    pub num_nested: u64,
    pub is_rec: bool,
    pub is_reflexive: bool,
}

#[derive(Debug, Clone)]
pub struct Ctor<'a> {
    pub head: Head<'a>,
    pub is_unsafe: bool,
    pub induct: u32,
    pub cidx: u64,
    pub num_params: u64,
    pub num_fields: u64,
}

#[derive(Debug, Clone, Copy)]
pub struct Rule {
    pub ctor: u32,
    pub nfields: u64,
    pub rhs: u32,
}

#[derive(Debug, Clone)]
pub struct Rec<'a> {
    pub head: Head<'a>,
    pub is_unsafe: bool,
    pub all: Ids<'a>,
    pub num_params: u64,
    pub num_indices: u64,
    pub num_motives: u64,
    pub num_minors: u64,
    pub rules: Vec<Rule>,
    pub k: bool,
}

#[derive(Debug, Clone)]
pub struct Inductive<'a> {
    pub types: Vec<IndType<'a>>,
    pub ctors: Vec<Ctor<'a>>,
    pub recs: Vec<Rec<'a>>,
}

/// A theorem's proof block: where it is and what it may name.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BlockRef {
    /// The theorem's declaration index.
    pub decl: u32,
    /// The theorem's name id.
    pub name: u32,
    /// Absolute offset and length of the block.
    pub offset: u64,
    pub length: u64,
    /// Its number of expression records.
    pub exprs: u64,
    /// Frontier entries (names, levels, expressions) listed before the theorem.
    pub frontier: [u32; 3],
}

#[derive(Debug, Clone)]
pub enum Decl<'a> {
    Axiom {
        head: Head<'a>,
        is_unsafe: bool,
    },
    /// `safety`: 0 safe, 1 unsafe, 2 partial.
    Defn {
        head: Head<'a>,
        value: u32,
        hints: Hints,
        safety: u8,
        all: Ids<'a>,
    },
    Thm {
        head: Head<'a>,
        value: u32,
        all: Ids<'a>,
    },
    Opaque {
        head: Head<'a>,
        value: u32,
        is_unsafe: bool,
        all: Ids<'a>,
    },
    /// `kind`: 0 type, 1 ctor, 2 lift, 3 ind.
    Quot {
        head: Head<'a>,
        kind: u8,
    },
    Inductive(Box<Inductive<'a>>),
    /// A theorem whose value is the last expression of its proof block.
    ThmBlock {
        head: Head<'a>,
        block: BlockRef,
        all: Ids<'a>,
    },
}

impl Decl<'_> {
    /// The kind byte (0-6).
    pub fn kind(&self) -> u8 {
        match self {
            Decl::Axiom { .. } => 0,
            Decl::Defn { .. } => 1,
            Decl::Thm { .. } => 2,
            Decl::Opaque { .. } => 3,
            Decl::Quot { .. } => 4,
            Decl::Inductive(_) => 5,
            Decl::ThmBlock { .. } => 6,
        }
    }
}

/// A MAIN record.
#[derive(Debug, Clone)]
pub enum Event<'a> {
    Name {
        id: u32,
        prefix: u32,
        part: Component<'a>,
    },
    Level {
        id: u32,
        level: Level,
    },
    Expr {
        id: u32,
        expr: Expr<'a>,
    },
    /// `kind`: 0 name, 1 level, 2 expression; `index` counts entries of that kind.
    Frontier {
        kind: u8,
        index: u32,
        item: u32,
    },
    /// `offset`: absolute offset of the record's tag byte.
    Decl {
        index: u32,
        offset: u64,
        decl: Decl<'a>,
    },
}

// ---------------------------------------------------------------------------
// MAIN

const NONE: u32 = u32::MAX;

/// The most expressions a proof block may hold (spec 7.1), so that a block
/// index fits a u32.
pub const MAX_BLOCK_EXPRS: u64 = u32::MAX as u64;

/// What MAIN defined so far.
pub struct State {
    pub names: u32,
    pub levels: u32,
    pub exprs: u32,
    pub decls: u32,
    /// Canonical names (string components point into the file).
    pub canon: Canon,
    /// Name id to canonical id.
    pub name_canon: Vec<u32>,
    /// Canonical id to the index of the declaration declaring it (`u32::MAX`: none).
    pub canon_decl: Vec<u32>,
    /// Frontier tables: entry index to item id, per kind.
    pub frontier: [Vec<u32>; 3],
    listed: [Vec<u64>; 3],
    /// Every proof block, in declaration order.
    pub blocks: Vec<BlockRef>,
    proofs_used: u64,
}

impl State {
    fn new(counts: [u32; 4], main_len: u64) -> State {
        // counts are hints: never reserve more than the bytes can hold
        let cap = |c: u32, per: u64| (c as u64).min(main_len / per) as usize;
        let mut name_canon = Vec::with_capacity(cap(counts[0], 3));
        name_canon.push(crate::canon::ANON);
        State {
            names: 1,
            levels: 1,
            exprs: 0,
            decls: 0,
            canon: Canon::new(),
            name_canon,
            canon_decl: vec![NONE],
            frontier: [Vec::new(), Vec::new(), Vec::new()],
            listed: [Vec::new(), Vec::new(), Vec::new()],
            blocks: Vec::new(),
            proofs_used: 0,
        }
    }
    /// The dotted form of name `id`, for messages.
    pub fn name_display(&self, bytes: &[u8], id: u32) -> String {
        self.canon.display(bytes, self.name_canon[id as usize])
    }
    fn next(&self, kind: u8) -> u32 {
        match kind {
            0 => self.names,
            1 => self.levels,
            _ => self.exprs,
        }
    }
}

type E = (Class, String);

fn verr(e: VarintError) -> E {
    match e {
        VarintError::Truncated => (Class::Truncated, "the record runs past the end".into()),
        VarintError::NonMinimal => (Class::VarintNonMinimal, "a varint is not minimal".into()),
        VarintError::Overflow => (Class::VarintOverflow, "a varint is too long".into()),
    }
}

/// A cursor over a section or block. `b` ends where the section or block
/// ends; positions are absolute offsets in the file.
struct Cur<'a> {
    b: &'a [u8],
    p: usize,
}

const HIGH: u64 = 0x8080_8080_8080_8080;

/// The fast paths of [`decode`] and [`decode_block`]: a record is read with
/// plain loads and accepted only if every check passes. Anything else (a
/// record near the end of the file, a varint longer than 8 bytes, any error)
/// gives `None`, and the record is read again by the checked reader, which
/// gives the error and its place.
///
/// A fast-path record is read from a window of the file at its first byte;
/// its varints start before byte 64 of the window (a record of the fast
/// path is shorter than that), so a load never needs a bounds check. The
/// bytes may run past the section: the caller checks where the record ends.
const WIN: usize = 72;

/// A varint of at most 8 bytes at offset `o` of a window, minimal.
#[inline(always)]
fn fw(win: &[u8; WIN], o: &mut usize) -> Option<u64> {
    // o < 64 always (see WIN); the mask only lets the compiler see it
    let i = *o & 63;
    let w = u64::from_le_bytes(win[i..i + 8].try_into().unwrap());
    word_varint(w, o)
}

/// A varint of at most 8 bytes at `p` of `b`, minimal.
#[inline(always)]
fn fv(b: &[u8], p: &mut usize) -> Option<u64> {
    let w = u64::from_le_bytes(b.get(*p..*p + 8)?.try_into().unwrap());
    word_varint(w, p)
}

/// The varint at the start of the little-endian word `w`, if it has at most
/// 8 bytes and is minimal; `p` moves past it.
#[inline(always)]
fn word_varint(w: u64, p: &mut usize) -> Option<u64> {
    if w & 0x80 == 0 {
        *p += 1;
        return Some(w & 0x7f);
    }
    // two to four bytes: the last one (with its high bit clear) is not zero
    if w & 0x8000 == 0 {
        let hi = (w >> 8) & 0x7f;
        if hi == 0 {
            return None;
        }
        *p += 2;
        return Some((w & 0x7f) | hi << 7);
    }
    if w & 0x80_0000 == 0 {
        let hi = (w >> 16) & 0x7f;
        if hi == 0 {
            return None;
        }
        *p += 3;
        return Some((w & 0x7f) | (w >> 1) & 0x3f80 | hi << 14);
    }
    if w & 0x8000_0000 == 0 {
        let hi = (w >> 24) & 0x7f;
        if hi == 0 {
            return None;
        }
        *p += 4;
        return Some((w & 0x7f) | (w >> 1) & 0x3f80 | (w >> 2) & 0x1f_c000 | hi << 21);
    }
    let stop = !w & HIGH;
    if stop == 0 {
        return None;
    }
    // bytes in the varint, 5..=8; the last one is not zero
    let n = stop.trailing_zeros() / 8 + 1;
    if (w >> (8 * (n - 1))) & 0xff == 0 {
        return None;
    }
    let x = if n == 8 {
        w
    } else {
        w & ((1u64 << (8 * n)) - 1)
    };
    let x = (x & 0x007f_007f_007f_007f) | ((x & 0x7f00_7f00_7f00_7f00) >> 1);
    let x = (x & 0x0000_3fff_0000_3fff) | ((x & 0x3fff_0000_3fff_0000) >> 2);
    let x = (x & 0x0fff_ffff) | ((x & 0x0fff_ffff_0000_0000) >> 4);
    *p += n as usize;
    Some(x)
}

impl<'a> Cur<'a> {
    #[inline(always)]
    fn left(&self) -> usize {
        self.b.len() - self.p
    }
    /// A varint, with every rule of spec section 3.
    #[inline(always)]
    fn v(&mut self) -> Result<u64, E> {
        if let Some(&x) = self.b.get(self.p) {
            if x < 0x80 {
                self.p += 1;
                return Ok(x as u64);
            }
        }
        self.v_long()
    }
    /// A varint of two bytes or more: up to eight bytes from one load,
    /// the rest (and every error) through the plain decoder.
    #[inline(always)]
    fn v_long(&mut self) -> Result<u64, E> {
        match fv(self.b, &mut self.p) {
            Some(x) => Ok(x),
            None => self.v_slow(),
        }
    }
    #[cold]
    #[inline(never)]
    fn v_slow(&mut self) -> Result<u64, E> {
        format::get_varint(self.b, &mut self.p, self.b.len()).map_err(verr)
    }
    #[inline(always)]
    fn byte(&mut self) -> Result<u8, E> {
        match self.b.get(self.p) {
            Some(&x) => {
                self.p += 1;
                Ok(x)
            }
            None => Err((Class::Truncated, "the record runs past the end".into())),
        }
    }
    fn boolean(&mut self) -> Result<bool, E> {
        match self.byte()? {
            0 => Ok(false),
            1 => Ok(true),
            x => Err((Class::Bool, format!("bool byte {x}"))),
        }
    }
    fn enm(&mut self, max: u8, what: &str) -> Result<u8, E> {
        let x = self.byte()?;
        if x > max {
            return Err((Class::Enum, format!("{what} {x} out of range")));
        }
        Ok(x)
    }
    fn bytes(&mut self) -> Result<&'a [u8], E> {
        let n = self.v()?;
        if n > self.left() as u64 {
            return Err((Class::Truncated, "bytes run past the end".into()));
        }
        let s = &self.b[self.p..self.p + n as usize];
        self.p += n as usize;
        Ok(s)
    }
    fn string(&mut self) -> Result<&'a str, E> {
        let s = self.bytes()?;
        std::str::from_utf8(s)
            .map_err(|_| (Class::Utf8, "a string is not well-formed UTF-8".into()))
    }
    fn nat(&mut self) -> Result<&'a [u8], E> {
        let s = self.bytes()?;
        if s.last() == Some(&0) {
            return Err((Class::NatNonMinimal, "a nat ends in a zero byte".into()));
        }
        Ok(s)
    }
    /// A list of ids each checked by `ok`.
    fn ids(&mut self, mut ok: impl FnMut(u64) -> Result<(), E>) -> Result<Ids<'a>, E> {
        let n = self.v()?;
        if n > self.left() as u64 {
            return Err((Class::Truncated, "a list runs past the end".into()));
        }
        let start = self.p;
        for _ in 0..n {
            let x = self.v()?;
            ok(x)?;
        }
        Ok(Ids {
            raw: &self.b[start..self.p],
            n,
            map: None,
        })
    }
    /// A count of parts; each part takes at least `min` bytes.
    fn count(&mut self, min: u64) -> Result<u64, E> {
        let n = self.v()?;
        if n.saturating_mul(min) > self.left() as u64 {
            return Err((Class::Truncated, "parts run past the end".into()));
        }
        Ok(n)
    }
}

/// A reader of MAIN's records: an iterator of events. Every record is
/// checked as it is read; after the last record the counts and the PROOFS
/// fill are checked.
pub struct Main<'a> {
    bytes: &'a [u8],
    p: usize,
    end: usize,
    start: u64,
    rec: u64,
    done: bool,
    counts: [u32; 4],
    trailer: u64,
    proofs: Option<Section>,
    st: State,
}

impl<'a> Main<'a> {
    /// What MAIN defined so far.
    pub fn state(&self) -> &State {
        &self.st
    }
    pub fn into_state(self) -> State {
        self.st
    }
    /// Absolute offset of the next record.
    pub fn position(&self) -> u64 {
        self.p as u64
    }
    /// Offset of MAIN.
    pub fn start(&self) -> u64 {
        self.start
    }

    #[inline(always)]
    fn name_id(&self, x: u64) -> Result<u32, E> {
        if x >= self.st.names as u64 {
            return Err((Class::NameId, format!("name {x} is not defined yet")));
        }
        Ok(x as u32)
    }
    #[inline(always)]
    fn level_id(&self, x: u64) -> Result<u32, E> {
        if x >= self.st.levels as u64 {
            return Err((Class::LevelId, format!("level {x} is not defined yet")));
        }
        Ok(x as u32)
    }
    #[inline(always)]
    fn back(&self, d: u64) -> Result<u32, E> {
        // d - 1 < exprs, with d = 0 wrapping to the top
        if d.wrapping_sub(1) >= self.st.exprs as u64 {
            return Err((
                Class::BackDistance,
                format!(
                    "back distance {d} with {} expressions defined",
                    self.st.exprs
                ),
            ));
        }
        Ok(self.st.exprs - d as u32)
    }

    fn new_name(&mut self, pre: u32, part: Component<'a>, off: u64) -> Result<u32, E> {
        if self.st.names == u32::MAX {
            return Err((Class::Counts, "more than 2^32 - 1 names".into()));
        }
        let cp = self.st.name_canon[pre as usize];
        let c = match part {
            Component::Str(s) => {
                // the name table keeps a component's length in a u32
                if s.len() as u64 >= crate::canon::MAX_COMPONENT {
                    return Err((
                        Class::Limit,
                        format!(
                            "a name component of {} bytes: this reader takes fewer than {}",
                            s.len(),
                            crate::canon::MAX_COMPONENT
                        ),
                    ));
                }
                self.st.canon.str_id(self.bytes, cp, off, s.len() as u32)
            }
            Component::Num(k) => self.st.canon.num_id(cp, k),
        };
        if c as usize == self.st.canon_decl.len() {
            self.st.canon_decl.push(NONE);
        }
        self.st.name_canon.push(c);
        let id = self.st.names;
        self.st.names += 1;
        Ok(id)
    }

    // A declared name: unique (spec 5.2).
    fn declare(&mut self, name: u32) -> Result<(), E> {
        let c = self.st.name_canon[name as usize] as usize;
        if c == crate::canon::ANON as usize {
            return Err((
                Class::AnonymousName,
                "a declaration declares the anonymous name".into(),
            ));
        }
        let d = self.st.canon_decl[c];
        if d != NONE {
            let s = self.st.canon.display(self.bytes, c as u32);
            return Err((
                Class::DuplicateName,
                if d == self.st.decls {
                    format!("{s} is declared twice in this record")
                } else {
                    format!("{s} is already declared by declaration {d}")
                },
            ));
        }
        self.st.canon_decl[c] = self.st.decls;
        Ok(())
    }

    fn head(&mut self, c: &mut Cur<'a>) -> Result<Head<'a>, E> {
        let name = self.name_id(c.v()?)?;
        self.declare(name)?;
        let names = self.st.names as u64;
        let params = c.ids(|x| {
            if x < names {
                Ok(())
            } else {
                Err((Class::NameId, format!("name {x} is not defined yet")))
            }
        })?;
        let ty = self.back(c.v()?)?;
        Ok(Head { name, params, ty })
    }

    fn names(&self, c: &mut Cur<'a>) -> Result<Ids<'a>, E> {
        let names = self.st.names as u64;
        c.ids(|x| {
            if x < names {
                Ok(())
            } else {
                Err((Class::NameId, format!("name {x} is not defined yet")))
            }
        })
    }

    /// A name record after its tag (1 or 2): its id, prefix and component.
    #[inline(always)]
    fn name_rec(&mut self, tag: u8, c: &mut Cur<'a>) -> Result<(u32, u32, Component<'a>), E> {
        let pre = self.name_id(c.v()?)?;
        let (part, off) = if tag == 1 {
            let s = c.string()?;
            (Component::Str(s), (c.p - s.len()) as u64)
        } else {
            (Component::Num(c.v()?), 0)
        };
        let id = self.new_name(pre, part, off)?;
        Ok((id, pre, part))
    }

    /// A level record after its tag (3 to 6).
    #[inline(always)]
    fn level_rec(&mut self, tag: u8, c: &mut Cur<'a>) -> Result<(u32, Level), E> {
        let level = match tag {
            3 => Level::Succ(self.level_id(c.v()?)?),
            4 => Level::Max(self.level_id(c.v()?)?, self.level_id(c.v()?)?),
            5 => Level::IMax(self.level_id(c.v()?)?, self.level_id(c.v()?)?),
            _ => Level::Param(self.name_id(c.v()?)?),
        };
        if self.st.levels == u32::MAX {
            return Err((Class::Counts, "more than 2^32 - 1 levels".into()));
        }
        let id = self.st.levels;
        self.st.levels += 1;
        Ok((id, level))
    }

    /// An expression record after its tag (7 to 16).
    #[inline(always)]
    fn expr_rec(&mut self, tag: u8, c: &mut Cur<'a>) -> Result<(u32, Expr<'a>), E> {
        let expr = match tag {
            10 => Expr::App(Ref::Main(self.back(c.v()?)?), Ref::Main(self.back(c.v()?)?)),
            7 => Expr::BVar(c.v()?),
            8 => Expr::Sort(self.level_id(c.v()?)?),
            9 => {
                let n = self.name_id(c.v()?)?;
                let levels = self.st.levels as u64;
                let us = c.ids(|x| {
                    if x < levels {
                        Ok(())
                    } else {
                        Err((Class::LevelId, format!("level {x} is not defined yet")))
                    }
                })?;
                Expr::Const(n, us)
            }
            11 | 12 => {
                let bi = c.enm(3, "binder")?;
                let n = self.name_id(c.v()?)?;
                let t = Ref::Main(self.back(c.v()?)?);
                let b = Ref::Main(self.back(c.v()?)?);
                if tag == 11 {
                    Expr::Lam(bi, n, t, b)
                } else {
                    Expr::Pi(bi, n, t, b)
                }
            }
            13 => {
                let n = self.name_id(c.v()?)?;
                let t = Ref::Main(self.back(c.v()?)?);
                let v = Ref::Main(self.back(c.v()?)?);
                let b = Ref::Main(self.back(c.v()?)?);
                Expr::Let(n, t, v, b)
            }
            14 => Expr::Nat(c.nat()?),
            15 => Expr::Str(c.string()?),
            _ => {
                let n = self.name_id(c.v()?)?;
                let i = c.v()?;
                Expr::Proj(n, i, Ref::Main(self.back(c.v()?)?))
            }
        };
        if self.st.exprs == u32::MAX {
            return Err((Class::Counts, "more than 2^32 - 1 expressions".into()));
        }
        let id = self.st.exprs;
        self.st.exprs += 1;
        Ok((id, expr))
    }

    /// A frontier record after its tag (19): kind, entry index, item.
    fn frontier_rec(&mut self, c: &mut Cur<'a>) -> Result<(u8, u32, u32), E> {
        let kind = c.enm(2, "frontier kind")?;
        let d = c.v()?;
        let next = self.st.next(kind) as u64;
        if d == 0 || d > next {
            return Err((
                Class::FrontierBack,
                format!("frontier back distance {d} with {next} items defined"),
            ));
        }
        let item = (next - d) as u32;
        let bits = &mut self.st.listed[kind as usize];
        let (w, b) = ((item / 64) as usize, item % 64);
        if bits.len() <= w {
            bits.resize(w + 1, 0);
        }
        if bits[w] >> b & 1 != 0 {
            return Err((
                Class::FrontierDuplicate,
                format!("item {item} is already in the frontier"),
            ));
        }
        bits[w] |= 1 << b;
        let t = &mut self.st.frontier[kind as usize];
        let index = t.len() as u32;
        t.push(item);
        Ok((kind, index, item))
    }

    /// A declaration record after its tag (18): its index and declaration.
    fn decl_rec(&mut self, c: &mut Cur<'a>) -> Result<(u32, Decl<'a>), E> {
        let index = self.st.decls;
        if index == u32::MAX {
            return Err((Class::Counts, "more than 2^32 - 1 declarations".into()));
        }
        let decl = self.decl(c)?;
        self.st.decls += 1;
        Ok((index, decl))
    }

    #[cold]
    fn bad_tag(t: u8) -> E {
        if t == 17 {
            (Class::Tag, "tag 17 is reserved".into())
        } else {
            (Class::Tag, format!("unknown tag {t}"))
        }
    }

    fn record(&mut self, c: &mut Cur<'a>) -> Result<Event<'a>, E> {
        let at = c.p as u64;
        let tag = c.byte()?;
        match tag {
            1 | 2 => {
                let (id, prefix, part) = self.name_rec(tag, c)?;
                Ok(Event::Name { id, prefix, part })
            }
            3..=6 => {
                let (id, level) = self.level_rec(tag, c)?;
                Ok(Event::Level { id, level })
            }
            7..=16 => {
                let (id, expr) = self.expr_rec(tag, c)?;
                Ok(Event::Expr { id, expr })
            }
            18 => {
                let (index, decl) = self.decl_rec(c)?;
                Ok(Event::Decl {
                    index,
                    offset: at,
                    decl,
                })
            }
            19 => {
                let (kind, index, item) = self.frontier_rec(c)?;
                Ok(Event::Frontier { kind, index, item })
            }
            t => Err(Self::bad_tag(t)),
        }
    }

    fn decl(&mut self, c: &mut Cur<'a>) -> Result<Decl<'a>, E> {
        let kind = c.enm(6, "declaration kind")?;
        Ok(match kind {
            0 => {
                let head = self.head(c)?;
                Decl::Axiom {
                    head,
                    is_unsafe: c.boolean()?,
                }
            }
            1 => {
                let head = self.head(c)?;
                let value = self.back(c.v()?)?;
                let hints = match c.enm(2, "hints")? {
                    0 => Hints::Opaque,
                    1 => Hints::Abbrev,
                    _ => Hints::Regular(c.v()?),
                };
                let safety = c.enm(2, "safety")?;
                let all = self.names(c)?;
                Decl::Defn {
                    head,
                    value,
                    hints,
                    safety,
                    all,
                }
            }
            2 => {
                let head = self.head(c)?;
                let value = self.back(c.v()?)?;
                let all = self.names(c)?;
                Decl::Thm { head, value, all }
            }
            3 => {
                let head = self.head(c)?;
                let value = self.back(c.v()?)?;
                let is_unsafe = c.boolean()?;
                let all = self.names(c)?;
                Decl::Opaque {
                    head,
                    value,
                    is_unsafe,
                    all,
                }
            }
            4 => {
                let head = self.head(c)?;
                Decl::Quot {
                    head,
                    kind: c.enm(3, "quotient kind")?,
                }
            }
            5 => {
                let nt = c.count(10)?;
                let mut types = Vec::with_capacity(nt as usize);
                for _ in 0..nt {
                    let head = self.head(c)?;
                    let is_unsafe = c.boolean()?;
                    let num_params = c.v()?;
                    let num_indices = c.v()?;
                    let all = self.names(c)?;
                    let ctors = self.names(c)?;
                    let num_nested = c.v()?;
                    let is_rec = c.boolean()?;
                    let is_reflexive = c.boolean()?;
                    types.push(IndType {
                        head,
                        is_unsafe,
                        num_params,
                        num_indices,
                        all,
                        ctors,
                        num_nested,
                        is_rec,
                        is_reflexive,
                    });
                }
                let nc = c.count(8)?;
                let mut ctors = Vec::with_capacity(nc as usize);
                for _ in 0..nc {
                    let head = self.head(c)?;
                    let is_unsafe = c.boolean()?;
                    let induct = self.name_id(c.v()?)?;
                    let cidx = c.v()?;
                    let num_params = c.v()?;
                    let num_fields = c.v()?;
                    ctors.push(Ctor {
                        head,
                        is_unsafe,
                        induct,
                        cidx,
                        num_params,
                        num_fields,
                    });
                }
                let nr = c.count(12)?;
                let mut recs = Vec::with_capacity(nr as usize);
                for _ in 0..nr {
                    let head = self.head(c)?;
                    let is_unsafe = c.boolean()?;
                    let all = self.names(c)?;
                    let num_params = c.v()?;
                    let num_indices = c.v()?;
                    let num_motives = c.v()?;
                    let num_minors = c.v()?;
                    let nrules = c.count(3)?;
                    let mut rules = Vec::with_capacity(nrules as usize);
                    for _ in 0..nrules {
                        let ctor = self.name_id(c.v()?)?;
                        let nfields = c.v()?;
                        let rhs = self.back(c.v()?)?;
                        rules.push(Rule { ctor, nfields, rhs });
                    }
                    let k = c.boolean()?;
                    recs.push(Rec {
                        head,
                        is_unsafe,
                        all,
                        num_params,
                        num_indices,
                        num_motives,
                        num_minors,
                        rules,
                        k,
                    });
                }
                Decl::Inductive(Box::new(Inductive { types, ctors, recs }))
            }
            _ => {
                let head = self.head(c)?;
                let length = c.v()?;
                let exprs = c.v()?;
                if exprs == 0 || exprs > length / 2 {
                    return Err((
                        Class::BlockExprs,
                        format!("block of {length} bytes cannot hold {exprs} expressions"),
                    ));
                }
                // block expressions are numbered by a u32 like every other
                // kind (spec 7.1), decided here, before any block is read
                if exprs > MAX_BLOCK_EXPRS {
                    return Err((
                        Class::BlockExprs,
                        format!("block of {exprs} expressions: at most 2^32 - 1"),
                    ));
                }
                let plen = self.proofs.map(|s| s.length).unwrap_or(0);
                let used = self.st.proofs_used;
                if length > plen - used {
                    return Err((
                        Class::ProofsFill,
                        format!(
                            "block of {length} bytes runs past PROOFS ({} bytes left)",
                            plen - used
                        ),
                    ));
                }
                let block = BlockRef {
                    decl: self.st.decls,
                    name: head.name,
                    offset: self.proofs.map(|s| s.offset).unwrap_or(0) + used,
                    length,
                    exprs,
                    frontier: [
                        self.st.frontier[0].len() as u32,
                        self.st.frontier[1].len() as u32,
                        self.st.frontier[2].len() as u32,
                    ],
                };
                self.st.proofs_used = used + length;
                self.st.blocks.push(block);
                let all = self.names(c)?;
                Decl::ThmBlock { head, block, all }
            }
        })
    }

    fn finish(&self) -> Result<(), Failure> {
        let defined = [self.st.names, self.st.levels, self.st.exprs, self.st.decls];
        const WHAT: [&str; 4] = ["names", "levels", "MAIN expressions", "declarations"];
        for k in 0..4 {
            if defined[k] != self.counts[k] {
                return Err(Failure::new(
                    Class::Counts,
                    Place::Trailer,
                    self.trailer + 4 * k as u64,
                    0,
                    format!(
                        "the trailer counts {} {}, MAIN defines {}",
                        self.counts[k], WHAT[k], defined[k]
                    ),
                ));
            }
        }
        if let Some(s) = self.proofs {
            if self.st.blocks.is_empty() {
                return Err(Failure::new(
                    Class::ProofsFill,
                    Place::Section(format::SEC_PROOFS),
                    s.offset,
                    0,
                    "PROOFS without a block",
                ));
            }
            if self.st.proofs_used != s.length {
                return Err(Failure::new(
                    Class::ProofsFill,
                    Place::Section(format::SEC_PROOFS),
                    s.offset + self.st.proofs_used,
                    0,
                    format!(
                        "the blocks fill {} of {} bytes",
                        self.st.proofs_used, s.length
                    ),
                ));
            }
        }
        Ok(())
    }
}

impl<'a> Iterator for Main<'a> {
    type Item = Result<Event<'a>, Failure>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }
        if self.p >= self.end {
            self.done = true;
            return self.finish().err().map(Err);
        }
        let at = self.p;
        self.rec += 1;
        let mut c = Cur {
            b: &self.bytes[..self.end],
            p: self.p,
        };
        match self.record(&mut c) {
            Ok(ev) => {
                self.p = c.p;
                Some(Ok(ev))
            }
            Err((class, msg)) => {
                self.done = true;
                Some(Err(Failure::new(
                    class,
                    Place::Section(format::SEC_MAIN),
                    at as u64,
                    self.rec,
                    msg,
                )))
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Proof blocks

/// A reader of one proof block: an iterator of its expressions (with their
/// index in the block). Names and levels come out as ids, expression
/// references as MAIN ids or block indices. Needs the MAIN state from at
/// least the theorem's record on.
pub struct Block<'a> {
    bytes: &'a [u8],
    st: &'a State,
    b: BlockRef,
    p: usize,
    end: usize,
    k: u64,
    done: bool,
    rule_p: bool,
    /// The frontier entries the block may use, per kind.
    fnames: &'a [u32],
    flevels: &'a [u32],
    fexprs: &'a [u32],
}

impl<'a> Block<'a> {
    pub fn new(bytes: &'a [u8], st: &'a State, b: BlockRef) -> Block<'a> {
        let f = |k: usize| {
            let t = &st.frontier[k][..];
            &t[..(b.frontier[k] as usize).min(t.len())]
        };
        Block {
            fnames: f(0),
            flevels: f(1),
            fexprs: f(2),
            bytes,
            st,
            b,
            p: b.offset as usize,
            end: (b.offset + b.length) as usize,
            k: 0,
            done: false,
            rule_p: true,
        }
    }

    /// The same reader without rule P, for tools that only convert the
    /// representation (unpacking). Rule P is a declaration failure, not a
    /// structural error, so such a block is still well-formed.
    pub fn without_rule_p(mut self) -> Block<'a> {
        self.rule_p = false;
        self
    }

    fn fail(&self, class: Class, at: u64, rec: u64, msg: String) -> Failure {
        let mut f = Failure::new(class, Place::Section(format::SEC_PROOFS), at, rec, msg);
        f.decl = Some(self.b.decl);
        f.theorem = Some(self.st.name_display(self.bytes, self.b.name));
        f
    }

    #[inline(always)]
    fn fname(&self, x: u64) -> Result<u32, E> {
        match usize::try_from(x).ok().and_then(|i| self.fnames.get(i)) {
            Some(&n) => Ok(n),
            None => Err(Self::unlisted("name", x)),
        }
    }
    #[cold]
    fn unlisted(what: &str, x: u64) -> E {
        (
            Class::FrontierIndex,
            format!("frontier {what} {x} not listed before the declaration"),
        )
    }
    #[inline(always)]
    fn flevel(&self, x: u64) -> Result<u32, E> {
        match usize::try_from(x).ok().and_then(|i| self.flevels.get(i)) {
            Some(&n) => Ok(n),
            None => Err(Self::unlisted("level", x)),
        }
    }
    #[inline(always)]
    fn eref(&self, r: u64, k: u64) -> Result<Ref, E> {
        // r - 1 < k: an expression of this block (r = 0 wraps to the top)
        let d = r.wrapping_sub(1);
        if d < k {
            // k < block-exprs <= MAX_BLOCK_EXPRS, checked in the record
            return Ok(Ref::Block((k - r) as u32));
        }
        self.eref_frontier(r, k)
    }
    #[inline(always)]
    fn eref_frontier(&self, r: u64, k: u64) -> Result<Ref, E> {
        if r == 0 {
            return Err((Class::BackDistance, "reference 0".into()));
        }
        let f = r - k - 1;
        match usize::try_from(f).ok().and_then(|i| self.fexprs.get(i)) {
            Some(&e) => Ok(Ref::Main(e)),
            None => Err(Self::unlisted("expression", f)),
        }
    }
    // rule P (spec 6)
    fn placed(&self, name: u32) -> Result<(), E> {
        if !self.rule_p {
            return Ok(());
        }
        let c = self.st.name_canon[name as usize] as usize;
        let d = self.st.canon_decl[c];
        if d == NONE || d >= self.b.decl {
            let s = self.st.name_display(self.bytes, name);
            return Err((
                Class::RuleP,
                format!("{s} is not declared before the theorem"),
            ));
        }
        Ok(())
    }

    fn record(&self, c: &mut Cur<'a>) -> Result<Expr<'a>, E> {
        self.record_at(c, self.k)
    }

    #[inline(always)]
    fn record_at(&self, c: &mut Cur<'a>, k: u64) -> Result<Expr<'a>, E> {
        let tag = c.byte()?;
        Ok(match tag {
            7 => Expr::BVar(c.v()?),
            8 => Expr::Sort(self.flevel(c.v()?)?),
            9 => {
                let n = self.fname(c.v()?)?;
                self.placed(n)?;
                let lim = self.flevels.len() as u64;
                let mut us = c.ids(|x| {
                    if x < lim {
                        Ok(())
                    } else {
                        Err(Self::unlisted("level", x))
                    }
                })?;
                us.map = Some(self.flevels);
                Expr::Const(n, us)
            }
            10 => {
                let f = self.eref(c.v()?, k)?;
                Expr::App(f, self.eref(c.v()?, k)?)
            }
            11 | 12 => {
                let bi = c.enm(3, "binder")?;
                let n = self.fname(c.v()?)?;
                let t = self.eref(c.v()?, k)?;
                let b = self.eref(c.v()?, k)?;
                if tag == 11 {
                    Expr::Lam(bi, n, t, b)
                } else {
                    Expr::Pi(bi, n, t, b)
                }
            }
            13 => {
                let n = self.fname(c.v()?)?;
                let t = self.eref(c.v()?, k)?;
                let v = self.eref(c.v()?, k)?;
                Expr::Let(n, t, v, self.eref(c.v()?, k)?)
            }
            14 => Expr::Nat(c.nat()?),
            15 => Expr::Str(c.string()?),
            16 => {
                let n = self.fname(c.v()?)?;
                self.placed(n)?;
                let i = c.v()?;
                Expr::Proj(n, i, self.eref(c.v()?, k)?)
            }
            t => return Err((Class::Tag, format!("tag {t} in a proof block"))),
        })
    }
}

impl<'a> Iterator for Block<'a> {
    type Item = Result<(u32, Expr<'a>), Failure>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }
        if self.k == self.b.exprs {
            self.done = true;
            if self.p != self.end {
                return Some(Err(self.fail(
                    Class::BlockCount,
                    self.p as u64,
                    self.k + 1,
                    format!("bytes left after {} expressions", self.b.exprs),
                )));
            }
            return None;
        }
        let at = self.p;
        if at >= self.end {
            self.done = true;
            return Some(Err(self.fail(
                Class::BlockCount,
                at as u64,
                self.k + 1,
                format!(
                    "the block ends after {} of {} expressions",
                    self.k, self.b.exprs
                ),
            )));
        }
        let mut c = Cur {
            b: &self.bytes[..self.end],
            p: self.p,
        };
        match self.record(&mut c) {
            Ok(e) => {
                self.p = c.p;
                // k < block-exprs <= MAX_BLOCK_EXPRS, checked in the record
                let k = self.k as u32;
                self.k += 1;
                Some(Ok((k, e)))
            }
            Err((class, msg)) => {
                self.done = true;
                Some(Err(self.fail(class, at as u64, self.k + 1, msg)))
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Single-pass decoding

/// What a caller does with the records of a single-pass [`decode`]. Every
/// method is called only after its record passed every check up to that
/// point, so the caller does not need to check anything the format promises.
/// The defaults do nothing. An error from the caller stops the pass.
pub trait Visit<'a> {
    type Error;
    /// A name record (`id` from 1; 0 is the anonymous name).
    fn name(&mut self, id: u32, prefix: u32, part: Component<'a>) -> Result<(), Self::Error> {
        let _ = (id, prefix, part);
        Ok(())
    }
    /// A level record (`id` from 1; 0 is the zero level).
    fn level(&mut self, id: u32, level: Level) -> Result<(), Self::Error> {
        let _ = (id, level);
        Ok(())
    }
    /// A MAIN expression.
    fn expr(&mut self, id: u32, expr: &Expr<'a>) -> Result<(), Self::Error> {
        let _ = (id, expr);
        Ok(())
    }
    /// A frontier entry: `kind` 0 name, 1 level, 2 expression.
    fn frontier(&mut self, kind: u8, index: u32, item: u32) -> Result<(), Self::Error> {
        let _ = (kind, index, item);
        Ok(())
    }
    /// A theorem with a proof block was read, before its [`Visit::decl`].
    /// `true` decodes the block now: its expressions go to
    /// [`Visit::block_expr`], then the declaration follows. `false` leaves the
    /// block for later, through [`decode_block`].
    fn open_block(&mut self, block: &BlockRef) -> bool {
        let _ = block;
        true
    }
    /// The `k`-th expression of the block being decoded (from 0). The last
    /// one is the theorem's value.
    fn block_expr(&mut self, k: u32, expr: &Expr<'_>) -> Result<(), Self::Error> {
        let _ = (k, expr);
        Ok(())
    }
    /// A declaration record. `offset` is the absolute offset of its tag byte.
    fn decl(&mut self, index: u32, offset: u64, decl: &Decl<'a>) -> Result<(), Self::Error> {
        let _ = (index, offset, decl);
        Ok(())
    }
}

/// Why a [`decode`] stopped.
#[derive(Debug)]
pub enum Stop<E> {
    /// The file failed a check: rejected or declined, see [`Failure::outcome`].
    File(Failure),
    /// The caller stopped the pass.
    Visitor(E),
}

/// The end of a [`decode`] that ran to the end of MAIN.
pub struct Decoded {
    /// What MAIN defined: the frontier tables and names needed to decode
    /// the blocks left for later.
    pub state: State,
    /// What the file holds. `block_exprs` counts the expressions every
    /// block declares, decoded or not.
    pub summary: Summary,
    /// Blocks left for later ([`Visit::open_block`] said no). They are not
    /// checked yet: a reader says the file is accepted only once each of
    /// them is decoded without an error.
    pub unread: u64,
}

impl Failure {
    /// The outcome this failure gives: declined for a decline, rejected
    /// otherwise.
    pub fn outcome(self) -> Outcome {
        Outcome::of(self)
    }
}

/// Decodes a file in one pass, every check inline. MAIN's records go to the
/// visitor in file order, and each proof block the visitor opens is decoded
/// at its theorem's record, before the declaration itself.
///
/// The reported failure is the one [`verify`] reports (spec section 8): a
/// structural error in MAIN, the trailer counts or the PROOFS fill comes
/// before any error inside a block. So after an error inside a block the
/// pass stops calling the visitor, but still checks the rest of MAIN, and
/// reports the block's error only if MAIN has none. A visitor that stopped
/// early must expect events up to the failing record of a block.
///
/// ```no_run
/// use susz::read::{decode, Expr, File, Visit};
///
/// struct Count(u64);
///
/// impl<'a> Visit<'a> for Count {
///     type Error = ();
///     fn expr(&mut self, _id: u32, _e: &Expr<'a>) -> Result<(), ()> {
///         self.0 += 1;
///         Ok(())
///     }
///     fn block_expr(&mut self, _k: u32, _e: &Expr<'_>) -> Result<(), ()> {
///         self.0 += 1;
///         Ok(())
///     }
/// }
///
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// let bytes = std::fs::read("Init.susz")?;
/// let file = File::open(&bytes)?;
/// let mut count = Count(0);
/// match decode(&file, &mut count) {
///     Ok(_) => println!("{} expressions", count.0),
///     Err(e) => println!("{e:?}"),
/// }
/// # Ok(())
/// # }
/// ```
pub fn decode<'a, V: Visit<'a>>(file: &File<'a>, v: &mut V) -> Result<Decoded, Stop<V::Error>> {
    file.main().run(v)
}

/// Decodes one proof block with every check inline, calling `f` with each
/// expression's index in the block and the expression. `st` is the state
/// of a [`decode`] that has read at least the theorem's record.
pub fn decode_block<'a, E>(
    bytes: &'a [u8],
    st: &'a State,
    block: BlockRef,
    mut f: impl FnMut(u32, &Expr<'a>) -> Result<(), E>,
) -> Result<(), Stop<E>> {
    Block::new(bytes, st, block).run(&mut f)
}

impl<'a> Main<'a> {
    /// One record of [`decode`]: checked, then handed to the visitor when
    /// `live` (no block failed yet). The outer error is the record's own; the
    /// inner one a block's failure or the visitor's.
    #[inline(always)]
    fn step<V: Visit<'a>>(
        &mut self,
        c: &mut Cur<'a>,
        at: usize,
        v: &mut V,
        live: bool,
        sum: &mut Summary,
        unread: &mut u64,
    ) -> Result<Result<(), Stop<V::Error>>, E> {
        let tag = c.byte()?;
        let r = match tag {
            7..=16 => {
                let (id, expr) = self.expr_rec(tag, c)?;
                if !live {
                    return Ok(Ok(()));
                }
                v.expr(id, &expr)
            }
            1 | 2 => {
                let (id, prefix, part) = self.name_rec(tag, c)?;
                if !live {
                    return Ok(Ok(()));
                }
                v.name(id, prefix, part)
            }
            3..=6 => {
                let (id, level) = self.level_rec(tag, c)?;
                if !live {
                    return Ok(Ok(()));
                }
                v.level(id, level)
            }
            19 => {
                let (kind, index, item) = self.frontier_rec(c)?;
                if !live {
                    return Ok(Ok(()));
                }
                v.frontier(kind, index, item)
            }
            18 => {
                let (index, decl) = self.decl_rec(c)?;
                if !live {
                    return Ok(Ok(()));
                }
                return Ok(self.visit_decl(v, index, at as u64, &decl, sum, unread));
            }
            t => return Err(Self::bad_tag(t)),
        };
        Ok(r.map_err(Stop::Visitor))
    }

    #[inline(never)]
    fn visit_decl<V: Visit<'a>>(
        &self,
        v: &mut V,
        index: u32,
        offset: u64,
        decl: &Decl<'a>,
        sum: &mut Summary,
        unread: &mut u64,
    ) -> Result<(), Stop<V::Error>> {
        if let Decl::ThmBlock { block, .. } = decl {
            sum.blocks += 1;
            sum.block_exprs += block.exprs;
            if v.open_block(block) {
                Block::new(self.bytes, &self.st, *block)
                    .run(&mut |k, e: &Expr<'_>| v.block_expr(k, e))?;
            } else {
                *unread += 1;
            }
        }
        v.decl(index, offset, decl).map_err(Stop::Visitor)
    }

    /// A MAIN expression id from a back distance, for the fast path.
    #[inline(always)]
    fn fback(&self, d: u64) -> Option<Ref> {
        let n = self.st.exprs as u64;
        if d.wrapping_sub(1) < n {
            Some(Ref::Main((n - d) as u32))
        } else {
            None
        }
    }

    /// The fast path of one MAIN expression record at `at` (see [`fv`]):
    /// the expression and where the record ends.
    #[inline(always)]
    fn fast_expr(&self, at: usize) -> Option<(Expr<'a>, usize)> {
        let win: &[u8; WIN] = self.bytes.get(at..at + WIN)?.try_into().unwrap();
        let mut o = 1;
        let e = match win[0] {
            10 => {
                let f = self.fback(fw(win, &mut o)?)?;
                Expr::App(f, self.fback(fw(win, &mut o)?)?)
            }
            tag @ (11 | 12) => {
                let bi = win[1];
                if bi > 3 {
                    return None;
                }
                o = 2;
                let n = fw(win, &mut o)?;
                if n >= self.st.names as u64 {
                    return None;
                }
                let t = self.fback(fw(win, &mut o)?)?;
                let body = self.fback(fw(win, &mut o)?)?;
                if tag == 11 {
                    Expr::Lam(bi, n as u32, t, body)
                } else {
                    Expr::Pi(bi, n as u32, t, body)
                }
            }
            9 => {
                let n = fw(win, &mut o)?;
                if n >= self.st.names as u64 {
                    return None;
                }
                // at most 5 levels: the record stays within the window
                let k = fw(win, &mut o)?;
                if k > 5 {
                    return None;
                }
                let start = o;
                let levels = self.st.levels as u64;
                for _ in 0..k {
                    if fw(win, &mut o)? >= levels {
                        return None;
                    }
                }
                if at + o > self.end {
                    return None;
                }
                Expr::Const(
                    n as u32,
                    Ids {
                        raw: &self.bytes[at + start..at + o],
                        n: k,
                        map: None,
                    },
                )
            }
            8 => {
                let l = fw(win, &mut o)?;
                if l >= self.st.levels as u64 {
                    return None;
                }
                Expr::Sort(l as u32)
            }
            7 => Expr::BVar(fw(win, &mut o)?),
            _ => return None,
        };
        if at + o > self.end || self.st.exprs == u32::MAX {
            return None;
        }
        Some((e, at + o))
    }

    fn run<V: Visit<'a>>(mut self, v: &mut V) -> Result<Decoded, Stop<V::Error>> {
        let mut c = Cur {
            b: &self.bytes[..self.end],
            p: self.p,
        };
        let mut sum = Summary {
            counts: self.counts,
            ..Default::default()
        };
        let mut unread = 0;
        // the first error inside a block, reported after MAIN is checked
        let mut late: Option<Failure> = None;
        while c.p < c.b.len() {
            let at = c.p;
            self.rec += 1;
            if let Some((e, q)) = self.fast_expr(at) {
                let id = self.st.exprs;
                self.st.exprs += 1;
                c.p = q;
                if late.is_none() {
                    v.expr(id, &e).map_err(Stop::Visitor)?;
                }
                continue;
            }
            match self.step(&mut c, at, v, late.is_none(), &mut sum, &mut unread) {
                Ok(Ok(())) => {}
                Ok(Err(Stop::File(f))) => late = Some(f),
                Ok(Err(Stop::Visitor(e))) => return Err(Stop::Visitor(e)),
                Err((class, msg)) => {
                    return Err(Stop::File(Failure::new(
                        class,
                        Place::Section(format::SEC_MAIN),
                        at as u64,
                        self.rec,
                        msg,
                    )))
                }
            }
        }
        self.p = c.p;
        self.finish().map_err(Stop::File)?;
        if let Some(f) = late {
            return Err(Stop::File(f));
        }
        sum.frontier = [
            self.st.frontier[0].len() as u64,
            self.st.frontier[1].len() as u64,
            self.st.frontier[2].len() as u64,
        ];
        Ok(Decoded {
            state: self.st,
            summary: sum,
            unread,
        })
    }
}

impl<'a> Block<'a> {
    /// The whole block through `f`, with the same checks and failures as
    /// the iterator.
    /// An expression reference, for the fast path.
    #[inline(always)]
    fn fref(&self, r: u64, k: u64) -> Option<Ref> {
        let d = r.wrapping_sub(1);
        if d < k {
            return Some(Ref::Block((k - r) as u32));
        }
        // r >= 1 and r - 1 >= k here unless r = 0
        if r == 0 {
            return None;
        }
        let f = usize::try_from(r - k - 1).ok()?;
        self.fexprs.get(f).map(|&e| Ref::Main(e))
    }

    /// The fast path of the `k`-th record at `at` (see [`fv`]): the
    /// expression and where the record ends.
    #[inline(always)]
    fn fast(&self, at: usize, k: u64) -> Option<(Expr<'a>, usize)> {
        let win: &[u8; WIN] = self.bytes.get(at..at + WIN)?.try_into().unwrap();
        let mut o = 1;
        let e = match win[0] {
            10 => {
                let f = self.fref(fw(win, &mut o)?, k)?;
                Expr::App(f, self.fref(fw(win, &mut o)?, k)?)
            }
            tag @ (11 | 12) => {
                let bi = win[1];
                if bi > 3 {
                    return None;
                }
                o = 2;
                let n = *self.fnames.get(usize::try_from(fw(win, &mut o)?).ok()?)?;
                let t = self.fref(fw(win, &mut o)?, k)?;
                let body = self.fref(fw(win, &mut o)?, k)?;
                if tag == 11 {
                    Expr::Lam(bi, n, t, body)
                } else {
                    Expr::Pi(bi, n, t, body)
                }
            }
            13 => {
                let n = *self.fnames.get(usize::try_from(fw(win, &mut o)?).ok()?)?;
                let t = self.fref(fw(win, &mut o)?, k)?;
                let v = self.fref(fw(win, &mut o)?, k)?;
                Expr::Let(n, t, v, self.fref(fw(win, &mut o)?, k)?)
            }
            7 => Expr::BVar(fw(win, &mut o)?),
            _ => return None,
        };
        if at + o > self.end {
            return None;
        }
        Some((e, at + o))
    }

    fn run<E>(self, f: &mut impl FnMut(u32, &Expr<'a>) -> Result<(), E>) -> Result<(), Stop<E>> {
        let mut c = Cur {
            b: &self.bytes[..self.end],
            p: self.p,
        };
        let mut k = 0u64;
        while k < self.b.exprs {
            let at = c.p;
            if let Some((e, q)) = self.fast(at, k) {
                // k < block-exprs <= MAX_BLOCK_EXPRS, checked in the record
                f(k as u32, &e).map_err(Stop::Visitor)?;
                c.p = q;
                k += 1;
                continue;
            }
            if at >= self.end {
                return Err(Stop::File(self.fail(
                    Class::BlockCount,
                    at as u64,
                    k + 1,
                    format!("the block ends after {k} of {} expressions", self.b.exprs),
                )));
            }
            match self.record_at(&mut c, k) {
                // k < block-exprs <= MAX_BLOCK_EXPRS, checked in the record
                Ok(e) => f(k as u32, &e).map_err(Stop::Visitor)?,
                Err((class, msg)) => {
                    return Err(Stop::File(self.fail(class, at as u64, k + 1, msg)))
                }
            }
            k += 1;
        }
        if c.p != self.end {
            return Err(Stop::File(self.fail(
                Class::BlockCount,
                c.p as u64,
                k + 1,
                format!("bytes left after {} expressions", self.b.exprs),
            )));
        }
        Ok(())
    }
}

/// The full structural check of a file (spec section 10): framing, every MAIN
/// record, the counts and PROOFS fill, and every proof block. INDEX is not
/// read (its directory entry is checked). This is [`decode`] with a visitor
/// that only opens every block.
pub fn verify(bytes: &[u8]) -> Outcome {
    struct Check;
    impl Visit<'_> for Check {
        type Error = std::convert::Infallible;
    }
    let f = match File::open(bytes) {
        Ok(f) => f,
        Err(e) => return Outcome::of(e),
    };
    match decode(&f, &mut Check) {
        Ok(d) => Outcome::Accepted(d.summary),
        Err(Stop::File(e)) => Outcome::of(e),
        Err(Stop::Visitor(x)) => match x {},
    }
}

/// The check as two passes: all of MAIN through the iterator, then every
/// block in declaration order. Kept to show that [`verify`] gives the same
/// outcome and location.
#[doc(hidden)]
pub fn verify_two_pass(bytes: &[u8]) -> Outcome {
    let f = match File::open(bytes) {
        Ok(f) => f,
        Err(e) => return Outcome::of(e),
    };
    let mut m = f.main();
    for ev in &mut m {
        if let Err(e) = ev {
            return Outcome::of(e);
        }
    }
    let st = m.into_state();
    let mut sum = Summary {
        counts: f.counts,
        blocks: st.blocks.len() as u64,
        ..Default::default()
    };
    for &b in &st.blocks {
        for r in Block::new(bytes, &st, b) {
            if let Err(e) = r {
                return Outcome::of(e);
            }
        }
        sum.block_exprs += b.exprs;
    }
    sum.frontier = [
        st.frontier[0].len() as u64,
        st.frontier[1].len() as u64,
        st.frontier[2].len() as u64,
    ];
    Outcome::Accepted(sum)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vectors::{build, Vector, Want, BASE};

    fn outcome_with(exprs: u64, length: u64) -> Failure {
        let src = BASE.replace(
            "@d8 18 6 5 0 1 len:t cnt:t 1 5",
            &format!("@d8 18 6 5 0 1 {length} {exprs} 1 5"),
        );
        let v = Vector {
            name: "t".into(),
            src,
            want: Want::Accept,
        };
        match verify(&build(&v).bytes) {
            Outcome::Rejected(f) => f,
            o => panic!("{o:?}"),
        }
    }

    // block-exprs is limited to 2^32 - 1 (spec 7.1), decided from the
    // record before any block is read: 2^32 is a block-exprs error, 2^32 - 1
    // passes that check and fails only because the block is not there.
    #[test]
    fn block_exprs_u32_range() {
        let f = outcome_with(1 << 32, 1 << 33);
        assert_eq!(f.class, Class::BlockExprs);
        assert_eq!(f.place, Place::Section(format::SEC_MAIN));
        let f = outcome_with(MAX_BLOCK_EXPRS, 2 * MAX_BLOCK_EXPRS);
        assert_eq!(f.class, Class::ProofsFill);
        assert_eq!(f.place, Place::Section(format::SEC_MAIN));
    }
}
