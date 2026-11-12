//! The test vectors (spec section 12): accept, reject, decline and
//! bad-INDEX files written in the `asm` language. Every reject vector is a
//! minimal mutation of an accept vector, named after the rule it breaks;
//! its expected location comes from the assembler (a record marked `!`, or
//! a field of the layout), not from the reader.
//!
//! `cargo run --example gen-vectors` writes them to `tests/vectors/`;
//! `tests/vectors.rs` checks the committed files against this list and the
//! reader against the expectations.

use crate::asm::{assemble, Assembled};
use crate::format;
use crate::read::{self, Class, Outcome, Place};

/// The base vector: names, levels, every expression kind, every
/// declaration kind, a proof block naming frontier items of each kind, a
/// declaration after the theorem, INDEX and SOURCE. Its declarations
/// type-check in a real Lean kernel: `Ind` is a one-field structure with the
/// recursor Lean derives, `Eq` is there for the quotient package, and both
/// theorems prove an `Eq` (the block's proof reduces a projection).
pub const BASE: &str = r#"# Susz 1 test vector: the base every reject vector mutates.
section MAIN
19 0 1                  # frontier name 0: the anonymous name
19 1 1                  # frontier level 0: level zero
1 0 s:"Nat"             # name 1: Nat
19 0 1                  # frontier name 1: Nat
1 1 s:"zero"            # name 2: Nat.zero
2 1 7                   # name 3: Nat.7
1 0 s:"u"               # name 4: u
1 0 s:"T"               # name 5: T
19 0 1                  # frontier name 2: T
1 0 s:"Ind"             # name 6: Ind
19 0 1                  # frontier name 3: Ind
1 6 s:"mk"              # name 7: Ind.mk
19 0 1                  # frontier name 4: Ind.mk
1 6 s:"rec"             # name 8: Ind.rec
1 0 s:"u_1"             # name 9: u_1
1 0 s:"Eq"              # name 10: Eq
1 10 s:"refl"           # name 11: Eq.refl
19 0 1                  # frontier name 5: Eq.refl
1 0 s:"Quot"            # name 12: Quot
1 0 s:"String"          # name 13: String
19 0 1                  # frontier name 6: String
1 0 s:"L"               # name 14: L
1 0 s:"S"               # name 15: S
1 0 s:"Z"               # name 16: Z
19 0 1                  # frontier name 7: Z
3 0                     # level 1: succ zero
19 1 1                  # frontier level 1
6 4                     # level 2: param u
4 1 2                   # level 3: max 1 2
5 2 1                   # level 4: imax 2 1
6 9                     # level 5: param u_1
8 1                     # expr 0: Sort 1
19 2 1                  # frontier expr 0
9 1 0                   # expr 1: const Nat []
19 2 1                  # frontier expr 1
@d0 18 0 1 0 2 0        # decl 0: axiom Nat : expr 0
14 nat:0                # expr 2: 0
@d1 18 1 2 0 2 1 2 1 0 1 2      # decl 1: def Nat.zero : expr 1 := expr 2, regular 1, safe, all [2]
8 0                     # expr 3: Prop
7 0                     # expr 4: bvar 0
7 1                     # expr 5: bvar 1
7 2                     # expr 6: bvar 2
9 6 1 2                 # expr 7: const Ind [u]
9 7 1 2                 # expr 8: const Ind.mk [u]
12 0 0 8 2              # expr 9: forall (_ : Nat), Ind.{u}
8 5                     # expr 10: Sort u_1
12 0 0 4 1              # expr 11: forall (_ : Ind.{u}), Sort u_1
10 4 8                  # expr 12: app Ind.mk.{u} (bvar 0)
10 8 1                  # expr 13: app (bvar 1) expr 12
12 0 0 13 1             # expr 14: forall (_ : Nat), expr 13 (the minor premise)
10 9 11                 # expr 15: app (bvar 2) (bvar 0)
12 0 0 9 1              # expr 16: forall (_ : Ind.{u}), expr 15
12 0 0 3 1              # expr 17: forall (_ : expr 14), expr 16
12 1 0 7 1              # expr 18: forall {_ : expr 11}, expr 17 (the recursor's type)
10 14 15                # expr 19: app (bvar 1) (bvar 0)
11 0 0 19 1             # expr 20: fun (_ : Nat) => expr 19
11 0 0 7 1              # expr 21: fun (_ : expr 14) => expr 20
11 1 0 11 1             # expr 22: fun {_ : expr 11} => expr 21 (the rule's right side)
@d2 18 5 1 6 1 4 23 0 0 0 1 6 1 7 0 0 0 1 7 1 4 14 0 6 0 0 1 1 8 2 9 4 5 0 1 6 0 0 1 1 1 7 1 1 0   # decl 2: inductive Ind.{u} : Type, Ind.mk : Nat -> Ind, Ind.rec.{u_1, u}
8 2                     # expr 23: Sort u
12 0 0 19 21            # expr 24: forall (_ : bvar 1), Prop
12 0 0 21 1             # expr 25: forall (_ : bvar 0), expr 24
12 1 0 3 1              # expr 26: forall {_ : Sort u}, expr 25 (Eq's type)
9 10 1 2                # expr 27: const Eq [u]
10 1 23                 # expr 28: app expr 27 (bvar 1)
10 1 25                 # expr 29: app expr 28 (bvar 0)
10 1 26                 # expr 30: app expr 29 (bvar 0)
12 0 0 27 1             # expr 31: forall (_ : bvar 0), expr 30
12 1 0 9 1              # expr 32: forall {_ : Sort u}, expr 31 (Eq.refl's type)
@d3 18 5 1 10 1 4 7 0 2 1 1 10 1 11 0 0 0 1 11 1 4 1 0 10 0 2 0 0   # decl 3: inductive Eq.{u}, Eq.refl.{u}, no recursor
12 0 0 8 10             # expr 33: forall (_ : expr 25), Sort u
12 1 0 11 1             # expr 34: forall {_ : Sort u}, expr 33 (Quot's type)
@d4 18 4 12 1 4 1 0     # decl 4: quot Quot.{u} : expr 34, type
@d5 18 0 13 0 35 0      # decl 5: axiom String : expr 0
10 27 31                # expr 35: app Ind.mk.{u} (bvar 0)
13 0 35 34 1            # expr 36: let _ : Nat := 0; expr 35
@d6 18 3 14 1 4 30 1 0 1 14     # decl 6: opaque L.{u} : Ind.{u} := expr 36, all [L]
9 10 1 1                # expr 37: const Eq [level 1]
10 1 37                 # expr 38: app expr 37 Nat
9 2 0                   # expr 39: const Nat.zero []
10 2 1                  # expr 40: app expr 38 expr 39
10 1 39                 # expr 41: app expr 40 0
9 11 1 1                # expr 42: const Eq.refl [level 1]
10 1 42                 # expr 43: app expr 42 Nat
10 1 42                 # expr 44: app expr 43 0
@d7 18 2 15 0 4 1 1 15  # decl 7: theorem S : Nat.zero = 0 := Eq.refl 0 (in MAIN)
14 nat:256              # expr 45: 256
10 8 1                  # expr 46: app expr 38 256
10 1 2                  # expr 47: app expr 46 256
@d8 18 6 5 0 1 len:t cnt:t 1 5  # decl 8: theorem T : 256 = 256, proof in block t
15 s:"ok"               # expr 48: "ok"
8 3                     # expr 49: Sort (max 1 2)
8 4                     # expr 50: Sort (imax 2 1)
16 6 0 15               # expr 51: proj Ind 0 expr 36
@d9 18 0 16 0 52 1      # decl 9: unsafe axiom Z : expr 0
section PROOFS
block t decl=8
9 4 1 1                 # t0: const Ind.mk [level 1]
8 1                     # t1: Sort (level 1)
12 3 0 1 1              # t2: forall [_ : t1], t1
7 0                     # t3: bvar 0
11 3 0 5 1              # t4: fun [_ : expr 0] => t3
15 s:"a\0b\xf0\x9f\x8d\x8e"     # t5: NUL and a 4-byte character
9 6 0                   # t6: const String []
9 5 1 1                 # t7: const Eq.refl [level 1]
10 1 10                 # t8: app t7 expr 1
10 9 6                  # t9: app t0 t3
16 3 0 1                # t10: proj Ind 0 t9
10 3 1                  # t11: app t8 t10
11 2 7 14 1             # t12: fun {{Z : expr 1}} => t11
14 nat:256              # t13: 256
10 2 1                  # t14: app t12 t13
13 0 9 10 1             # t15: let _ : t6 := t5; t14
13 0 14 12 1            # t16: let _ : t2 := t4; t15 (the value)
section INDEX
10                      # decl-count
0 rel:MAIN:d0           # entry 0
1 rel:d0:d1             # entry 1
5 rel:d1:d2             # entry 2
5 rel:d2:d3             # entry 3
4 rel:d3:d4             # entry 4
0 rel:d4:d5             # entry 5
3 rel:d5:d6             # entry 6
2 rel:d6:d7             # entry 7
6 rel:d7:d8 len:t       # entry 8
0 rel:d8:d9             # entry 9
ntcount                 # name-count
nt L 6
nt S 7
nt T 8
nt Z 9
nt Eq 3
nt Eq.refl 3
nt Ind 2
nt Ind.mk 2
nt Ind.rec 2
nt Nat 0
nt Nat.zero 1
nt Quot 4
nt String 5
section SOURCE
x:7b2274657374223a747275657d    # {"test":true}
counts 17 6 52 10
"#;

const MINIMAL: &str = r#"# Susz 1 test vector: one axiom.
section MAIN
1 0 s:"A"               # name 1: A
8 0                     # expr 0: Prop
18 0 1 0 1 0            # decl 0: axiom A : Prop
counts 2 1 1 1
"#;

const MAIN_ONLY: &str = r#"# Susz 1 test vector: MAIN only (no PROOFS); varint, nat and string edges.
section MAIN
1 0 s:"A"               # name 1: A
2 1 18446744073709551615        # name 2: A.(2^64 - 1)
8 0                     # expr 0: Prop
18 0 1 0 1 0            # decl 0: axiom A : Prop
7 0                     # bvar 0
7 127                   # bvar 127
7 128                   # bvar 128
7 9223372036854775808   # bvar 2^63
7 18446744073709551615  # bvar 2^64 - 1
14 nat:0                # 0
14 nat:255              # 255
14 nat:256              # 256
14 nat:18446744073709551616     # 2^64
14 nat:1606938044258990275541962092341162602522202993782792835301376   # 2^200
15 s:"\0"               # NUL
15 s:"\xf4\x8f\xbf\xbf"         # U+10FFFF
counts 3 1 13 1
"#;

/// Where an expected error is, from the assembled layout.
#[derive(Debug, Clone, Copy)]
pub enum Exp {
    /// The record marked `!`.
    Marked,
    /// A header field.
    Header(u64),
    /// A trailer field, `k` bytes before the end of the file.
    FromEnd(u64),
    /// A trailer field `k` bytes after the trailer's start.
    Trailer(u64),
    /// Field `k` of directory entry `i` (from 0).
    Entry(usize, u64),
    /// The section-count field (no entry).
    DirCount,
    /// `k` bytes into a section.
    SectionAt(u16, u64),
    /// The end of a block (label, record number, theorem's declaration).
    BlockEnd(&'static str, u64, u32),
}

#[derive(Debug, Clone, Copy)]
pub enum Look {
    Found(u32),
    NotFound,
    Invalid,
}

#[derive(Debug, Clone)]
pub enum Want {
    Accept,
    Reject(Class, Exp),
    Decline(Class, Exp),
    /// A bad INDEX: accepted by a full check, index invalid, with lookups.
    BadIndex(Vec<(&'static str, Look)>),
}

pub struct Vector {
    pub name: String,
    pub src: String,
    pub want: Want,
}

impl Vector {
    pub fn dir(&self) -> &'static str {
        match self.want {
            Want::Accept => "accept",
            Want::Reject(..) => "reject",
            Want::Decline(..) => "decline",
            Want::BadIndex(_) => "index",
        }
    }
}

// Each pair replaces the one line holding `from` by `to` (or, when `from`
// spans lines, exactly that text).
fn mutate(base: &str, pairs: &[(&str, &str)]) -> String {
    let mut s = base.to_string();
    for (from, to) in pairs {
        assert_eq!(
            s.matches(from).count(),
            1,
            "mutation source not unique: {from}"
        );
        if from.contains('\n') {
            s = s.replacen(from, to, 1);
        } else {
            s = s
                .lines()
                .map(|l| {
                    if l.contains(from) {
                        to.to_string()
                    } else {
                        l.to_string()
                    }
                })
                .collect::<Vec<_>>()
                .join("\n")
                + "\n";
        }
    }
    s
}

fn header_note(s: &str, note: &str) -> String {
    let mut lines = s.splitn(2, '\n');
    let _ = lines.next();
    format!(
        "# Susz 1 test vector: {note}\n{}",
        lines.next().unwrap_or("")
    )
}

/// Every vector.
pub fn all() -> Vec<Vector> {
    use Class::*;
    use Exp::*;
    let mut v: Vec<Vector> = Vec::new();
    let mut add = |name: &str, src: String, want: Want| {
        v.push(Vector {
            name: name.into(),
            src,
            want,
        })
    };
    // accept
    add("minimal", MINIMAL.into(), Want::Accept);
    add("blocks", BASE.into(), Want::Accept);
    let noindex = {
        let a = BASE.find("section INDEX").unwrap();
        let b = BASE.find("section SOURCE").unwrap();
        format!("{}{}", &BASE[..a], &BASE[b..])
    };
    add(
        "blocks-no-index",
        header_note(&noindex, "the base without INDEX."),
        Want::Accept,
    );
    add("main-only", MAIN_ONLY.into(), Want::Accept);
    let unknown = BASE.replace(
        "counts 17 6 52 10",
        "section 77               # an unknown informational section\nx:0102ff\ncounts 17 6 52 10",
    );
    add(
        "unknown-informational",
        header_note(&unknown, "an unknown informational section is skipped."),
        Want::Accept,
    );
    let pad = BASE.replace("section SOURCE", "section PAD\nx:00000000\nsection SOURCE");
    add("pad", header_note(&pad, "a PAD section."), Want::Accept);

    // decline
    let m =
        |base: &str, note: &str, pairs: &[(&str, &str)]| header_note(&mutate(base, pairs), note);
    let hdr = |line: &str, note: &str| {
        header_note(
            &BASE.replacen("section MAIN", &format!("{line}\nsection MAIN"), 1),
            note,
        )
    };
    add(
        "major-2",
        hdr("header major=2", "major version 2."),
        Want::Decline(Major, Header(8)),
    );
    let must = BASE.replace(
        "counts 17 6 52 10",
        "section 77 flags=1      # an unknown must-understand section\nx:0102ff\ncounts 17 6 52 10",
    );
    add(
        "unknown-must-understand",
        header_note(&must, "an unknown must-understand section."),
        Want::Decline(MustUnderstand, Entry(4, 0)),
    );

    // reject: framing
    add(
        "magic",
        hdr("header magic=53555a5a0d0a1a0a", "bad magic."),
        Want::Reject(Magic, Header(0)),
    );
    add(
        "reserved-header-16",
        hdr("header r16=1", "reserved u16 of the header."),
        Want::Reject(Reserved, Header(10)),
    );
    add(
        "reserved-header-32",
        hdr("header r32=1", "reserved u32 of the header."),
        Want::Reject(Reserved, Header(12)),
    );
    add(
        "reserved-entry",
        m(
            BASE,
            "reserved field of a directory entry.",
            &[("section INDEX", "section INDEX res=1")],
        ),
        Want::Reject(Reserved, Entry(2, 4)),
    );
    add(
        "trailer-length",
        hdr("trailer tlen=100", "trailer length."),
        Want::Reject(TrailerLength, FromEnd(8)),
    );
    add(
        "trailer-section-count",
        hdr(
            "trailer nsec=3",
            "section count disagrees with the trailer length.",
        ),
        Want::Reject(TrailerLength, FromEnd(8)),
    );
    add(
        "end-magic",
        hdr("trailer endmagic=5a53555a", "end magic."),
        Want::Reject(EndMagic, FromEnd(4)),
    );
    add(
        "directory-overlap",
        m(
            BASE,
            "a section overlaps the one before.",
            &[("section INDEX", "section INDEX doff=-1")],
        ),
        Want::Reject(SectionTiling, Entry(2, 8)),
    );
    add(
        "directory-gap",
        m(
            BASE,
            "a gap between sections.",
            &[("section INDEX", "section INDEX doff=1")],
        ),
        Want::Reject(SectionTiling, Entry(2, 8)),
    );
    add(
        "directory-out-of-file",
        m(
            BASE,
            "a section runs past the trailer.",
            &[("section SOURCE", "section SOURCE dlen=1000")],
        ),
        Want::Reject(SectionTiling, Entry(3, 16)),
    );
    add(
        "directory-short",
        m(
            BASE,
            "the sections end before the trailer.",
            &[("section SOURCE", "section SOURCE dlen=-1")],
        ),
        Want::Reject(SectionTiling, Entry(3, 16)),
    );
    add(
        "directory-duplicate-id",
        m(
            BASE,
            "a section id given twice.",
            &[("section SOURCE", "section SOURCE id=5")],
        ),
        Want::Reject(SectionDuplicate, Entry(3, 0)),
    );
    add(
        "directory-flags-known",
        m(
            BASE,
            "INDEX with the must-understand flag.",
            &[("section INDEX", "section INDEX flags=1")],
        ),
        Want::Reject(SectionFlags, Entry(2, 2)),
    );
    add(
        "directory-flags-reserved",
        m(
            BASE,
            "a reserved flag bit.",
            &[("section SOURCE", "section SOURCE flags=2")],
        ),
        Want::Reject(SectionFlags, Entry(3, 2)),
    );
    add(
        "directory-no-main",
        "# Susz 1 test vector: no MAIN section.\nsection SOURCE\nx:7b7d\ncounts 1 1 0 0\n".into(),
        Want::Reject(SectionMissing, DirCount),
    );
    add(
        "counts-exprs",
        m(
            BASE,
            "the trailer counts one expression too many.",
            &[("counts 17 6 52 10", "counts 17 6 53 10")],
        ),
        Want::Reject(Counts, Trailer(8)),
    );
    add(
        "counts-decls",
        m(
            BASE,
            "the trailer counts one declaration too few.",
            &[("counts 17 6 52 10", "counts 17 6 52 9")],
        ),
        Want::Reject(Counts, Trailer(12)),
    );
    add(
        "pad-nonzero",
        header_note(
            &pad.replace("x:00000000", "x:00000100"),
            "a PAD byte is not zero.",
        ),
        Want::Reject(PadNonZero, SectionAt(format::SEC_PAD, 2)),
    );

    // reject: primitives
    let r = |name: &str, note: &str, from: &str, to: &str, class: Class| {
        (
            name.to_string(),
            m(BASE, note, &[(from, to)]),
            Want::Reject(class, Marked),
        )
    };
    let prims = vec![
        r("varint-nonminimal", "a varint with a trailing zero byte.", "1 1 s:\"zero\"", "! 1 v:1:2 s:\"zero\"", VarintNonMinimal),
        r("varint-11-bytes", "an 11-byte varint.", "7 0                     # expr 4", "! 7 x:ffffffffffffffffff8100   # expr 4", VarintOverflow),
        r("varint-10th-byte-2", "a 10th varint byte 0x02.", "7 0                     # expr 4", "! 7 x:ffffffffffffffffff02     # expr 4", VarintOverflow),
        r("varint-10th-byte-0", "a 10th varint byte 0x00.", "7 0                     # expr 4", "! 7 x:ffffffffffffffffff00     # expr 4", VarintNonMinimal),
        r("truncated-varint", "MAIN ends inside a varint.", "@d9 18 0 16 0 52 1      # decl 9: unsafe axiom Z : expr 0", "@d9 18 0 16 0 52 1\n! 7 x:80", Truncated),
        r("truncated-string", "MAIN ends inside a string.", "@d9 18 0 16 0 52 1      # decl 9: unsafe axiom Z : expr 0", "@d9 18 0 16 0 52 1\n! 15 x:05414243", Truncated),
        r("truncated-list", "MAIN ends inside a list.", "@d9 18 0 16 0 52 1      # decl 9: unsafe axiom Z : expr 0", "@d9 18 0 16 0 52 1\n! 9 1 x:0500", Truncated),
        r("utf8-overlong", "an overlong UTF-8 form.", "1 0 s:\"u\"", "! 1 0 s:\"\\xc1\\xb5\"", Utf8),
        r("utf8-surrogate", "a UTF-8 encoded surrogate.", "1 0 s:\"u\"", "! 1 0 s:\"\\xed\\xa0\\x80\"", Utf8),
        r("utf8-truncated", "a cut UTF-8 sequence.", "1 0 s:\"u\"", "! 1 0 s:\"\\xf0\\x9f\\x8d\"", Utf8),
        r("nat-nonminimal", "a nat with a trailing zero byte.", "14 nat:0                # expr 2", "! 14 natx:00            # expr 2", NatNonMinimal),
        r("bool-2", "a bool byte 2.", "@d0 18 0 1 0 2 0", "! @d0 18 0 1 0 2 2", Bool),
        r("enum-binder", "binder 4.", "11 0 0 19 1             # expr 20", "! 11 4 0 19 1           # expr 20", Enum),
        r("enum-decl-kind", "declaration kind 7.", "@d0 18 0 1 0 2 0", "! @d0 18 7 1 0 2 0", Enum),
        r("enum-hints", "hints 3.", "@d1 18 1 2 0 2 1 2 1 0 1 2", "! @d1 18 1 2 0 2 1 3 1 0 1 2", Enum),
        r("enum-safety", "safety 3.", "@d1 18 1 2 0 2 1 2 1 0 1 2", "! @d1 18 1 2 0 2 1 2 1 3 1 2", Enum),
        r("enum-quot-kind", "quotient kind 4.", "@d4 18 4 12 1 4 1 0", "! @d4 18 4 12 1 4 1 4", Enum),
        r("enum-frontier-kind", "frontier kind 3.", "19 0 1                  # frontier name 0", "! 19 3 1                # frontier name 0", Enum),
        r("tag-unknown", "an unknown tag in MAIN.", "7 0                     # expr 4", "! 20 0                  # expr 4", Tag),
        r("tag-0", "tag 0 in MAIN.", "7 0                     # expr 4", "! 0 0                   # expr 4", Tag),
        r("tag-17", "tag 17 (mdata, retired) in MAIN.", "7 0                     # expr 4", "! 17 1                  # expr 4", Tag),
        r("block-tag-19", "a frontier entry in a block.", "7 0                     # t3", "! 19 2 1                # t3", Tag),
        r("block-tag-18", "a declaration in a block.", "7 0                     # t3", "! 18 0 1 0 1 0          # t3", Tag),
        r("back-distance-0", "back distance 0.", "10 4 8                  # expr 12", "! 10 0 8                # expr 12", BackDistance),
        r("back-distance-past-start", "a back distance past the first expression.", "10 4 8                  # expr 12", "! 10 13 8               # expr 12", BackDistance),
        r("block-reference-0", "block reference 0.", "10 3 1                  # t11", "! 10 0 1                # t11", BackDistance),
        r("name-forward", "a name id not yet defined.", "9 1 0                   # expr 1", "! 9 17 0                # expr 1", NameId),
        r("name-prefix-self", "a name whose prefix is itself.", "1 6 s:\"mk\"", "! 1 7 s:\"mk\"", NameId),
        r("level-forward", "a level id not yet defined.", "8 1                     # expr 0", "! 8 6                   # expr 0", LevelId),
        r("frontier-back-0", "frontier back distance 0.", "19 2 1                  # frontier expr 0", "! 19 2 0                # frontier expr 0", FrontierBack),
        r("frontier-back-past-start", "a frontier entry past the first item.", "19 2 1                  # frontier expr 0", "! 19 2 2                # frontier expr 0", FrontierBack),
        r("frontier-duplicate", "a level listed twice in the frontier.", "19 1 1                  # frontier level 1", "! 19 1 2                # frontier level 1", FrontierDuplicate),
        r("block-exprs-0", "block-exprs 0.", "@d8 18 6 5 0 1 len:t cnt:t 1 5", "! @d8 18 6 5 0 1 len:t 0 1 5", BlockExprs),
        r("block-exprs-over-half", "block-exprs above block-length / 2.", "@d8 18 6 5 0 1 len:t cnt:t 1 5", "! @d8 18 6 5 0 1 len:t 999 1 5", BlockExprs),
        r("block-past-proofs", "a block longer than PROOFS.", "@d8 18 6 5 0 1 len:t cnt:t 1 5", "! @d8 18 6 5 0 1 99 cnt:t 1 5", ProofsFill),
        r("frontier-index-expr", "a frontier expression not listed before the theorem.", "11 2 7 14 1             # t12", "! 11 2 7 15 1           # t12", FrontierIndex),
        r("frontier-index-name", "a frontier name not listed before the theorem.", "11 2 7 14 1             # t12", "! 11 2 8 14 1           # t12", FrontierIndex),
        r("frontier-index-level", "a frontier level not listed before the theorem.", "8 1                     # t1", "! 8 2                   # t1", FrontierIndex),
        r("rule-p-later", "a block names a constant declared after its theorem.", "9 4 1 1                 # t0", "! 9 7 1 1               # t0", RuleP),
        r("rule-p-self", "a block names its own theorem.", "9 4 1 1                 # t0", "! 9 2 1 1               # t0", RuleP),
        r("rule-p-proj", "a block projects with a structure declared after its theorem.", "16 3 0 1                # t10", "! 16 7 0 1              # t10", RuleP),
        r("rule-p-undeclared", "a block names a name no declaration declares.", "9 4 1 1                 # t0", "! 9 0 1 1               # t0", RuleP),
        r("duplicate-name", "a name declared by two declarations.", "@d4 18 4 12 1 4 1 0", "! @d4 18 4 1 1 4 1 0", DuplicateName),
        r(
            "duplicate-name-in-block",
            "a constructor named like its type.",
            "@d2 18 5 1 6 1 4 23 0 0 0 1 6 1 7 0 0 0 1 7 1 4 14",
            "! @d2 18 5 1 6 1 4 23 0 0 0 1 6 1 7 0 0 0 1 6 1 4 14 0 6 0 0 1 1 8 2 9 4 5 0 1 6 0 0 1 1 1 7 1 1 0",
            DuplicateName,
        ),
    ];
    for (n, s, w) in prims {
        add(&n, s, w);
    }
    add(
        "block-fewer-records",
        m(
            BASE,
            "block-exprs one below the records in the block.",
            &[
                (
                    "@d8 18 6 5 0 1 len:t cnt:t 1 5",
                    "@d8 18 6 5 0 1 len:t 16 1 5",
                ),
                (
                    "13 0 14 12 1            # t16",
                    "! 13 0 14 12 1          # t16",
                ),
            ],
        ),
        Want::Reject(BlockCount, Marked),
    );
    add(
        "block-more-records",
        m(
            BASE,
            "block-exprs one above the records in the block.",
            &[(
                "@d8 18 6 5 0 1 len:t cnt:t 1 5",
                "@d8 18 6 5 0 1 len:t 18 1 5",
            )],
        ),
        Want::Reject(BlockCount, BlockEnd("t", 18, 8)),
    );
    add(
        "proofs-not-filled",
        m(
            BASE,
            "PROOFS holds a byte after the last block.",
            &[(
                "13 0 14 12 1            # t16",
                "13 0 14 12 1            # t16\nblock extra\nx:07",
            )],
        ),
        Want::Reject(ProofsFill, SectionAt(format::SEC_PROOFS, u64::MAX)),
    );
    add(
        "proofs-without-blocks",
        header_note(
            &MAIN_ONLY.replace("counts 3 1 13 1", "section PROOFS\nx:0700\ncounts 3 1 13 1"),
            "PROOFS without a proof block.",
        ),
        Want::Reject(ProofsFill, SectionAt(format::SEC_PROOFS, 0)),
    );

    // bad INDEX
    let bi = |name: &str, note: &str, pairs: &[(&str, &str)], looks: Vec<(&'static str, Look)>| {
        (
            name.to_string(),
            m(BASE, note, pairs),
            Want::BadIndex(looks),
        )
    };
    let bad = vec![
        bi(
            "index-offset",
            "entry 0's offset is not at its record.",
            &[("0 rel:MAIN:d0", "0 rel:d0:d0")],
            vec![("Nat", Look::Invalid)],
        ),
        bi(
            "index-kind",
            "entry 2's kind is not its record's.",
            &[("5 rel:d1:d2", "2 rel:d1:d2")],
            vec![("Ind", Look::Invalid), ("Nat", Look::Found(0))],
        ),
        bi(
            "index-block-length",
            "entry 8's block length is not its record's.",
            &[("6 rel:d7:d8 len:t", "6 rel:d7:d8 3")],
            vec![("T", Look::Invalid)],
        ),
        bi(
            "index-order",
            "keys out of order.",
            &[("nt S 7\nnt T 8", "nt T 8\nnt S 7")],
            vec![("Nat", Look::Invalid)],
        ),
        bi(
            "index-repeated",
            "a key repeated (an empty suffix).",
            &[("nt T 8", "nt T 8\nnt T 8")],
            vec![("T", Look::Invalid)],
        ),
        bi(
            "index-shared-not-maximal",
            "shared is not the full common prefix.",
            &[("nt S 7", "nt S 7 shared=1")],
            vec![("S", Look::Invalid)],
        ),
        bi(
            "index-name-missing",
            "a declared name missing from the table.",
            &[("nt Z 9\n", "")],
            vec![("Z", Look::NotFound), ("T", Look::Found(8))],
        ),
        bi(
            "index-wrong-decl",
            "a key naming the wrong declaration.",
            &[("nt S 7", "nt S 6")],
            vec![("S", Look::Invalid)],
        ),
        bi(
            "index-decl-count",
            "decl-count is not the number of declarations.",
            &[(
                "10                      # decl-count",
                "11                      # decl-count",
            )],
            vec![("Nat", Look::Invalid)],
        ),
    ];
    for (n, s, w) in bad {
        add(&n, s, w);
    }
    v
}

fn place_name(p: Place) -> String {
    p.to_string()
}

/// The expectation text a vector's `.expect` file holds, computed from the
/// vector (its want and the assembled layout), not from the reader; only
/// the digest of an accepted file comes from the reader.
pub fn expect_text(v: &Vector, a: &Assembled) -> String {
    let lay = &a.layout;
    let loc = |class: Class, e: Exp| -> String {
        let (place, off, rec, decl): (String, u64, u64, Option<u32>) = match e {
            Exp::Marked => {
                let m = a
                    .marked
                    .unwrap_or_else(|| panic!("{}: no marked record", v.name));
                (format::section_name(m.section), m.offset, m.record, m.decl)
            }
            Exp::Header(k) => ("header".into(), k, 0, None),
            Exp::FromEnd(k) => ("trailer".into(), lay.len - k, 0, None),
            Exp::Trailer(k) => ("trailer".into(), lay.trailer + k, 0, None),
            Exp::Entry(i, k) => ("directory".into(), lay.entry(i) + k, i as u64 + 1, None),
            Exp::DirCount => ("directory".into(), lay.trailer + 16, 0, None),
            Exp::SectionAt(id, k) => {
                let k = if k == u64::MAX { lay.blocks["t"].1 } else { k };
                (format::section_name(id), lay.section(id).0 + k, 0, None)
            }
            Exp::BlockEnd(l, rec, d) => {
                let b = lay.blocks[l];
                ("PROOFS".into(), b.0 + b.1, rec, Some(d))
            }
        };
        let mut s = format!(
            "class {}\nplace {place}\noffset {off}\nrecord {rec}\n",
            class.name()
        );
        if let Some(d) = decl {
            s.push_str(&format!("decl {d}\n"));
        }
        s
    };
    match &v.want {
        Want::Accept => accepted_text(&a.bytes, true),
        Want::Reject(c, e) => format!("outcome rejected\n{}", loc(*c, *e)),
        Want::Decline(c, e) => format!("outcome declined\n{}", loc(*c, *e)),
        Want::BadIndex(looks) => {
            let mut s = accepted_text(&a.bytes, false);
            s.push_str("index invalid\n");
            for (n, l) in looks {
                s.push_str(&match l {
                    Look::Found(d) => format!("lookup {n} found {d}\n"),
                    Look::NotFound => format!("lookup {n} notfound\n"),
                    Look::Invalid => format!("lookup {n} invalid\n"),
                });
            }
            s
        }
    }
}

// counts from the trailer, digest from the reader; with `index`, the INDEX
// state of the file (`absent` or `ok`, the latter with every name's lookup).
fn accepted_text(bytes: &[u8], index: bool) -> String {
    let f = read::File::open(bytes).expect("an accept vector opens");
    let c = f.counts;
    let d = crate::digest::of_susz(bytes)
        .map(|d| format!("{d:016x}"))
        .unwrap_or_else(|e| format!("error {e}"));
    let mut s = format!(
        "outcome accepted\ncounts {} {} {} {}\ndigest {d}\n",
        c[0], c[1], c[2], c[3]
    );
    if index {
        match crate::index::parse(&f) {
            Err(crate::index::IndexError::Absent) => s.push_str("index absent\n"),
            Ok(ix) => {
                s.push_str("index ok\n");
                for (k, d) in &ix.names {
                    s.push_str(&format!("lookup {} found {d}\n", dotted(k)));
                }
            }
            Err(e) => s.push_str(&format!("index error {e}\n")),
        }
    }
    s
}

/// The dotted form of an INDEX key (for vector files).
pub fn dotted(k: &[u8]) -> String {
    let mut out = Vec::new();
    let mut p = 0;
    while p < k.len() {
        let t = k[p];
        p += 1;
        let v = format::get_varint(k, &mut p, k.len()).unwrap_or(0);
        if t == 1 {
            out.push(String::from_utf8_lossy(&k[p..p + v as usize]).into_owned());
            p += v as usize;
        } else {
            out.push(v.to_string());
        }
    }
    out.join(".")
}

/// The expectation text the reader gives for a vector's bytes (what the
/// tests compare with the `.expect` file).
pub fn observed_text(v: &Vector, bytes: &[u8]) -> String {
    let lookups = |looks: &[(&str, Look)], f: &read::File| -> String {
        let mut s = String::new();
        for (n, _) in looks {
            let key = crate::index::key_of_dotted(n);
            s.push_str(&match crate::index::lookup(f, &key) {
                Ok(x) => format!("lookup {n} found {}\n", x.decl),
                Err(crate::index::IndexError::NotFound) => format!("lookup {n} notfound\n"),
                Err(crate::index::IndexError::Invalid(_)) => format!("lookup {n} invalid\n"),
                Err(e) => format!("lookup {n} error {e}\n"),
            });
        }
        s
    };
    match read::verify(bytes) {
        Outcome::Accepted(_) => {
            let f = read::File::open(bytes).unwrap();
            match &v.want {
                Want::BadIndex(looks) => {
                    let mut s = accepted_text(bytes, false);
                    match crate::index::verify_index(&f) {
                        Err(crate::index::IndexError::Invalid(_)) => s.push_str("index invalid\n"),
                        Ok(()) => s.push_str("index ok (expected invalid)\n"),
                        Err(e) => s.push_str(&format!("index error {e}\n")),
                    }
                    s.push_str(&lookups(looks, &f));
                    s
                }
                _ => {
                    let mut s = accepted_text(bytes, true);
                    if s.contains("index ok") {
                        if let Err(e) = crate::index::verify_index(&f) {
                            s.push_str(&format!("verify-index failed: {e}\n"));
                        }
                        // every listed name looks up to its declaration
                        let ix = crate::index::parse(&f).unwrap();
                        for (k, d) in &ix.names {
                            match crate::index::lookup(&f, k) {
                                Ok(x) if x.decl == *d => {}
                                r => s.push_str(&format!("lookup {} gave {r:?}\n", dotted(k))),
                            }
                        }
                    }
                    s
                }
            }
        }
        Outcome::Rejected(e) => format!("outcome rejected\n{}", fail_text(&e)),
        Outcome::Declined(e) => format!("outcome declined\n{}", fail_text(&e)),
    }
}

fn fail_text(e: &read::Failure) -> String {
    let mut s = format!(
        "class {}\nplace {}\noffset {}\nrecord {}\n",
        e.class.name(),
        place_name(e.place),
        e.offset,
        e.record
    );
    if let Some(d) = e.decl {
        s.push_str(&format!("decl {d}\n"));
    }
    s
}

/// Assembles a vector.
pub fn build(v: &Vector) -> Assembled {
    assemble(&v.src).unwrap_or_else(|e| panic!("{}: {e}", v.name))
}
