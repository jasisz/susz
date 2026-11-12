# Open questions found while implementing Susz 1

Each item is an ambiguity or gap in [`spec.md`](spec.md) found while
writing the reference crate. The crate follows the **proposed resolution**;
the test vectors pin it. None changes the format's bytes; most only pin an
error location or a packer's exit class. Another implementation (the Aver
reader and packer) should follow the same resolutions, or the owner should
decide otherwise and the spec should say so.

## 1. Rule P and "a packer writes only accepted files" (sections 6, 9, 10)

The canonical layout (section 9) puts every expression only one theorem's
value reaches in that theorem's block. If the export's theorem names a
constant not declared before it (a broken export, or an Arena-style test of
a failing theorem), the canonical file breaks rule P, while section 10 says
a packer writes only files a reader accepts.

**Resolution:** the packer writes the canonical layout anyway. A rule P
violation is a structural error inside a proof block, which section 2 makes
a failure of that theorem, ordered with the other declaration failures;
section 10 already allows "for a checker, proceed to check". The kernel
would fail the theorem too, so the outcome is the same (Appendix A, R6 (a)).
`susz verify` reports such a file as rejected at the block. Proposed
wording for section 9: "A packer MUST write only files whose header,
directory, trailer and MAIN are well-formed; a proof block that breaks
rule P reflects a failing theorem of the export."

## 2. Duplicate declared names in the export (sections 5.2, 9)

Unique declared names is a MAIN rule, so a canonical packer cannot write an
export that declares a name twice (Lean rejects such an environment too).

**Resolution:** the packer refuses: exit 1 (not a valid export), with the
name and both declaration indices.

## 3. A declaration named by the anonymous name (sections 5.2, 6a.1)

Nothing in MAIN forbids it, but its INDEX key is empty and the name table
needs a non-empty suffix for every key, so no correct INDEX exists for such
a file.

**Resolution:** the packer refuses it (exit 1), with and without INDEX, so
the two settings keep the same outcome. Readers accept it in MAIN;
`verify_index` reports any INDEX of such a file invalid. Proposed: make it a
structural error of MAIN ("a declared name is not the anonymous name").

## 4. Name equality for unique names and rule P (sections 5.2, 6)

MAIN may hold two name records for the same name (same prefix, same
component). The spec says "declared by an earlier declaration" without
saying whether names compare by id or by value.

**Resolution:** by value: two names are equal when their prefixes are equal
and their components are equal (string bytes, or number). Both checks, and
INDEX keys, use this equality. Proposed: say so in 5.2.

## 5. Where a counts mismatch is reported, and when (sections 4, 8)

Section 8 orders "trailer and directory" before MAIN, but the counts can
only be compared after MAIN.

**Resolution:** after the last MAIN record, before the PROOFS fill check;
at the trailer field that differs first (names, levels, expressions,
declarations), record 0. A reader may use the counts before that only as
allocation hints, capped by MAIN's length.

## 6. Where PROOFS fill errors are reported (sections 5.2, 6)

**Resolution:** a kind-6 record whose block would run past PROOFS (or with
no PROOFS section) is an error of that MAIN record (class `proofs-fill`).
After MAIN: PROOFS present without any kind-6 record (even of length 0) is
an error at PROOFS' first byte; PROOFS longer than the blocks is an error at
the first byte after the last block. Both have record 0 and come after the
counts check.

## 7. PAD's place in the error order (sections 4.1, 8)

**Resolution:** PAD is checked with the framing, after the directory and
before MAIN, at its first non-zero byte (record 0).

## 8. Order inside the header, trailer and directory (section 8)

**Resolution:** header: magic, length, major (a decline), reserved fields.
Trailer: end magic, trailer length range, trailer length against the
section count. Directory, entry by entry: reserved field, flag bits, flags
of a known id, duplicate id, start offset (tiling), end within the body;
then a gap before the trailer, then a missing MAIN; only then a decline for
an unknown must-understand section (the first in directory order). So a
file with a malformed directory is rejected even if it also needs an
unknown section. Directory errors give the entry's number (from 1) as the
record number; header and trailer errors give 0.

## 9. Two errors in one record (section 8)

The class is pinned by the conformance suite, so it matters which of two
broken fields of one record is reported.

**Resolution:** the first broken field in byte order. A duplicate declared
name is checked when its name field is read (before later fields).

## 10. Block record count errors (section 6)

**Resolution:** a block with fewer records than `block-exprs`: class
`block-count` at the block's end, record number = records found + 1. A
block with bytes left after `block-exprs` records: class `block-count` at
the first byte left, record number `block-exprs` + 1. A record cut by the
block's end: class `truncated` at the record's start.

## 11. Which ndjson inputs a packer accepts (sections 9, 9.1)

Byte-identical packers must also agree on which inputs they pack. The spec
names lean4export 3.1 but not the JSON dialect or the header form.

**Resolution (as the Aver packer's reader):** non-negative integers only
(leading zeros allowed), raw control characters allowed in strings, a
trailing comma allowed in objects; a key not in the record's lean4export 3.1
key set: exit 2; a missing or repeated key: exit 1. The header line must be
exactly `{"meta":M}` (M kept byte for byte as SOURCE); another form, or a
`format.version` other than 3.1.x: exit 2. SOURCE is always written.
Numbers that do not fit a u64 (a `Name.num` component, a bound variable
index, a projection index): exit 2.
