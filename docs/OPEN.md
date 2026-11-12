# Open questions in Susz 1

These are gaps in [`spec.md`](spec.md) that came up while writing the
reference crate. The crate follows the answers below, and the test vectors
pin them. None of them changes the bytes of the format. Most only fix an
error location or a packer's exit code. Other implementations should follow
the same answers unless the spec later says otherwise.

## 1. Rule P and "a packer writes only accepted files" (sections 6, 9, 10)

If a theorem in the export names a constant that is not declared before it,
the canonical file breaks rule P, so does the packer still write it?

Yes, the packer writes the canonical layout anyway, and `susz verify`
rejects the file at that block.

A rule P violation in a block is a failure of that theorem (section 2).
Section 10 already lets a checker go on to check such a file, and the kernel
would fail the theorem too (Appendix A, R6 (a)).

The spec could say instead that a packer writes only files whose header,
directory, trailer and MAIN are well-formed.

## 2. Duplicate declared names in the export (sections 5.2, 9)

What does the packer do with an export that declares a name twice?

It refuses with exit 1 (not a valid export), and names the duplicate and both
declaration indices.

Unique declared names is a MAIN rule, so no canonical file can hold such an
export, and Lean rejects such an environment too.

## 3. A declaration named by the anonymous name (sections 5.2, 6a.1)

What happens to a declaration whose name is the anonymous name?

The packer refuses it with exit 1, with or without INDEX. Readers accept it
in MAIN, and an INDEX check reports any INDEX of such a file invalid.

Its INDEX key would be empty while every key needs a non-empty suffix, so no
correct INDEX exists, and refusing in both settings keeps their outcomes the
same.

The spec could make it a structural error of MAIN ("a declared name is not
the anonymous name").

## 4. Name equality for unique names and rule P (sections 5.2, 6)

MAIN may hold two name records for the same name, so do these rules compare
names by id or by value?

By value. Two names are equal when their prefixes are equal and their
components are equal (the same string bytes, or the same number), and both
rules and the INDEX keys use this equality.

The spec says "declared by an earlier declaration" without saying which, and
comparing ids would miss a name written twice. Section 5.2 could say so.

## 5. Where a counts mismatch is reported, and when (sections 4, 8)

Where and when does a reader report trailer counts that differ from MAIN?

After the last MAIN record and before the PROOFS fill check, at the first
trailer count that differs (names, levels, expressions, declarations), with
record number 0. Before that, a reader uses the counts only as allocation
hints, capped by MAIN's length.

Section 8 puts the trailer before MAIN, but the counts can only be compared
once MAIN is read.

## 6. Where PROOFS fill errors are reported (sections 5.2, 6)

Where does a reader report blocks that do not fill PROOFS exactly?

A kind-6 record whose block would run past PROOFS, or that has no PROOFS
section at all, is an error at that MAIN record (class `proofs-fill`). Two
more cases are found after MAIN and after the counts check, both with record
number 0:

- a PROOFS section with no kind-6 record (even if it has length 0) is an
  error at its first byte;
- a PROOFS section longer than its blocks is an error at the first byte
  after the last block.

An overrun shows at the record that causes it, while the other two cases
only show once all of MAIN is read.

## 7. PAD's place in the error order (sections 4.1, 8)

Where does PAD's all-zero check go in the error order?

With the framing, after the directory and before MAIN. It is reported at the
first non-zero byte, with record number 0.

PAD is not part of MAIN, and every reader checks it, so it belongs with the
framing.

## 8. Order inside the header, trailer and directory (section 8)

In what order does a reader check the header, the trailer and the directory?

- Header: magic, length, major (a decline), reserved fields.
- Trailer: end magic, the range of the trailer length, the trailer length
  against the section count.
- Directory, entry by entry: reserved field, flag bits, flags of a known id,
  duplicate id, start offset (tiling), end within the body.
- Then a gap before the trailer, then a missing MAIN.
- Only then a decline for an unknown must-understand section, the first one
  in directory order.

Directory errors give the entry's number (from 1) as the record number.
Header and trailer errors give 0.

This way a file with a malformed directory is rejected, even if it also needs
an unknown section.

## 9. Two errors in one record (section 8)

Which error does a reader report when one record has two broken fields?

The first broken field in byte order. A duplicate declared name is checked
when its name field is read, before the later fields.

The conformance suite pins the error class, so the choice matters.

## 10. Block record count errors (section 6)

How does a reader report a block with the wrong number of records?

- Fewer records than `block-exprs`: class `block-count` at the block's end,
  with record number = records found + 1.
- Bytes left after `block-exprs` records: class `block-count` at the first
  byte left, with record number `block-exprs` + 1.
- A record cut off by the block's end: class `truncated` at the record's
  start.

The conformance suite pins class and location, so each case needs one fixed
answer.

## 11. Which ndjson inputs a packer accepts (sections 9, 9.1)

The spec names lean4export 3.1 but not the JSON dialect or the header line,
so which inputs does a packer accept?

- Integers: non-negative only. Leading zeros are allowed.
- Strings may hold raw control characters.
- An object may end with a trailing comma.
- A key outside the record's lean4export 3.1 key set: exit 2.
- A missing or repeated key: exit 1.
- The header line must be exactly `{"meta":M}`. M is kept byte for byte as
  SOURCE. Any other form, or a `format.version` other than 3.1.x: exit 2.
- SOURCE is always written.
- A number that does not fit a u64 (a `Name.num` component, a bound variable
  index, a projection index): exit 2.

Byte-identical packers must also agree on which inputs they pack, and these
rules match the reader of the Aver packer.
