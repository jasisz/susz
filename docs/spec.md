# Susz 1

Version: Susz 1 (major 1), 2026-11-12.

Susz (`.susz`) is a binary form of a Lean 4 kernel export: the records of a
lean4export 3.1 ndjson file, without text to parse, with each proof that
only one theorem uses kept in a block of its own. This document defines the
first public version, **Susz 1**. The internal versions 0 and 2 (and the
branch version 1) are not Susz 1 and a Susz 1 reader does not read them.

Key words MUST, MUST NOT, SHOULD, MAY as in RFC 2119.

Sections 1-9 and 11 are normative. Appendix A lists the decisions behind
the choices (referred to as A.1 ... A.14) with their rationale; Appendix B
lists the changes from the internal version 2. Questions found while
implementing, with the resolution the reference crate follows, are in
[`OPEN.md`](OPEN.md).

## 1. Rules (unchanged from version 2)

1. **The file is input, not a witness.** A file holds structure only: no
   hashes, loose-bound-variable ranges, flags, or other derived facts. Every
   size, offset and count the file gives a reader is verified against the
   records it describes; a file whose hints disagree with its records is
   rejected. The verdict `accepted` is given only once the whole file was
   read and verified.
2. **Declaration order is content.** Admission to the environment and every
   "declared before" rule are computed from the order of declaration records,
   never from layout.
3. **Layout is a hint.** Which expressions sit in proof blocks, and section
   placement, may change only how fast a file is read, never the verdict.
4. **Errors are deterministic.** The outcome of a full check (and the
   location of the reported error, section 8) is a function of the file
   bytes, excluding the content of the INDEX section, alone: the same for
   any number of workers, for eager or lazy decoding of proof blocks, and
   whether or not the reader looks at INDEX.
5. **Packing is deterministic.** The same export, with INDEX on or off,
   gives the same bytes from any canonical packer (section 9).

Also kept: implicit dense ids, expressions named by back distance, proof
blocks bounded by the frontier, the trailer at the end of the file.

## 2. Outcomes

A reader gives exactly one of:

- **accepted**: the file is well-formed and (for a checker) every
  declaration was admitted;
- **rejected**: the file is malformed (a *structural error*) or a declaration
  fails;
- **declined**: the reader cannot judge the file: it needs a feature the
  reader does not implement (unknown major version, unknown must-understand
  section) or exceeds one of the reader's own implementation limits
  (section 7.2). Declined is not a verdict on the file.

A *subset check* (section 6a.2) has one more outcome, **index invalid**: an
INDEX entry it relied on disagrees with the records. It ends that subset
check only; it is never a verdict on the file.

A *structural error* of the header, the directory, the trailer or the MAIN
section rejects the file before any declaration is checked. A structural
error inside a proof block is an error of that block's theorem, ordered with
the other declaration failures (section 8).

## 3. Encoding primitives

- Fixed-width integers (`u16`, `u32`, `u64`) are little-endian.
- **varint**: unsigned LEB128, 7 bits per byte, low group first, high bit set
  on every byte but the last. A varint MUST be minimal: a varint of more
  than one byte MUST NOT end in the byte `0x00`. It MUST have at most 10
  bytes and its value MUST be below 2^64 (so a 10th byte is `0x00`...`0x01`,
  and `0x00` is excluded by minimality: the 10th byte is exactly `0x01`).
  Every varint field is a u64; fields have tighter ranges where stated.
- **bool**: one byte, `0x00` or `0x01`; any other value is an error.
- **enum byte**: one byte with the values listed for that field; any other
  value is an error.
- **bytes**: varint length `n`, then `n` bytes.
- **string**: `bytes` that MUST be well-formed UTF-8 (RFC 3629: no overlong
  forms, no surrogates, nothing above U+10FFFF). No normalisation; NUL is
  allowed.
- **list**: varint count `n`, then `n` varints.
- **nat**: a natural number of any size: `bytes` holding the number's
  minimal little-endian base-256 digits. Zero is the empty byte string; a
  non-empty one MUST NOT end in `0x00`. (Only Nat literals use it; see
  A.2.)

A length or count is never trusted for allocation: a reader MUST check that
the bytes it announces exist (`n` bytes for bytes/strings, at least `n` bytes
for a list or a record count) before reserving room for them.

## 4. File layout

```
file      = header body trailer
header    = magic major:u16 reserved:u16=0 reserved:u32=0          ; 16 bytes
magic     = 53 55 53 5A 0D 0A 1A 0A                               ; "SUSZ\r\n\x1a\n"
body      = section*                     ; the sections, tiled in directory order
trailer   = counts directory trailer-length:u32 end-magic
counts    = names:u32 levels:u32 exprs:u32 decls:u32
directory = section-count:u32 entry{section-count}
entry     = id:u16 flags:u16 reserved:u32=0 offset:u64 length:u64  ; 24 bytes
end-magic = 5A 53 55 53                                           ; "ZSUS"
```

- `major` is 1 for this document. A reader declines a file of another major.
  The magic's byte 4 is `0x0D`, never a valid internal version byte (0, 1,
  2), so old and new files cannot be confused; the `\r\n\x1a\n` tail
  detects text-mode corruption as in PNG. There is no `minor` field:
  additions are announced by sections (A.5, A.14).
- `trailer-length` counts the whole trailer, these last 8 bytes included,
  so a reader finds the trailer from the end of the file. It MUST equal
  `16 + 4 + 24 * section-count + 8`.
- `counts`: the number of names and levels (each including its implicit id
  0), of MAIN expressions, and of declarations. They MUST equal what the
  MAIN section defines. (Format limit, section 7.1.)
- `flags` bit 0 is **must-understand**; bits 1-15 MUST be 0.
- Sections MUST tile the body exactly: the first starts at offset 16, each
  next one where the one before ended, and the last ends where the trailer
  starts. No gaps, no overlap, no bytes outside a section.
- An id MUST NOT occur twice.

### 4.1 Section ids

| id | name | must-understand | required | content |
| --- | --- | --- | --- | --- |
| 1 | MAIN | yes | yes | names, levels, shared expressions, frontier, declarations (section 5) |
| 2 | PROOFS | yes | iff some kind-6 declaration exists | proof blocks (section 6) |
| 3 | SOURCE | no | no | the source export's `meta` object, verbatim UTF-8 JSON (A.10) |
| 4 | PAD | no | no | zero bytes, for alignment; MUST be all `0x00` |
| 5 | INDEX | no | no (written by default, `--no-index` omits it) | declaration index and name table (section 6a) |
| 6..0x7FFF | reserved | | | |
| 0x8000..0xFFFF | private / experimental | | | never in canonical files |

- A known id whose flags differ from the table is a structural error.
- An unknown id with must-understand set: the reader **declines**
  ("needs section N"): the file is not shown malformed, only beyond this
  reader (A.6).
- An unknown id without must-understand: skipped, never read.
- A known informational section MAY be skipped by a reader that does not
  use it. SOURCE never changes the verdict: a reader that parses it and
  finds bad JSON ignores it (and MAY warn). INDEX never changes the
  verdict of a **full check** (one that gives the file's verdict), which MAY
  ignore it entirely, at no cost. A reader that uses INDEX (lookup, subset
  check) MUST verify every entry it relies on against the records; a
  disagreement gives that reader's subset result the outcome **index
  invalid** (section 6a.3), never a full-check verdict. The INDEX directory
  entry itself (id, flags, offset, length) is part of the directory and
  checked as such by every reader. PAD's
  all-zero rule is checked by every reader, so that no byte of a canonical
  file is unconstrained.

## 5. MAIN section

```
main     = record*
record   = name-rec | level-rec | expr-rec | frontier-rec | decl-rec
```

Ids are implicit and dense, per kind, in record order: names from 1 (0 is
the anonymous name), levels from 1 (0 is level zero), MAIN expressions from
0, declarations from 0. A name or level field holds the id. An expression
field holds a **back distance** `d`: it names the expression whose id is
(next expression id) − `d`; `1 <= d <= ` (number of expressions defined so
far) MUST hold.

### 5.1 Records

| tag | record | fields |
| --- | --- | --- |
| 1 | name `str` | prefix: name, component: string |
| 2 | name `num` | prefix: name, component: varint (A.1) |
| 3 | level `succ` | level |
| 4 | level `max` | level, level |
| 5 | level `imax` | level, level |
| 6 | level `param` | name |
| 7 | `bvar` | index: varint |
| 8 | `sort` | level |
| 9 | `const` | name, levels: list |
| 10 | `app` | fn: back, arg: back |
| 11 | `lam` | binder: enum, name, type: back, body: back |
| 12 | `forallE` | binder: enum, name, type: back, body: back |
| 13 | `letE` | name, type: back, value: back, body: back |
| 14 | `natVal` | value: nat |
| 15 | `strVal` | value: string |
| 16 | `proj` | struct: name, field: varint, expr: back |
| 17 | (reserved; was `mdata`, A.7) | |
| 18 | declaration | kind: enum, fields per kind (5.2) |
| 19 | frontier entry | kind: enum (0 name, 1 level, 2 expression), back: varint |
| other | | structural error |

Binder: 0 default, 1 implicit, 2 strict implicit, 3 instance implicit.

A name, level or level-list element MUST be an id already defined (names:
`< ` next name id; levels: `< ` next level id). A frontier entry names the
item `d` back from the next id of its kind (`1 <= d <= ` next id, the
implicit 0 counting). The frontier entries of each kind are numbered from 0
in record order; an item MUST NOT be listed twice (A.13).

### 5.2 Declarations

`head = name, params: list of names, type: back`.

| kind | declaration | fields after the kind byte |
| --- | --- | --- |
| 0 | axiom | head, unsafe: bool |
| 1 | definition | head, value: back, hints, safety: enum, all: list |
| 2 | theorem | head, value: back, all: list |
| 3 | opaque | head, value: back, unsafe: bool, all: list |
| 4 | quotient | head, qkind: enum (0 type, 1 ctor, 2 lift, 3 ind) |
| 5 | inductive block | types, ctors, recs: each a varint count then the parts |
| 6 | theorem, proof in a block | head, block-length: varint, block-exprs: varint, all: list |

Hints: enum 0 opaque, 1 abbrev, 2 regular followed by height: varint.
Safety: 0 safe, 1 unsafe, 2 partial. Inductive type: head, unsafe: bool,
numParams, numIndices: varint, all: list, ctors: list, numNested: varint,
isRec: bool, isReflexive: bool. Constructor: head, unsafe: bool, induct:
name, cidx, numParams, numFields: varint. Recursor: head, unsafe: bool, all:
list, numParams, numIndices, numMotives, numMinors: varint, rules: varint
count of (ctor: name, nfields: varint, rhs: back), k: bool.

**Unique declared names (A.8).** Every name a declaration record
declares (its head name; for a block every type, constructor and recursor
name) MUST NOT be declared by any earlier declaration record or earlier in
the same record. A violation is a structural error at that record. A name's
**declaration index** is the index of the record declaring it.

Kind 6: `block-length` is the byte length of its proof block, `block-exprs`
the number of expression records in it; `1 <= block-exprs <= block-length /
2` MUST hold (an expression record takes at least 2 bytes) (A.4).

## 6. PROOFS section

```
proofs = block*            ; one per kind-6 declaration, in declaration order
block  = expr-rec{block-exprs}
```

The first kind-6 declaration's block starts the section; each next block
starts where the one before ended; the blocks MUST fill the section exactly
(checked from the MAIN section alone, before any block is decoded). A block
MUST hold exactly `block-exprs` records, all expression records (tags 7-16),
and end exactly after the last; its last expression is the theorem's value.

Inside a block of theorem `T`:

- A name field is a **frontier name index**, a level field a **frontier
  level index**; an index MUST be below the number of frontier entries of
  that kind listed in MAIN before `T`'s declaration record.
- An expression reference `r` from the block's expression `k` (counting from
  0) names the block's expression `k − r` when `1 <= r <= k`, and otherwise
  frontier expression `r − k − 1`, which MUST be below the number of
  frontier expression entries listed before `T`.
- **Declared before (rule P).** The name of every `const` and every `proj`
  record in the block MUST have a declaration index below `T`'s. A
  violation, like any other structural error of the block, is an error of
  `T` (section 8). There are no marks and no `placed` flag (Appendix A, R6).

## 6a. INDEX section

Purpose: let any checker, or a subset checker ("check
`Foo.bar`", "check namespace `Foo`"), find a declaration by name, jump to its
record in MAIN and to its proof block, without decoding every proof block
and without decoding MAIN past what it needs.

### 6a.1 Layout

```
index      = decl-count:varint entry{decl-count} name-count:varint name-entry{name-count}
entry      = kind:enum main-delta:varint [block-length:varint]   ; block-length iff kind = 6
name-entry = shared:varint suffix:bytes decl:varint
name-key   = component*                    ; root first
component  = 01 len:varint utf8-bytes      ; string component
           | 02 value:varint               ; numeric component
```

- `entry` i describes declaration i, in declaration order. `kind` is its
  declaration kind (0-6). `main-delta` is the offset of its record's tag byte
  minus that of entry i−1 (for i = 0: minus the start of MAIN); prefix sums
  give absolute offsets. `block-length` repeats the kind-6 record's, so a
  proof block's offset in PROOFS is the sum of the block lengths before it.
- The name table holds every declared name (a head name; for an inductive
  block every type, constructor and recursor name) exactly once, sorted by
  `name-key` bytewise, strictly increasing. Keys are front-coded: `shared`
  bytes of the previous key (0 for the first), then `suffix`; `shared` MUST
  be the full common prefix length (canonical), and `suffix` MUST be
  non-empty. `decl` is the index of the declaration declaring it.
- `decl-count` MUST equal `counts.decls`; `name-count` the number of
  declared names. Content and order are fully determined by MAIN, so
  canonical packers write identical bytes.
- Keys are not hashes: they are the names themselves, so rule 1's "no
  hashes" holds; a lookup is a binary search over the decoded table, or a
  linear scan of the front-coded bytes.

### 6a.2 What a subset checker gets, and what it still must read

With INDEX, finding `Foo.bar` costs reading INDEX only (no MAIN, no PROOFS):
it gives declaration i, its record offset, kind and, for a theorem with a
block, the block's byte range. Every namespace `Foo` is a contiguous run of
the sorted table (keys of `Foo.*` share the prefix of `Foo`).

What INDEX does not remove:

- **The MAIN prefix.** Records only point backwards, so declaration i depends
  only on MAIN bytes before the end of its record, plus its block. But those
  bytes are variable-length records (names, levels, shared expressions,
  frontier, earlier declarations) with no per-record offsets, so a checker
  must decode **all of MAIN up to declaration i** to build the terms its
  record and block name. For a declaration late in mathlib that is nearly
  all of MAIN; for one early in the file it is little. (Random access into
  MAIN would need an offset per expression, ~4 bytes × 105 M on mathlib: out
  of scope.)
- **Dependencies.** Which constants declaration i uses is known only from
  its terms; the declarations of those constants are all before i, so the
  same prefix holds them. A subset checker admits them as stated (or checks
  them too, at the cost of a full check of that prefix). Theorem blocks of
  dependencies are needed only by a checker that unfolds theorem values.
- **Proof blocks** other than those of the declarations being checked are
  never decoded.

A subset check's result ("`Foo.bar` checks, given the declarations before
it") is not the file's verdict: the rest of the file is not verified, and a
name missing from the name table is "not found", not a verdict.

### 6a.3 Verification (rule 1)

A reader that relies on an entry verifies it against the records it reads
anyway (the MAIN prefix): entry i's offset is the tag byte of declaration
i's record, of that kind, and `block-length` equals the record's; a name
entry's key equals the name the record of declaration `decl` declares, as
built from the MAIN name records. Sort order, front coding and the
"shared is the full common prefix" rule are checked on the entries it
decodes. A disagreement makes the subset check's outcome **index invalid**;
it does not reject the file, and a full check of the same file is
unaffected. A full check does not read INDEX. A tool that wants to vouch
for an INDEX (for instance a packer's self-test, or a `--verify-index`
option) checks every entry while MAIN is read (one comparison per
declaration) and the name table once after (decode, compare each key with
the name built for its declaration, strict order, every declared name once);
its result is reported apart from the verdict.

## 7. Limits

### 7.1 Format limits (normative, implementation-independent)

- Each of the four counts is at most 2^32 − 1, so every id fits a u32 in any
  implementation. (A.3; mathlib today: 105 M expressions, about 40×
  headroom.)
- Every other quantity is bounded only by the u64 range of varints and by
  the file's bytes. There is no format limit on record size, string or
  literal length, block length or block expression count.

### 7.2 Implementation limits

A reader MAY have its own limits (memory, vector sizes, chunk sizes). On
exceeding one it MUST **decline**, never reject, and the decline MUST be a
function of the file bytes (not of timing, worker count or buffering
accidents). When a reader declines while decoding a proof block lazily, the
outcome is the earliest event in declaration order: a failure of an earlier
declaration still makes the file rejected. Readers SHOULD document their
limits. Examples: a cap on a block's expression count (decidable from
`block-exprs` before checking starts), or on a literal's size. A limit that
depends on buffering (a record crossing a chunk boundary) is not a function
of the file bytes; such a record is read by a slow path instead.

## 8. Errors

A structural error is reported with: the section (or `header`, `directory`,
`trailer`), the **absolute byte offset of the first byte of the offending
record** (of the field, for header/trailer/directory errors), and the
record's number within its section or block (from 1). For a proof block, the
theorem's name too. Example: `PROOFS @ 18,342,117: block of Foo.bar, record
12: frontier name 9001 not listed before the declaration`.

Order: header, then trailer and directory, then MAIN records in file order:
the first error found in that order is reported, before any declaration is
checked. Then declaration failures in declaration order, the earliest
reported. Within one declaration: building failures first (universe
parameters named twice), then its block's structural error, then failures of
checking. The conformance suite pins (outcome, error class, section,
record offset) for structural errors; messages stay free text (A.12).

## 9. Packing (normative for canonical packers)

A packer MUST write only files a conformant reader accepts, and MUST be
deterministic. Any accepted layout is a valid Susz file: a simple packer MAY
put every expression in MAIN and emit no kind-6 declaration and no PROOFS
section. A **canonical** packer writes exactly this layout, so that any two
canonical packers produce identical bytes:

- Records in export order. An expression that only one theorem's value
  reaches (directly, or only through other such expressions) goes to that
  theorem's block, in export order; every other expression stays in MAIN,
  renumbered densely in export order.
- Each frontier entry right after the record of the item it lists; the
  anonymous name's and level zero's entries first, before any record, when
  they are listed.
- Sections in id order MAIN, PROOFS, INDEX, SOURCE; INDEX written by
  default and omitted with `--no-index` (every canonical packer takes the
  option); no
  PAD, no private sections.
- Canonical bytes are defined per (export, INDEX on/off): for each setting
  both canonical packers MUST write identical bytes. The two files differ
  only by the INDEX section and its directory entry.
- SOURCE holds the source export's `meta` object, byte for byte as in its
  header line.

### 9.1 What packing drops (normative)

A Susz file does not preserve, and a checker MUST NOT depend on:

- `mdata`: the metadata map is dropped, and the record itself is not
  written; a reference to an `mdata` expression is written as a reference
  to the expression it wraps (A.7);
- `letE.nondep` (elaboration only);
- the export's own numeric ids (`in`, `il`, `ie`): Susz numbers items
  itself, and MAIN expression ids differ from the export's;
- the placement of expressions in the export's line order, beyond what
  section 9 keeps. Declaration order is kept exactly.

Everything else in a lean4export 3.1 record is kept. A packer MUST refuse
(not silently drop) an export record or field it does not know.

## 10. Conformance

A conformant **reader** MUST:

1. reject every file breaking a MUST of sections 3-6 and the "MUST equal"
   checks of section 4, with the error located as in section 8;
2. accept (or, for a checker, proceed to check) every file satisfying them,
   unless it declines for a documented implementation limit or unknown
   must-understand section;
3. give the same outcome and error location regardless of parallelism,
   eager or lazy decoding, and buffering;
4. not allocate more than a constant times the bytes already validated;
5. treat informational sections as in 4.1: a full check's outcome MUST be
   the same with the INDEX section's content replaced by any bytes of the
   same length; a subset check MUST verify every INDEX entry it relies on
   and report "index invalid" on a mismatch (section 6a.3).

A conformant **packer** MUST write only accepted files and be deterministic;
a **canonical** packer MUST write the section 9 layout, with INDEX by
default and without it under `--no-index`. Canonical packers MUST
agree byte for byte on every corpus file, for each setting.

## 11. Test vectors and accept/reject corpus (plan)

- **Format:** `vectors/{accept,reject,decline}/NAME.susz` plus
  `NAME.expect` (outcome, class, section, offset, record number; for accept:
  counts and a digest of the decoded records). Vectors are generated from a
  small textual assembler (`susz-asm`, in the reference crate as a dev tool) so
  each is reviewable; every reject vector is one minimal mutation of an
  accept vector, named after the rule it breaks.
- **Accept:** minimal file (one axiom); MAIN-only file (no PROOFS); file
  with blocks; a block naming frontier items of each kind; varint edge
  values (0, 127, 128, 2^63, 2^64−1); `nat` 0, 255, 256, 2^64, 2^200;
  strings with NUL and 4-byte UTF-8; unknown informational section; PAD.
- **Reject (one or more each):** magic; reserved bytes; trailer length;
  end magic; directory overlap / gap / out of file / duplicate id / bad
  flags on a known id; counts mismatch; non-minimal varint; 11-byte varint;
  10th byte `0x02`; truncated varint/string/list; bad UTF-8 (overlong,
  surrogate, truncated); non-minimal `nat`; bool 2; each enum out of range;
  unknown tag in MAIN; tag 17; tag 19 or 18 in a block; back distance 0 and
  past the start; name/level id forward; frontier entry back 0, past the
  start, duplicate; blocks not filling PROOFS; block-exprs 0 or > length/2;
  block with fewer/more records; frontier index listed after T; rule P with
  a constant declared after T and with T itself; duplicate declared name
  (across records and inside one block); PAD with a non-zero byte.
- **Decline:** major 2; unknown must-understand section.
- **Corpus:** test exports and Init packed by every canonical packer,
  with and without `--no-index` (byte-identical required for each setting;
  the two settings' full-check outcomes identical), round-tripped to the export's records modulo
  section 9.1; mathlib/cslib in CI where memory allows.
- **INDEX vectors:** accept: file with INDEX, file without INDEX, a lookup
  of every declared name in the Init vector giving the right record; reject:
  offset not at a declaration record, kind mismatch, block-length mismatch,
  keys out of order or repeated, `shared` not maximal, empty suffix, a
  declared name missing, a key naming the wrong declaration, decl-count
  mismatch. Each of these is a bad-INDEX vector, not a reject vector: a
  full check MUST give the same outcome as for the same file with correct
  INDEX (or without it), and a subset check relying on the bad entry MUST
  give "index invalid". Accept vectors exist with and without INDEX.
- **Differential and fuzzing:** cargo-fuzz on the Rust reader (no panic, no
  over-allocation); mutated files read by two independent readers,
  requiring the same outcome and location.

## Appendix A. Decisions and rationale

Decided 2026-11-12. Rows A.1-A.10 and A.12-A.14 as recommended by the
review; A.11 against the recommendation: INDEX is in Susz 1 (section 6a),
optional at pack time, never part of a full check's verdict.

| # | choice | decided | alternative not taken |
| --- | --- | --- | --- |
| A.1 | `Name.num` component | u64 varint, packer refuses larger | `nat` bytes |
| A.2 | Nat literal | minimal little-endian bytes | canonical decimal |
| A.3 | format count limit | 2^32 − 1 per kind (u32 ids) | none (u64) |
| A.4 | proof block expression count | in the kind-6 record | at the block head (as v2) |
| A.5 | magic / version | new 8-byte magic, `major` = 1 | `"SUSZ"` + version byte 3 |
| A.6 | unknown must-understand section | decline | reject |
| A.7 | `mdata` | not written; references go to the wrapped expr | keep tag 17 as an alias |
| A.8 | unique declared names | structural rule of the format | checker refuses to reorder on duplicates |
| A.9 | literal-implied constants | checker: file-order prefix up to their last declaration | per-block cache isolation; or fail T |
| A.10 | meta | verbatim JSON in informational SOURCE | binary fields |
| A.11 | declaration index | **INDEX in Susz 1**, written by default, `--no-index` omits it; full checks ignore it (section 6a) | no index |
| A.12 | conformance pins error location | yes (section, record offset) | outcome only |
| A.13 | duplicate frontier entries | rejected | allowed |
| A.14 | `minor` version field | none (sections announce features) | u16 minor, informational |

### Rationale

**R1. Varints.** Minimal encoding required; value < 2^64; 10 bytes max.
Rationale: one byte per varint check (last byte non-zero) makes every value
have one encoding, which canonical packing and byte-identical packers need.
Naturally big fields: only Nat literals (own encoding, `nat`). **A.1:**
Lean's `Name.num` component is a `Nat` too. Recommendation: u64 varint, a
packer refuses a component ≥ 2^64 (none exists in practice; Lean generates
them from counters). Alternative: `nat` encoding, +1 byte per numeric
component.

**R2. Nat literals.** **A.2:** minimal little-endian bytes
(recommended: maps to bignum limbs, linear-time decode, half the size of
decimal; Init 1.9 KB → 1.0 KB) or canonical decimal (no sign, no leading
zero, `"0"` for zero; quadratic decode for huge literals, easy to eyeball).

**R3. Limits.** Section 7: one format limit (u32 counts), every implementation- or
buffering-shaped limit becomes a documented decline.

**R4. Versioning.** Section directory with must-understand bit, unknown
must → decline (A.6), unknown informational → skip. Public numbering
starts at major 1 with a new magic (A.5); internal 0/1/2 are not read by
Susz 1 readers. A checker MAY keep reading version 2 during a transition.

**R5. Tag 19.** Tag 19 is only the MAIN frontier entry; proof blocks have
no tag 19 (no marks). Tag 17 retired (A.7). Block records are exactly
tags 7-16.

**R6. Marks, `placed`, the literal constants.** Decision: remove all three
from the format; replace with rule P (section 6) and unique declared names
(section 5.2, A.8). Analysis:

- *Why they existed.* A checker that reorders checking (for instance by
  namespace) may do so only when every declaration names only constants
  placed before it; otherwise a
  declaration could meet cached facts about a constant declared after it.
  MAIN records are seen while reading; a lazy block is not, so v2 carried a
  per-theorem `placed` bool (verified on decode) and marks to reproduce the
  ndjson reader's per-line rule exactly.
- *Marks carry nothing on real exports.* Probe (native packer + read-only
  scan of v2 files): every proof block has exactly one mark and it equals its
  own theorem's index; no block has `placed = false`; no block names a
  constant declared at or after its theorem; no block holds a literal whose
  implied constants come later; no frontier item is listed twice. Init:
  35,735 blocks; etale: 12,051; reachability: 2,417; con-leche: 13,588;
  mathlib: 451,917 (3,285 Nat literals in blocks, all after `Nat` etc.).
- *What the checker needs before checking a block of T:* its byte range and
  expression count (from MAIN), the frontier bound at T (from MAIN), and an
  assurance that the block names only constants declared before T. Rule P
  gives that as a format rule, enforced at decode at the same cost as
  version 2's placement flag check (one comparison per const/proj).
- *What a malicious file can do without marks/bool.* (a) Name in T's block
  a constant declared after T: rule P makes it T's error; the kernel would
  also fail T (every constant in a theorem's value is looked up), so the
  outcome and its position are unchanged, only the message. (b) Name a
  constant X declared before T by a declaration the checker skips (unsafe),
  then redeclare X safely later: reordered, T could meet facts about the
  second X. A checker that skips unsafe declarations admits such a
  redeclaration (skipped names are not in its environment), which is also a divergence from Lean, where the
  duplicate is rejected. Unique declared names (A.8) closes it in the
  format; alternative: the checker refuses to reorder when a name is
  declared twice (computable from MAIN). (c) Use a literal in T's block
  before `Nat`/`String`/... are declared. Which constants a literal stands
  for is kernel knowledge (for a Lean kernel: `Nat`; `String`, `String.ofList`,
  `List`, `Char`, `Char.ofNat`), so it stays out of the format.
  **A.9:** recommendation: the checker computes from MAIN the index L of
  the declaration that places the last of its literal constants (infinite if
  one is missing) and checks declarations up to L in file order before
  reordering the rest. Every T after L has them placed before it, so no
  per-block information is needed. Cost: Init/mathlib's prelude prefix
  (hundreds of declarations) stays sequential. Alternatives: check a block
  that violates the literal rule with its worker's caches emptied before and
  after (needs an audit that no other carried state depends on the
  environment); or fail T (diverges from the kernel when only `String` is
  needed but `Char.ofNat` comes later).
- *Placement in MAIN* stays a checker
  computation, not a format rule: unsafe definitions may name themselves,
  which a "declared before use" format rule would reject.
- *Probes that would settle the remaining doubt:* (1) the scan
  of version-2 files on mathlib and con-leche is done, 0
  violations; cslib not run; (2) adversarial files for
  (a), (b), (c), each run with `--reorder-always` and in file order: same
  outcome required; (3) for A.9's isolation alternative: list every map
  a worker carries across declarations and mark it environment-dependent or
  not.

**R7. meta.** **A.10:** keep it as verbatim JSON in the informational
SOURCE section (recommended): provenance only, lossless, no reader needs a
JSON parser, and the verdict never depends on it. The record semantics are
fixed by the Susz major version, not by lean4export's `format.version`; a
packer checks the source version it understands. Alternative: binary fields
(exporter version, Lean version, githash): lossy for unknown keys.

**R8. Errors.** Byte offsets of the record start, plus section and record
number (section 8).

**R9. Subset checking / index / block offsets.** A.11 decided against
the recommendation: the INDEX section is in Susz 1 (section 6a), for other
checkers and for checking a fragment. Packers write it by default,
`--no-index` omits it. It is informational: a full check ignores it and its
verdict never depends on it; a reader that relies on an entry verifies it,
and a bad entry gives that reader's subset check the outcome "index
invalid". It finds a declaration and its block by name without decoding
proof blocks; checking still needs the MAIN prefix before the declaration
(section 6a.2). Cost: see Appendix B.

**R10. Multi-file.** Out of scope for Susz 1. Sketch only: a
must-understand IMPORTS section listing each imported file by a content
hash and its four counts; a file's ids would continue after its imports'
(names, levels, expressions, declarations), MAIN back distances could reach
into imported MAIN expressions, rule P and unique names would range over the
union. Open questions: how the frontier works across files, and whether
imports form a DAG or a chain.

**R11. Lossy choices.** Stated normatively in section 9.1.

## Appendix B. Changes from version 2

| change | size effect |
| --- | --- |
| marks removed from blocks | −134 KB Init |
| `placed` bool removed from kind 6 | −1 byte per block (−36 KB Init) |
| block count moved from block head to kind-6 record | 0 |
| Nat literals as minimal LE bytes | ≈0 (−0.9 KB Init) |
| `mdata` record dropped (A.7) | ≈0 (absent from Init) |
| header 16 bytes, directory trailer, SOURCE section | +~70 bytes |
| INDEX section (A.11) | +3.4% Init, +2.4% mathlib (see below) |
| varints minimal, UTF-8 strict, unique names, rule P | 0 (validation only) |
| version 0 (single block) dropped | n/a |

Measured on v2 files from the native packer, without INDEX: Init
34.57 MB −0.49%, etale 11.71 MB −0.42%, reachability 1.94 MB −0.50%,
con-leche 53.97 MB −0.12%, mathlib 639.6 MB −0.36% (marks 1.80 MB, bools
0.45 MB, literals 0.08 MB).

INDEX, estimated from the same files (entries + front-coded name table):
Init 0.20 + 0.98 MB = +3.40%; con-leche 0.09 + 0.41 MB = +0.93%; mathlib
2.63 + 12.99 MB = 15.6 MB, +2.44% (718,577 declared names, ~18 bytes per
name in the table, 34.3 MB unencoded keys). Net Susz 1 against v2: Init
+2.9%, mathlib +2.1%. The name table is 83% of INDEX on mathlib; storing name
ids instead of keys would need MAIN decoded for every lookup, which defeats
the purpose, so keys stay.
