# Susz 1

Version: Susz 1 (major 1), 2026-11-12.

Susz (`.susz`) is a binary form of a Lean 4 kernel export. It holds the
records of a lean4export 3.1 ndjson file, with no text to parse. A proof that
only one theorem uses sits in a block of its own.

This document defines Susz 1, the first public version. The earlier internal
versions (0, 1 and 2) are not Susz 1, and a Susz 1 reader does not read them.

MUST, MUST NOT, SHOULD and MAY are used as in RFC 2119.

Sections 1 to 10 are normative. Section 11 describes the test vectors. Appendix A lists the choices we made and
why. The text refers to them as A.1 to A.14. Appendix B lists the changes
from internal version 2. [`OPEN.md`](OPEN.md) lists questions that came up
while implementing, with the answers the reference crate follows.

## 1. Rules

1. **The file is input, not a witness.** A file holds structure only. It has
   no hashes, no ranges of loose bound variables, no flags and no other
   derived facts. A reader verifies every size, offset and count in the file
   against the records it describes. If one of these hints disagrees with the
   records, the reader rejects the file. A reader says `accepted` only after
   it has read and verified the whole file.
2. **Declaration order is content.** The order of the declaration records
   decides admission to the environment and every "declared before" rule.
   Layout never does.
3. **Layout is a hint.** Which expressions sit in proof blocks, and where the
   sections are, may change how fast a file is read. It never changes the
   verdict.
4. **Errors are deterministic.** The outcome of a full check depends only on
   the file bytes, leaving out the content of the INDEX section. So does the
   location of the reported error (section 8). Both are the same for any
   number of workers, for eager or lazy decoding of proof blocks, and whether
   or not the reader looks at INDEX.
5. **Packing is deterministic.** For a given export and INDEX setting (on or
   off), every canonical packer writes the same bytes (section 9).

## 2. Outcomes

A reader gives exactly one of three outcomes.

- **accepted**: the file is well-formed. For a checker, every declaration was
  also admitted.
- **rejected**: the file is malformed (a *structural error*), or a
  declaration fails.
- **declined**: the reader cannot judge the file. Either the file needs a
  feature the reader does not implement (an unknown major version, an unknown
  must-understand section), or it goes past one of the reader's own
  implementation limits (section 7.2). Declined is not a verdict on the file.

A *subset check* (section 6a.2) has a fourth outcome, **index invalid**. It
means an INDEX entry the check relied on disagrees with the records. It ends
that subset check only. It is never a verdict on the file.

A structural error in the header, the directory, the trailer or the MAIN
section rejects the file before any declaration is checked. A structural
error inside a proof block is an error of that block's theorem. It is ordered
with the other declaration failures (section 8).

## 3. Encoding primitives

- Fixed-width integers (`u16`, `u32`, `u64`) are little-endian.
- **varint**: unsigned LEB128. Each byte carries 7 bits, low group first. The
  high bit is set on every byte but the last.
  - A varint MUST be minimal. A varint of more than one byte MUST NOT end in
    the byte `0x00`.
  - A varint MUST have at most 10 bytes, and its value MUST be below 2^64.
    The range allows only `0x00` or `0x01` as a 10th byte, and minimality
    rules out `0x00`. So the 10th byte is exactly `0x01`.
  - Every varint field is a u64. Some fields have tighter ranges, stated
    where the field is defined.
- **bool**: one byte, `0x00` or `0x01`. Any other value is an error.
- **enum byte**: one byte. Each field lists its values. Any other value is an
  error.
- **bytes**: a varint length `n`, then `n` bytes.
- **string**: `bytes` that MUST be well-formed UTF-8 (RFC 3629). That means
  no overlong forms, no surrogates and nothing above U+10FFFF. Strings are not
  normalised. NUL is allowed.
- **list**: a varint count `n`, then `n` varints.
- **nat**: a natural number of any size. It is `bytes` holding the number's
  minimal little-endian base-256 digits. Zero is the empty byte string. A
  non-empty one MUST NOT end in `0x00`. Only Nat literals use it (A.2).

A reader never trusts a length or count for allocation. Before it reserves
room, it MUST check that the announced bytes exist. That is `n` bytes for
bytes and strings, and at least `n` bytes for a list or a record count.

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

- `major` is 1 for this document. A reader declines a file with any other
  major.
- Byte 4 of the magic is `0x0D`. That is never a valid internal version byte
  (0, 1, 2), so old and new files cannot be confused. The `\r\n\x1a\n` tail
  catches text-mode corruption, as in PNG.
- There is no `minor` field. New features are announced by sections (A.5,
  A.14).
- `trailer-length` counts the whole trailer, including these last 8 bytes. A
  reader uses it to find the trailer from the end of the file. It MUST equal
  `16 + 4 + 24 * section-count + 8`.
- `counts` holds four numbers. They are the number of names and of levels
  (each including its implicit id 0), of MAIN expressions, and of
  declarations. They MUST equal what the MAIN section defines. Section 7.1
  limits them.
- `flags` bit 0 is **must-understand**. Bits 1-15 MUST be 0.
- Sections MUST tile the body exactly. The first starts at offset 16. Each
  next one starts where the one before ended. The last ends where the trailer
  starts. There are no gaps, no overlap and no bytes outside a section.
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
- If an unknown id has must-understand set, the reader **declines** ("needs
  section N"). The file is not malformed. It is only beyond this reader
  (A.6).
- A reader skips an unknown id without must-understand, and never reads it.
- A reader MAY skip a known informational section it does not use.
- SOURCE never changes the verdict. If a reader parses it and finds bad JSON,
  the reader ignores it and MAY warn.
- INDEX never changes the verdict of a **full check**, which is the check
  that gives the file's verdict. A full check MAY ignore INDEX entirely, at no
  cost.
- A reader that uses INDEX, for a lookup or a subset check, MUST verify every
  entry it relies on against the records. A disagreement gives that reader's
  subset result the outcome **index invalid** (section 6a.3). It never gives
  a full-check verdict.
- The INDEX directory entry itself (id, flags, offset, length) is part of the
  directory. Every reader checks it as such.
- Every reader checks PAD's all-zero rule, so no byte of a canonical file is
  left unconstrained.

## 5. MAIN section

```
main     = record*
record   = name-rec | level-rec | expr-rec | frontier-rec | decl-rec
```

Ids are implicit and dense. Each kind is numbered on its own, in record
order:

- names from 1 (0 is the anonymous name),
- levels from 1 (0 is level zero),
- MAIN expressions from 0,
- declarations from 0.

A name or level field holds the id. An expression field holds a **back
distance** `d`. It names the expression whose id is (next expression id) −
`d`. `1 <= d <= ` (number of expressions defined so far) MUST hold.

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

A name, a level, or an element of a level list MUST be an id that is already
defined. For a name that means below the next name id. For a level it means
below the next level id.

A frontier entry names the item `d` back from the next id of its kind, with
`1 <= d <= ` next id. The implicit id 0 counts. The frontier entries of each
kind are numbered from 0 in record order. An item MUST NOT be listed twice
(A.13).

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

The remaining fields:

- Hints: enum 0 opaque, 1 abbrev, 2 regular. Regular is followed by height:
  varint.
- Safety: 0 safe, 1 unsafe, 2 partial.
- Inductive type: head, unsafe: bool, numParams: varint, numIndices: varint,
  all: list, ctors: list, numNested: varint, isRec: bool, isReflexive: bool.
- Constructor: head, unsafe: bool, induct: name, cidx: varint, numParams:
  varint, numFields: varint.
- Recursor: head, unsafe: bool, all: list, numParams: varint, numIndices:
  varint, numMotives: varint, numMinors: varint, rules, k: bool. The rules are
  a varint count, then that many of (ctor: name, nfields: varint, rhs: back).

**Unique declared names (A.8).** A declaration record declares its head name.
An inductive block declares every type, constructor and recursor name in it.
A name a record declares MUST NOT be declared by an earlier declaration
record, or earlier in the same record. A violation is a structural error at
that record. A name's **declaration index** is the index of the record that
declares it.

Kind 6: `block-length` is the byte length of the theorem's proof block.
`block-exprs` is the number of expression records in it. `1 <= block-exprs
<= block-length / 2` MUST hold, since an expression record takes at least 2
bytes (A.4).

## 6. PROOFS section

```
proofs = block*            ; one per kind-6 declaration, in declaration order
block  = expr-rec{block-exprs}
```

The block of the first kind-6 declaration starts the section. Each next block
starts where the one before ended. The blocks MUST fill the section exactly.
A reader checks this from the MAIN section alone, before it decodes any
block. A block MUST hold exactly `block-exprs` records, all of them
expression records (tags 7-16), and MUST end right after the last one. Its
last expression is the theorem's value.

Inside the block of theorem `T`:

- A name field is a **frontier name index**, and a level field is a
  **frontier level index**. The index MUST be below the number of frontier
  entries of that kind listed in MAIN before `T`'s declaration record.
- Take an expression reference `r` from the block's expression `k` (counting
  from 0). If `1 <= r <= k`, it names the block's expression `k − r`.
  Otherwise it names frontier expression `r − k − 1`, which MUST be below the
  number of frontier expression entries listed before `T`.
- **Declared before (rule P).** The name of every `const` and every `proj`
  record in the block MUST have a declaration index below `T`'s. A violation
  is an error of `T`, like any other structural error of the block
  (section 8). There are no marks and no `placed` flag (Appendix A, R6).

## 6a. INDEX section

INDEX lets a checker find a declaration by name without decoding every proof
block. It serves any checker, and a subset checker in particular ("check
`Foo.bar`", "check namespace `Foo`"). From a name, the checker jumps to the
declaration's record in MAIN and to its proof block. It does not decode MAIN
past what it needs.

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
  declaration kind (0-6).
- `main-delta` is the offset of the record's tag byte minus that of entry
  i−1. For i = 0 it is minus the start of MAIN. Prefix sums give absolute
  offsets.
- `block-length` repeats the value in the kind-6 record. So a proof block's
  offset in PROOFS is the sum of the block lengths before it.
- The name table holds every declared name (section 5.2) exactly once. It is
  sorted by `name-key` bytewise, strictly increasing.
- Keys are front-coded. A key is the first `shared` bytes of the previous key
  (0 for the first key), then `suffix`. `shared` MUST be the full length of
  the common prefix, which makes the coding canonical. `suffix` MUST be
  non-empty.
- `decl` is the index of the declaration that declares the name.
- `decl-count` MUST equal `counts.decls`. `name-count` MUST equal the number
  of declared names.
- MAIN fully decides the content and order of INDEX, so canonical packers
  write identical bytes.
- Keys are the names themselves, not hashes, so rule 1 ("no hashes") holds.
  A lookup is a binary search over the decoded table, or a linear scan of the
  front-coded bytes.

### 6a.2 What a subset checker gets, and what it still must read

With INDEX, finding `Foo.bar` takes reading INDEX only, not MAIN or PROOFS.
It gives declaration i, its record offset, its kind and, for a theorem with a
block, the block's byte range. Each namespace `Foo` is one contiguous run of
the sorted table, because the keys of `Foo.*` start with the key of `Foo`.

A subset checker never decodes proof blocks other than those of the
declarations it checks. INDEX does not save it the following work.

- **The MAIN prefix.** Records only point backwards. So declaration i depends
  only on the MAIN bytes up to the end of its record, plus its block. But
  those bytes are variable-length records (names, levels, shared expressions,
  frontier, earlier declarations) with no per-record offsets. A checker must
  decode **all of MAIN up to declaration i** to build the terms that its
  record and block name. For a declaration late in mathlib that is nearly all
  of MAIN. For one early in the file it is little. Random access into MAIN
  would need an offset per expression, about 4 bytes × 105 M on mathlib. That
  is out of scope.
- **Dependencies.** Only the terms of declaration i show which constants it
  uses. The declarations of those constants all come before i, so the same
  prefix holds them. A subset checker admits them as stated. It may also
  check them, at the cost of a full check of that prefix. Only a checker that
  unfolds theorem values needs the proof blocks of dependencies.

A subset check's result ("`Foo.bar` checks, given the declarations before
it") is not the file's verdict. The rest of the file is not verified. A name
missing from the name table is "not found", which is not a verdict either.

### 6a.3 Verification (rule 1)

A reader that relies on an entry verifies it against the records it reads
anyway, which are the MAIN prefix. It checks that:

- entry i's offset is the tag byte of declaration i's record, and the record
  has the entry's kind;
- `block-length` equals the record's;
- a name entry's key equals the name declared by the record of declaration
  `decl`, as built from the MAIN name records.

On the entries it decodes, it also checks the sort order, the front coding,
and that `shared` is the full common prefix. A disagreement makes the subset
check's outcome **index invalid**. It does not reject the file. A full check
of the same file is unaffected. A full check does not need to read INDEX.

A tool may want to vouch for a whole INDEX, for instance in a packer's
self-test. It checks every entry while it reads MAIN, with one comparison per
declaration. After MAIN it checks the name table once. It decodes the table,
compares each key with the name built for its declaration, and checks strict
order and that every declared name appears once. It reports the result apart
from the verdict.

## 7. Limits

### 7.1 Format limits (normative, implementation-independent)

- Each of the four counts is at most 2^32 − 1, so every id fits a u32 in any
  implementation (A.3). Mathlib today has 105 M expressions, about 40× below
  the limit.
- Every other quantity is bounded only by the u64 range of varints and by the
  file's bytes. There is no format limit on record size, string or literal
  length, block length or block expression count.

### 7.2 Implementation limits

A reader MAY have its own limits, for example on memory, vector sizes or
chunk sizes. When a file goes past one, the reader MUST **decline**, never
reject. The decline MUST depend only on the file bytes. It MUST NOT depend on
timing, worker count or buffering.

A reader may decline while it decodes a proof block lazily. The outcome is
then the earliest event in declaration order. So a failure of an earlier
declaration still makes the file rejected.

Readers SHOULD document their limits. Examples are a cap on a block's
expression count, which `block-exprs` shows before checking starts, or a cap
on a literal's size. A limit that depends on buffering, such as a record that
crosses a chunk boundary, does not depend only on the file bytes. A reader
reads such a record on a slow path instead.

## 8. Errors

A reader reports a structural error with:

- the section, or `header`, `directory` or `trailer`;
- the **absolute byte offset of the first byte of the offending record**, or
  of the field for header, trailer and directory errors;
- the record's number within its section or block, from 1;
- for a proof block, the theorem's name.

Example: `PROOFS @ 18,342,117: block of Foo.bar, record 12: frontier name
9001 not listed before the declaration`.

A reader looks for structural errors in this order: the header, then the
trailer and directory, then the MAIN records in file order. It reports the
first error it finds, before any declaration is checked.

After that come declaration failures, in declaration order. The earliest one
is reported. Within one declaration, the order is:

1. failures to build it (universe parameters named twice),
2. the structural error of its block,
3. failures of checking.

The conformance suite pins the outcome, the error class, the section and the
record offset of each structural error. Messages stay free text (A.12).

## 9. Packing (normative for canonical packers)

A packer MUST write only files that a conformant reader accepts, and MUST be
deterministic. Any accepted layout is a valid Susz file. A simple packer MAY
put every expression in MAIN and write no kind-6 declaration and no PROOFS
section.

A **canonical** packer writes exactly the layout below, so any two canonical
packers produce identical bytes.

- Records are in export order. An expression that only one theorem's value
  reaches, directly or only through other such expressions, goes into that
  theorem's block, in export order. Every other expression stays in MAIN,
  renumbered densely in export order.
- Each frontier entry comes right after the record of the item it lists. If
  the anonymous name and level zero are listed, their entries come first,
  before any record.
- Sections come in this order, in the body and in the directory alike: MAIN
  (id 1), PROOFS (id 2, only when some kind-6 declaration exists), INDEX
  (id 5), SOURCE (id 3). This is not id order.
- INDEX is written by default and left out with `--no-index`. Every
  canonical packer has this option.
- SOURCE is always written. It holds the source export's `meta` object, byte
  for byte as in the export's header line.
- There is no PAD and no private section.
- Canonical bytes are defined per export and INDEX setting. For each setting,
  canonical packers MUST write identical bytes. The files for the two
  settings differ only by the INDEX section and its directory entry.

### 9.1 What packing drops (normative)

A Susz file does not keep the following, and a checker MUST NOT depend on
them.

- `mdata`. The metadata map is dropped and the record is not written. A
  reference to an `mdata` expression is written as a reference to the
  expression it wraps (A.7).
- `letE.nondep`, which only elaboration uses.
- The export's own numeric ids (`in`, `il`, `ie`). Susz numbers items itself,
  and MAIN expression ids differ from the export's.
- Where expressions sit in the export's line order, beyond what section 9
  keeps. Declaration order is kept exactly.

Everything else in a lean4export 3.1 record is kept. A packer MUST refuse an
export record or field it does not know. It never drops one silently.

## 10. Conformance

A conformant **reader** MUST:

1. reject every file that breaks a MUST of sections 3-6 or a "MUST equal"
   check of section 4, and locate the error as in section 8;
2. accept every file that satisfies them (a checker goes on to check it),
   unless it declines for a documented implementation limit or an unknown
   must-understand section;
3. give the same outcome and error location regardless of parallelism, eager
   or lazy decoding, and buffering;
4. allocate no more than a constant times the bytes already validated;
5. treat informational sections as in 4.1. A full check's outcome MUST be the
   same when the content of INDEX is replaced by any bytes of the same
   length. A subset check MUST verify every INDEX entry it relies on, and
   report "index invalid" on a mismatch (section 6a.3).

A conformant **packer** MUST write only accepted files and MUST be
deterministic. A **canonical** packer MUST write the section 9 layout, with
INDEX by default and without it under `--no-index`. Canonical packers MUST
agree byte for byte on every corpus file, for each setting.

## 11. Test vectors and corpus

- **Format.** A vector is `vectors/{accept,reject,decline}/NAME.susz` plus
  `NAME.expect`. The `.expect` file gives the outcome, class, section, offset
  and record number. For an accept vector it gives the counts and a digest of
  the decoded records. Vectors are generated from a small textual assembler
  (`susz-asm`, a dev tool in the reference crate), so each one can be
  reviewed. Every reject vector is one minimal change to an accept vector,
  and is named after the rule it breaks.
- **Accept:** minimal file (one axiom); MAIN-only file (no PROOFS); file with
  blocks; a block naming frontier items of each kind; varint edge values (0,
  127, 128, 2^63, 2^64−1); `nat` 0, 255, 256, 2^64, 2^200; strings with NUL
  and 4-byte UTF-8; unknown informational section; PAD. The declarations in
  every accept vector are valid Lean, so a full checker accepts them and
  reaches the one fault in each reject vector made from them. (Checked with
  Pestka; not yet with Lean's own kernel.)
- **Reject (one or more each):** magic; reserved bytes; trailer length; end
  magic; directory overlap / gap / out of file / duplicate id / bad flags on
  a known id; counts mismatch; non-minimal varint; 11-byte varint; 10th byte
  `0x02`; truncated varint/string/list; bad UTF-8 (overlong, surrogate,
  truncated); non-minimal `nat`; bool 2; each enum out of range; unknown tag
  in MAIN; tag 17; tag 19 or 18 in a block; back distance 0 and past the
  start; name/level id forward; frontier entry back 0, past the start,
  duplicate; blocks not filling PROOFS; block-exprs 0 or > length/2; block
  with fewer/more records; frontier index listed after T; rule P with a
  constant declared after T and with T itself; duplicate declared name
  (across records and inside one block); PAD with a non-zero byte.
- **Decline:** major 2; unknown must-understand section.
- **Corpus.** Every canonical packer packs the test exports and Init, with
  and without `--no-index`. For each setting the files must be
  byte-identical. The two settings must give the same full-check outcome.
  The files must round-trip to the export's records, up to what section 9.1
  drops. Large exports such as mathlib are tested locally; CI runs only the
  vectors.
- **INDEX vectors.** Accept: a file with INDEX, a file without INDEX, and a
  lookup of every declared name in the Init vector that gives the right
  record. Bad INDEX: offset not at a declaration record, kind mismatch,
  block-length mismatch, keys out of order or repeated, `shared` not maximal,
  empty suffix, a declared name missing, a key naming the wrong declaration,
  decl-count mismatch. These are bad-INDEX vectors, which are not reject
  vectors. A full check MUST give the same outcome as for the same file with
  a correct INDEX, or with none. A subset check that relies on the bad entry
  MUST give "index invalid". Accept vectors exist with and without INDEX.
- **Mutations.** The reference crate flips every single byte of the vectors
  and checks that the reader never panics. Fuzzing with cargo-fuzz, and
  comparing two independent readers on mutated files, are planned.

## Appendix A. Choices we made and why

These choices date from 2026-11-12.

| # | question | chosen | not taken |
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
| A.11 | declaration index | INDEX in Susz 1, written by default, `--no-index` omits it; full checks ignore it (section 6a) | no index |
| A.12 | conformance pins error location | yes (section, record offset) | outcome only |
| A.13 | duplicate frontier entries | rejected | allowed |
| A.14 | `minor` version field | none (sections announce features) | u16 minor, informational |

### Why

**R1. Varints.** A varint is minimal, below 2^64, and at most 10 bytes long.
Minimality gives every value exactly one encoding, and a reader checks it
with one byte (the last byte is non-zero). Canonical packing and
byte-identical packers need one encoding per value. The only fields that are
big by nature are Nat literals, and they have their own encoding, `nat`.

A.1: Lean's `Name.num` component is a `Nat` too. We store it as a u64
varint, and a packer refuses a component of 2^64 or more. None exists in
practice, because Lean makes them from counters. The `nat` encoding would
cost one more byte per numeric component.

**R2. Nat literals (A.2).** We chose minimal little-endian bytes. They map
to bignum limbs, decode in linear time, and take half the space of decimal
(Init: 1.9 KB → 1.0 KB). Canonical decimal (no sign, no leading zero, `"0"`
for zero) is easier to read by eye. But a huge decimal literal takes
quadratic time to decode.

**R3. Limits.** Section 7 has one format limit, the u32 counts. Every limit
that comes from an implementation or from buffering is a documented decline.

**R4. Versioning.** The section directory has a must-understand bit. An
unknown must-understand section makes a reader decline (A.6). An unknown
informational section is skipped. Public numbering starts at major 1, with a
new magic (A.5). Susz 1 readers do not read the internal versions 0, 1 and
2. A checker MAY keep reading version 2 during a transition.

**R5. Tag 19.** Tag 19 is only the MAIN frontier entry. Proof blocks have no
tag 19, because they have no marks. Tag 17 is retired (A.7). Block records
are exactly tags 7-16.

**R6. Marks, `placed`, the literal constants.** Susz 1 removes all three
from the format. Rule P (section 6) and unique declared names (section 5.2,
A.8) replace them.

- *Why they existed.* A checker may reorder checking, for instance by
  namespace. It may do so only when every declaration names only constants
  placed before it. Otherwise a declaration could meet cached facts about a
  constant declared after it. A reader sees MAIN records while reading, but
  it does not see a lazy block. So version 2 carried a `placed` bool per
  theorem, verified on decode. It also carried marks, to reproduce the
  ndjson reader's per-line rule exactly.
- *Marks carry nothing on real exports.* We scanned version-2 files written
  by the native packer, without changing them. Every proof block has exactly
  one mark, equal to its own theorem's index. No block has `placed = false`.
  No block names a constant declared at or after its theorem. No block holds
  a literal whose implied constants come later. No frontier item is listed
  twice. Blocks scanned: Init 35,735; etale 12,051; reachability 2,417;
  con-leche 13,588; mathlib 451,917 (3,285 Nat literals in blocks, all after
  `Nat` and the rest).
- *What a checker needs before it checks the block of T.* It needs the
  block's byte range and expression count (from MAIN), the frontier bound at
  T (from MAIN), and a guarantee that the block names only constants
  declared before T. Rule P gives that guarantee as a format rule. A reader
  enforces it at decode time, at the same cost as version 2's `placed` check
  (one comparison per `const` or `proj`).
- *What a malicious file can do without marks and `placed`.*
  - (a) T's block names a constant declared after T. Rule P makes that T's
    error. The kernel would also fail T, since it looks up every constant in
    a theorem's value. So the outcome and its position stay the same. Only
    the message differs.
  - (b) T names a constant X declared before T by a declaration that the
    checker skips (an unsafe one). Later, X is declared again, safely. With
    reordering, T could meet facts about the second X. A checker that skips
    unsafe declarations admits such a redeclaration, because skipped names
    are not in its environment. Lean rejects the duplicate, so this also
    diverges from Lean. Unique declared names (A.8) closes this hole in the
    format. The alternative was a checker that refuses to reorder when a
    name is declared twice, which it can compute from MAIN.
  - (c) T's block uses a literal before `Nat`, `String` and the rest are
    declared. Which constants a literal stands for is kernel knowledge, so
    it stays out of the format. For a Lean kernel they are `Nat`, `String`,
    `String.ofList`, `List`, `Char` and `Char.ofNat`.
- *A.9.* The checker computes from MAIN the index L of the declaration that
  places the last of its literal constants. L is infinite if one of them is
  missing. The checker checks declarations up to L in file order, then
  reorders the rest. Every T after L has the literal constants placed before
  it, so no per-block information is needed. The cost is that the prelude of
  Init and mathlib (hundreds of declarations) stays sequential. One
  alternative is to check a block that breaks the literal rule with its
  worker's caches emptied before and after. That needs an audit showing that
  no other state the worker carries depends on the environment. Another is
  to fail T. That diverges from the kernel when only `String` is needed but
  `Char.ofNat` comes later.
- *Placement in MAIN* stays a checker computation, not a format rule. Unsafe
  definitions may name themselves, and a format rule of "declared before
  use" would reject them.
- *Checks that would settle the remaining doubt.*
  1. The scan of version-2 files. It is done on mathlib and con-leche, with
     0 violations. It has not been run on cslib.
  2. Adversarial files for (a), (b) and (c). Each is checked with reordering
     forced and in file order, and both runs must give the same outcome.
  3. For A.9's isolation alternative: list every map a worker carries across
     declarations, and mark whether it depends on the environment.

**R7. meta (A.10).** The informational SOURCE section keeps `meta` as
verbatim JSON. That keeps provenance without loss. No reader needs a JSON
parser, and the verdict never depends on it. The Susz major version fixes
what the records mean. lean4export's `format.version` does not. A packer
checks that it understands the source version. Binary fields (exporter
version, Lean version, githash) would lose unknown keys.

**R8. Errors.** An error gives the byte offset of the record start, plus the
section and the record number (section 8).

**R9. INDEX (A.11).** INDEX is in Susz 1 (section 6a), for other checkers and
for checking part of a file. Packers write it by default, and `--no-index`
leaves it out. It is informational. A full check ignores it, and the verdict
never depends on it. A reader that relies on an entry verifies it. A bad
entry gives that reader's subset check the outcome "index invalid". INDEX
finds a declaration and its block by name without decoding proof blocks.
Checking still needs the MAIN prefix before the declaration (section 6a.2).
Appendix B gives the size cost.

**R10. Several files.** Susz 1 does not cover this. One possible design
follows. A must-understand IMPORTS section lists each imported file by a
content hash and its four counts. A file's ids (names, levels, expressions,
declarations) continue after those of its imports. MAIN back distances can
reach into imported MAIN expressions. Rule P and unique names range over all
the files together. Two questions stay open: how the frontier works across
files, and whether imports form a DAG or a chain.

**R11. Lossy choices.** Section 9.1 states them.

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

Without INDEX, measured on version-2 files from the native packer:

- Init 34.57 MB, −0.49%
- etale 11.71 MB, −0.42%
- reachability 1.94 MB, −0.50%
- con-leche 53.97 MB, −0.12%
- mathlib 639.6 MB, −0.36% (marks 1.80 MB, bools 0.45 MB, literals 0.08 MB)

INDEX, estimated from the same files as entries plus front-coded name table:

- Init: 0.20 + 0.98 MB = +3.40%
- con-leche: 0.09 + 0.41 MB = +0.93%
- mathlib: 2.63 + 12.99 MB = 15.6 MB, +2.44%. That covers 718,577 declared
  names, about 18 bytes per name in the table, from 34.3 MB of unencoded
  keys.

Net, Susz 1 against version 2 is +2.9% on Init and +2.1% on mathlib. The
name table is 83% of INDEX on mathlib. Storing name ids instead of keys
would mean decoding MAIN for every lookup, which defeats the purpose. So
the keys stay.
