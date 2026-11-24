# Susz 1

Version: Susz 1 (major 1), 2026-11-12; revised 2026-11-24 (flagged
inductive blocks, Appendix C) and 2026-11-24 (blocks without
`isReflexive`, Appendix D).

Susz (`.susz`) is a binary form of a Lean 4 kernel export. It holds the
records of a lean4export 3.1 or 3.2 ndjson file, with no text to parse. A proof that
only one theorem uses sits in a block of its own.

This document defines Susz 1, the first public version. The earlier internal
versions (0, 1 and 2) are not Susz 1, and a Susz 1 reader does not read them.

MUST, MUST NOT, SHOULD and MAY are used as in RFC 2119.

Sections 1 to 10 are normative. Section 11 describes the test vectors.
Appendix A lists the choices we made and why. The text refers to them as A.1
to A.15. Appendix B lists the changes from internal version 2. Appendix C
lists the 2026-11-24 revision, Appendix D the second one of that day.
[`OPEN.md`](OPEN.md) tells which questions came up while implementing. Their
answers are now part of the sections below.

## 1. Rules

1. A reader trusts nothing in the file. The file stores the records and
   nothing computed from them: no hashes, no ranges of loose bound variables,
   no flags. (The five flags of a flagged inductive block, section 5.2, are
   not computed by the packer: they are fields of the export's records, and
   the kernel takes them as input.) Sizes, offsets and counts are there only
   to help reading, and a reader checks each of them against the records. If one is wrong, the file
   is rejected. A reader says `accepted` only after it has read and checked
   the whole file.
2. The order of the declaration records decides when each declaration enters
   the environment, and what "declared before" means everywhere in this
   spec. Nothing else in the layout does.
3. Which expressions sit in proof blocks, and where the sections are, can
   make a file faster or slower to read. It never changes the verdict.
4. The outcome of a full check depends only on the file bytes, not counting
   the content of the INDEX section. So does where the reported error is
   (section 8). Neither changes with the number of workers, with decoding
   proof blocks eagerly or lazily, or with whether the reader looks at INDEX.
5. For a given export, with INDEX on or off, every canonical packer writes
   the same bytes (section 9).

## 2. Outcomes

A reader gives exactly one of three outcomes.

- **accepted**: the file is well-formed and no declaration fails. For a
  checker, every declaration was also admitted.
- **rejected**: the file is malformed, or a declaration fails.
- **declined**: the reader cannot judge the file. Either the file needs a
  feature the reader does not implement (an unknown major version, an unknown
  must-understand section), or it goes past one of the reader's own
  implementation limits (section 7.2). Declined is not a verdict on the file.

A file can fail in three ways.

1. A **structural error** means the file is malformed. It breaks a MUST of
   sections 3 to 6 or a "MUST equal" check of section 4, other than rule P.
   Bad INDEX content (section 6a) never is one. A file with no structural
   error is **well-formed**. A packer MUST write only well-formed files
   (section 9).
2. A **declaration failure found without types** is the failure of one
   declaration that a reader sees in the records alone. Susz 1 has one such
   rule, rule P (section 6). The file is still well-formed. The failure comes
   from the export, and a packer writes it as it is.
3. A **kernel failure** is the failure of one declaration that a checker
   finds by type checking. A reader that only checks structure does not look
   for these.

A reader reports a failure of kind 2 or 3 as the failure of that
declaration, not as a malformed file. The outcome is still rejected.

A *subset check* (section 6a.2) has a fourth outcome, **index invalid**. It
means an INDEX entry the check relied on disagrees with the records. It ends
that subset check only. It is never a verdict on the file.

A structural error in the header, the directory, the trailer or the MAIN
section rejects the file before any declaration is checked. A structural
error inside a proof block also makes the file malformed. But a lazy reader
only sees it when it decodes the block, so it is ordered with the failures of
that block's theorem (section 8).

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
| 6 | FLAGS | yes | iff some kind-7 or kind-8 declaration exists (then no kind-5 one does) | none: the section MUST be empty (length 0) |
| 7 | NOREFL | yes | iff some kind-8 declaration exists (then no kind-5 or kind-7 one does) | none: the section MUST be empty (length 0) |
| 8..0x7FFF | reserved | | | |
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
- FLAGS announces flagged inductive blocks (kind 7, section 5.2). It carries
  no bytes: its directory entry is the announcement. Because it is
  must-understand, a reader written before this revision declines a file
  with kind-7 records ("needs section 6") instead of rejecting it for an
  unknown declaration kind. A FLAGS section of non-zero length is a
  structural error (class `flags-section`) at its entry's length field. A
  kind-7 record in a file without FLAGS, a kind-5 record in a file with
  FLAGS, and FLAGS in a file without a kind-7 record, are structural errors
  of the same class (section 8.1). So with FLAGS every inductive block is
  kind 7 (or kind 8, below), and without it every one is kind 5.
- NOREFL announces inductive blocks whose types do not carry `isReflexive`
  (kind 8, section 5.2). Like FLAGS it carries no bytes and is
  must-understand, so a reader written before it declines such a file
  ("needs section 7"). A NOREFL section of non-zero length is a structural
  error (class `flags-section`) at its entry's length field. A kind-8
  record in a file without NOREFL, a kind-5 or kind-7 record in a file with
  NOREFL, and NOREFL in a file without a kind-8 record, are structural
  errors of the same class (section 8.1). A kind-8 block is flagged, so a
  file with NOREFL has FLAGS too, and every inductive block in it is
  kind 8.

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
| 7 | flagged inductive block | as kind 5, each type followed by its five flags |
| 8 | flagged inductive block without `isReflexive` | as kind 7, each type without its `isReflexive` byte |

The remaining fields:

- Hints: enum 0 opaque, 1 abbrev, 2 regular. Regular is followed by height:
  varint.
- Safety: 0 safe, 1 unsafe, 2 partial.
- Inductive type: head, unsafe: bool, numParams: varint, numIndices: varint,
  all: list, ctors: list, numNested: varint, isRec: bool, isReflexive: bool.
  In a kind-7 record each type goes on with its flags, five bools in this
  order: isImpredicative, isK, hasProjections, hasEta, hasLargeElim. Nothing
  else differs between kinds 5 and 7: constructors and recursors are written
  alike. A kind-8 record is a kind-7 record whose types leave out
  `isReflexive`: after isRec come the five flags.
- Constructor: head, unsafe: bool, induct: name, cidx: varint, numParams:
  varint, numFields: varint.
- Recursor: head, unsafe: bool, all: list, numParams: varint, numIndices:
  varint, numMotives: varint, numMinors: varint, rules, k: bool. The rules are
  a varint count, then that many of (ctor: name, nfields: varint, rhs: back).

**Flagged blocks.** lean4export 3.2 (the kernel renovation, lean4#16595)
gives every inductive type five flags, which the kernel takes as input: it
checks that each one is allowed for the type and does not recompute them.
A kind-7 block carries them, a kind-5 block does not. The two are different
declarations: "no flags" (a checker decides as before the renovation) is not
"every flag off". The flags belong to the block as a whole, so its types
either all carry them (kind 7) or none does (kind 5). The same holds for
the file: with FLAGS every inductive block is kind 7, without it every one
is kind 5 (section 4.1). A kernel never checks one environment by two sets
of rules, such as an `Acc` with large elimination admitted by the old rules
next to types whose flags were checked by the new ones. A recursor may have
no rules (`rules` count 0), in either kind: with the flags, a recursor that
eliminates only into `Prop` (no `hasLargeElim`) has none. The format checks
no relation between the flags, the recursors' `k` and the rest; that is the
kernel's job.

**Blocks without `isReflexive`.** `isReflexive` says whether some
constructor of the block has a field whose type is a function into a type of
the block. It is no input of the kernel: the kernel computes it while it
checks the constructors (on the block with its nested types eliminated),
and checkers compare their own value with the export's. Lean dropped the
field from `InductiveVal` with the renovation (lean4#16595), and its
exports no longer write it. A kind-8 block keeps what such an export
says, and nothing more: its types have no `isReflexive`, and a checker
computes it and has nothing to compare it with. Kinds 5 and 7 keep the
value the export gave, which a checker still compares. "Not given" is not
"false". As with the flags, a file is one or the other as a whole: with
NOREFL every inductive block is kind 8 (section 4.1). Only flagged blocks
come without it, because only the renovation's exports leave it out; an
unflagged block without `isReflexive` has no kind.

**Name equality.** MAIN may hold two name records for the same name. Two
names are equal when both are the anonymous name, or when their prefixes are
equal and their last components are equal (the same string bytes, or the
same number). Unique declared names, rule P and INDEX keys all compare names
this way, never by name id.

**Declared names (A.8).** A declaration record declares its head name. An
inductive block declares every type, constructor and recursor name in it.

- A name a record declares MUST NOT be the anonymous name.
- A name a record declares MUST NOT be declared by an earlier declaration
  record, or earlier in the same record.

A violation of either is a structural error at that record. A name's
**declaration index** is the index of the record that declares it.

Kind 6: `block-length` is the byte length of the theorem's proof block.
`block-exprs` is the number of expression records in it. `1 <= block-exprs
<= block-length / 2` MUST hold, since an expression record takes at least 2
bytes (A.4). `block-exprs <= 2^32 − 1` MUST hold too (section 7.1). A reader
checks both in the record, before it decodes any block, so the result is the
same for eager and lazy decoding.

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
  record in the block MUST have a declaration index below `T`'s. Names are
  compared by value (section 5.2). A violation is a declaration failure of
  `T`, not a structural error (section 2). It is found in byte order
  together with the structural errors of the block (section 8). There are no
  marks and no `placed` flag (Appendix A, R6).

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
  declaration kind (0-8).
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
- Expanded keys can be much larger than INDEX. A chain of names `a`, `a.a`,
  `a.a.a` and so on expands to a size that grows with the square of the
  section's length. A reader MUST still keep within section 10, item 4. The
  reference reader keeps expanded keys only while their total stays below 8
  bytes per INDEX byte (mathlib needs about 2.6), and scans the front-coded
  table past that. Both give the same answers.

### 6a.2 What a subset checker gets, and what it still must read

With INDEX, finding `Foo.bar` takes reading INDEX only, not MAIN or PROOFS.
It gives declaration i, its record offset, its kind and, for a theorem with a
block, the block's byte range. Each namespace `Foo` is one contiguous run of
the sorted table, because the keys of `Foo.*` start with the key of `Foo`.

So the cost of one lookup is decoding INDEX, one binary search, and the MAIN
prefix up to the declaration (see below). The search is the cheap step. A
reader that does many lookups decodes INDEX once and keeps its MAIN reader's
state between them. Then lookups in declaration order read MAIN once in all.

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
- `block-exprs` is at most 2^32 − 1 as well, so an expression's index inside
  its block fits a u32 too. Breaking it is a structural error at the kind-6
  record (section 5.2).
- Every other quantity is bounded only by the u64 range of varints and by the
  file's bytes. There is no format limit on record size, string or literal
  length, or block length.

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
on a literal's size. The reference reader has one: a string component of a
name must be shorter than 2^32 − 2 bytes. A limit that depends on buffering, such as a record that
crosses a chunk boundary, does not depend only on the file bytes. A reader
reads such a record on a slow path instead.

## 8. Errors

A reader reports a structural error or a declaration failure found without
types with:

- the section, or `header`, `directory` or `trailer`;
- the **absolute byte offset of the first byte of the offending record**, or
  of the field for header, trailer and directory errors;
- the record's number within its section or block, from 1 (for the
  directory, the entry's number from 1; 0 where there is no record);
- for a proof block, the theorem's name.

Example: `PROOFS @ 18,342,117: block of Foo.bar, record 12: frontier name
9001 not listed before the declaration`.

### 8.1 Before any declaration

A reader looks for structural errors in this order and reports the first one
it finds.

1. The header: magic, length, major (a decline), the reserved fields.
2. The trailer: end magic, the range of the trailer length, the trailer
   length against the section count.
3. The directory, entry by entry: the reserved field, the flag bits, the
   flags of a known id, a duplicate id, the start offset (tiling), the end
   within the body. Then a gap before the trailer, then a missing MAIN. Only
   then a decline for an unknown must-understand section, the first one in
   directory order. So a file with a malformed directory is rejected, even
   if it also needs an unknown section.
4. FLAGS's and NOREFL's lengths (they MUST be 0), at the entry's length
   field, the first such entry in directory order. Then PAD's
   all-zero rule, at the first non-zero byte.
5. The MAIN records, in file order. Inside one record, the first broken
   field in byte order. A declared name is checked for being anonymous or
   declared twice when its name field is read, before the fields after it.
   A kind-6 record whose block would run past the end of PROOFS, or that has
   no PROOFS section at all, is an error at that record, of class
   `proofs-fill`. A kind-7 or kind-8 record in a file without FLAGS, a
   kind-5 record in a file with FLAGS, a kind-8 record in a file without
   NOREFL, and a kind-5 or kind-7 record in a file with NOREFL, are errors
   at that record, of class `flags-section`, found right after its kind
   byte. The NOREFL rules are checked before the FLAGS ones.
6. After the last MAIN record, the trailer counts: the first one that
   differs from what MAIN defines (names, levels, expressions,
   declarations), at that count. Before this point a reader uses the counts
   only as allocation hints, capped by MAIN's length.
7. Then FLAGS without any kind-7 or kind-8 record: class `flags-section`,
   at FLAGS's offset (record number 0). Then NOREFL without any kind-8
   record, likewise at NOREFL's offset.
8. Then the rest of the PROOFS fill. A PROOFS section with no kind-6 record
   (even of length 0) is an error at its first byte. A PROOFS section longer
   than its blocks is an error at the first byte after the last block.

Header, trailer, PAD, counts and PROOFS fill errors have record number 0.

### 8.2 Declarations

After that come declaration failures, in declaration order. The earliest one
is reported. Within one declaration, the order is:

1. failures to build it (universe parameters named twice),
2. the errors of its block, in byte order: its structural errors and rule P
   alike,
3. kernel failures.

A block with the wrong number of records gives one of these:

- fewer records than `block-exprs`: class `block-count` at the block's end,
  with record number = records found + 1;
- bytes left after `block-exprs` records: class `block-count` at the first
  byte left, with record number `block-exprs` + 1;
- a record cut off by the block's end: class `truncated` at the record's
  start.

The conformance suite pins the outcome, the error class, the section and the
record offset of each error. Messages stay free text (A.12).

## 9. Packing (normative for canonical packers)

A packer MUST write only well-formed files (section 2), and MUST be
deterministic. Any well-formed layout is a valid Susz file. A simple packer
MAY put every expression in MAIN and write no kind-6 declaration and no
PROOFS section.

A packer writes every export it can represent. It does not fix or hide the
export's own failures. If a theorem's proof names a constant declared after
the theorem, the canonical file breaks rule P in that theorem's block. The
packer writes it, and a reader reports that theorem's failure. An export
that no well-formed file can hold is refused (section 9.2).

A **canonical** packer writes exactly the layout below, so any two canonical
packers produce identical bytes.

- Records are in export order. An expression that only one theorem's value
  reaches, directly or only through other such expressions, goes into that
  theorem's block, in export order. Every other expression stays in MAIN,
  renumbered densely in export order.
- Each frontier entry comes right after the record of the item it lists. If
  the anonymous name and level zero are listed, their entries come first,
  before any record.
- Sections come in this order, in the body and in the directory alike:
  FLAGS (id 6, only when some kind-7 or kind-8 declaration exists; empty,
  so it starts at offset 16, where MAIN starts), NOREFL (id 7, only when
  some kind-8 declaration exists; empty, at offset 16 too), MAIN (id 1), PROOFS (id 2, only when
  some kind-6 declaration exists), INDEX (id 5), SOURCE (id 3). This is not
  id order.
- An inductive block whose types carry the five flags in the export is
  written as kind 7, or as kind 8 when they do not carry `isReflexive`; any
  other as kind 5. A packer never adds or computes flags or
  `isReflexive`, and never drops them. Since the types of an export carry
  flags all or none, and `isReflexive` all or none (section 9.2), a packed
  file has only kind-8 blocks (with FLAGS and NOREFL), only kind-7 blocks
  (with FLAGS), or only kind-5 blocks (with neither).
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
  expression it wraps (A.7). A packer reads an `mdata` record with or without
  its `data` key (lean4export writes it, some other exporters do not).
- `letE.nondep`, which only elaboration uses.
- The export's own numeric ids (`in`, `il`, `ie`). Susz numbers items itself,
  and MAIN expression ids differ from the export's.
- Where expressions sit in the export's line order, beyond what section 9
  keeps. Declaration order is kept exactly.

Everything else in a lean4export 3.1 or 3.2 record is kept, the flags of
3.2 included. A packer MUST refuse an
export record or field it does not know. It never drops one silently.

### 9.2 Packer input (normative)

A packer reads lean4export 3.1 or 3.2 ndjson, one JSON object per line. Two packers
that write the same bytes must also agree on which inputs they pack, so the
accepted dialect is fixed here.

- The first line MUST be exactly `{"meta":M}`. M is kept byte for byte as
  SOURCE. Its `format.version` MUST be 3.1.x or 3.2.x.
- Integers are non-negative. Leading zeros are allowed.
- Strings may hold raw control characters.
- An object may end with a trailing comma. An array may not.
- Every other line is one record with exactly the keys of its lean4export
  3.1 kind. An object in `inductive.types` may also have the five keys of
  3.2, `isImpredicative`, `isK`, `hasProjections`, `hasEta` and
  `hasLargeElim` (booleans): all five or none. If one inductive type of the
  export carries them, every one MUST.
- Flags are read where they are, not by the version: a 3.1.x export whose
  types carry them packs as a 3.2.x one does, but for SOURCE. The version
  only adds one rule: in a 3.2.x export every inductive type MUST carry its
  flags. A 3.2.x export with a type without them is refused, not packed as
  a block without flags.
- An object in `inductive.types` that carries the five flags may leave out
  `isReflexive`, as Lean's exports do since lean4#16595 (under either
  version). If one inductive type of the export leaves it out, every one
  MUST. A type without the flags MUST carry it, as before.

A packer refuses an input in one of two classes. The `susz` tool exits with
1 or 2.

- **Not a valid export** (exit 1). The input breaks lean4export's own rules,
  or no well-formed file can hold it. Examples are malformed JSON, a line cut
  short, a missing or repeated key, a negative number, an id defined twice or
  used before it is defined, a name declared twice (compared by value), a
  declaration of the anonymous name, an empty input, an inductive type with
  some of the five flag keys but not all, inductive types with and without
  flags in one export (in one block or in different blocks), an inductive
  type without its flags in a 3.2.x export, inductive types with and
  without `isReflexive` in one export (in one block or in different
  blocks), and an inductive type without `isReflexive` and without flags.
- **Cannot pack** (exit 2). The input may be a fine export, but this packer
  cannot write it. Examples are a header in another form, another
  `format.version`, a record kind or key outside lean4export 3.1 and 3.2, a number
  that does not fit a u64 (a `Name.num` component, a bound variable index, a
  projection index), more than 2^32 − 1 names, levels, expressions or
  declarations, a packer's own limit, and I/O errors.

### 9.3 Digest

The digest says which declarations a file holds, so that a Susz file can be
checked against the export it was packed from, or two files of either form
against each other. It replaces the 64-bit digest of earlier releases of
the reference crate, which had no per-declaration form and a weak hash. A
reader does not need it; a tool that prints a Susz digest MUST compute it
as follows, from Susz or from lean4export 3.1 or 3.2 ndjson alike. A tool
reading ndjson refuses what a packer refuses (section 9.2), so a 3.2.x
export with a type without flags has no digest.

It is computed on structure. Ids, line order, the Susz layout (MAIN or
proof block, frontier, INDEX, SOURCE, PAD) do not count, and neither does
what section 9.1 drops: an `mdata` expression has the hash of the
expression it wraps, and `letE.nondep` is not hashed. Everything else in a
declaration counts, and so does the order of the declarations.

**Hashes.** `SHA256` is SHA-256 (FIPS 180-4). The hash of a name, a level
or an expression, a **node hash**, is the first 16 bytes of `SHA256(enc)`.
A declaration digest is the whole 32 bytes of `SHA256(enc)`. The **file
digest** is `SHA256(d0 ‖ d1 ‖ … ‖ dn−1)`, the declaration digests (32 bytes
each) in declaration order; for no declaration it is `SHA256("")`. Tools
print digests as lowercase hex.

**Encoding.** `enc` is a tag byte, then the fields in the order given. A
field is one of:

- `u8`: one byte (binder, a bool as `0x00`/`0x01`, an enum);
- `u64`: 8 bytes, little-endian;
- `h`: the 16-byte node hash of the name, level or expression referred to;
- `bytes`: a `u64` length, then the bytes;
- `hs`: a `u64` count, then that many `h`.

| tag | node | fields |
| --- | --- | --- |
| `0x01` | anonymous name | none |
| `0x02` | name `str` | prefix: h, component: bytes (UTF-8) |
| `0x03` | name `num` | prefix: h, component: u64 |
| `0x10` | level zero | none |
| `0x11` | `succ` | h |
| `0x12` | `max` | h, h |
| `0x13` | `imax` | h, h |
| `0x14` | `param` | name: h |
| `0x20` | `bvar` | index: u64 |
| `0x21` | `sort` | level: h |
| `0x22` | `const` | name: h, levels: hs |
| `0x23` | `app` | fn: h, arg: h |
| `0x24` | `lam` | binder: u8, name: h, type: h, body: h |
| `0x25` | `forallE` | binder: u8, name: h, type: h, body: h |
| `0x26` | `letE` | name: h, type: h, value: h, body: h |
| `0x27` | `natVal` | value: bytes, the canonical decimal |
| `0x28` | `strVal` | value: bytes (UTF-8) |
| `0x29` | `proj` | struct: h, field: u64, expr: h |

Binder: 0 default, 1 implicit, 2 strict implicit, 3 instance implicit, as in
section 5.1 (ndjson `default`, `implicit`, `strictImplicit`,
`instImplicit`). Strings are hashed as their UTF-8 bytes, without
normalising. The **canonical decimal** of a Nat literal is its ASCII
digits, with no sign and no leading zero, and `0` for zero. On the ndjson
side it is the `natVal` text with its leading zeros removed (one `0` stays
for zero); on the Susz side, the `nat` bytes written in decimal. A name
anywhere is hashed by value, so two Susz name records for the same name
(section 5.2) have the same hash.

Declarations, where `head` is name: h, levelParams: hs, type: h:

| tag | declaration | fields |
| --- | --- | --- |
| `0x40` | axiom | head, isUnsafe: u8 |
| `0x41` | definition | head, value: h, hints, safety: u8, all: hs |
| `0x42` | theorem | head, value: h, all: hs |
| `0x43` | opaque | head, value: h, isUnsafe: u8, all: hs |
| `0x44` | quotient | head, kind: u8 (0 type, 1 ctor, 2 lift, 3 ind) |
| `0x45` | inductive block | types: u64 count, then each type; ctors: u64 count, then each constructor; recs: u64 count, then each recursor |
| `0x47` | flagged inductive block (kind 7) | as `0x45`, each type with its flags |
| `0x48` | flagged inductive block without `isReflexive` (kind 8) | as `0x47`, each type without isReflexive |

- Hints: `0x00` opaque, `0x01` abbrev, or `0x02` then height: u64
  (regular).
- Safety: 0 safe, 1 unsafe, 2 partial.
- Inductive type: head, isUnsafe: u8, numParams: u64, numIndices: u64, all:
  hs, ctors: hs, numNested: u64, isRec: u8, isReflexive: u8. In a flagged
  block (`0x47`) it goes on with isImpredicative: u8, isK: u8,
  hasProjections: u8, hasEta: u8, hasLargeElim: u8. In a `0x48` block
  isReflexive is left out: the flags follow isRec.
- Constructor: head, isUnsafe: u8, induct: h, cidx: u64, numParams: u64,
  numFields: u64.
- Recursor: head, isUnsafe: u8, all: hs, numParams: u64, numIndices: u64,
  numMotives: u64, numMinors: u64, rules: u64 count then each rule as
  ctor: h, nfields: u64, rhs: h; then k: u8.

A theorem whose proof sits in a block (kind 6) is a theorem, tag `0x42`,
whose value is the block's last expression. The fields follow section 5.2,
so the Susz side reads them in record order; an ndjson object's keys come
in any order and are put in this one.

A file that is malformed, or an export that is not valid, has no digest. A
Susz file that breaks rule P (section 6) has one: the rule is about the
declarations, not about how they are written.

**Example.** The anonymous name is the first 16 bytes of `SHA256(01)`,
`4bf5122f344554c53bde2ebb8cd2b7e3`. The name `Nat` is the first 16 bytes of
`SHA256(02 ‖ anon ‖ 03 00 00 00 00 00 00 00 ‖ "Nat")`,
`68a9193ec9256ad58b3ddf294e10ce13`.

Section 9.4 defines a second digest, the kernel digest. Where a digest is
not qualified, it is this one, the exact digest.

### 9.4 Kernel digest

The kernel digest compares what a kernel checks. Two exports of one Lean
build by different exporters can differ in metadata that no kernel looks
at: binder names, binder info, the order in which an inductive block lists
its recursors. Their exact digests differ; their kernel digests do not. A
tool that prints a kernel digest MUST compute it as follows, and MUST label
it as the kernel digest wherever it could be taken for the exact one.

It is the exact digest of section 9.3, with these changes and no others.

**Binders.** A binder is hashed without its name and, for `lam` and
`forallE`, without its binder info. These nodes have tags of their own:

| tag | node | fields |
| --- | --- | --- |
| `0x2a` | `lam` | type: h, body: h |
| `0x2b` | `forallE` | type: h, body: h |
| `0x2c` | `letE` | type: h, value: h, body: h |

Every other name, level and expression node is hashed as in section 9.3,
so a node with no binder in it has the same hash in both digests.

**Declarations.** A declaration's tag is its section 9.3 tag plus `0x10`:
`0x50` axiom, `0x51` definition, `0x52` theorem, `0x53` opaque, `0x54`
quotient, `0x55` inductive block, `0x57` flagged inductive block, `0x58`
flagged inductive block without `isReflexive`. (The
flagged block's exact tag is `0x47`, not `0x46`, so that its kernel tag
is not `0x56`, the recursor's node tag below.) The fields are those of section 9.3,
except the recursors of an inductive block.

**Recursors.** An inductive block's recursors are hashed as a set. Each
recursor's node hash is the first 16 bytes of `SHA256(0x56 ‖ fields)`,
where the fields are the recursor's fields of section 9.3 (head, isUnsafe,
all, numParams, numIndices, numMotives, numMinors, rules, k). The block's
encoding ends with these node hashes sorted in ascending byte order, as
`hs`, in place of the recursors:

| tag | declaration | fields |
| --- | --- | --- |
| `0x55` | inductive block | types: u64 count, then each type; ctors: u64 count, then each constructor; recs: hs, sorted |
| `0x57` | flagged inductive block | as `0x55`, each type with its flags as in section 9.3 |
| `0x58` | flagged inductive block without `isReflexive` | as `0x57`, each type without isReflexive as in section 9.3 |

A block's recursors have distinct names (section 5.2), so their node
hashes differ unless SHA-256 collides, and sorting them gives one order.

The file digest is `SHA256(d0 ‖ d1 ‖ … ‖ dn−1)` over the kernel
declaration digests, in declaration order, as in section 9.3. The tags
keep the two digests apart: a declaration never has the same digest in
both, and neither does a file with a declaration in it (a file with none
has `SHA256("")` in both).

**What is left out, and why.** A kernel identifies a bound variable by its
de Bruijn index, never by the binder's name, and it type checks and
compares terms without binder info (Lean's own `Expr.eqv` ignores both).
It finds a recursor by its name: the order of the `recs` list says nothing
the names do not (the auxiliary recursors of a nested inductive, `rec_1`,
`rec_2`, …, are numbered by name, and exporters list them in different
orders).

**What still counts, and why.** Everything else, notably:

- The names of declarations, constants, projections' structures,
  constructors in rules and in `ctors` and `all` lists: a kernel looks
  declarations up by name.
- Level parameter names and their order. They are binders too, but `param`
  levels refer to them by name; leaving them out would need renaming up to
  alpha over level parameters, which this digest does not do.
- The order of a block's `types` (the mutual block's order: it fixes the
  order of the motives of its recursors) and of its `ctors`, and of each
  type's `ctors` list (a constructor's index, `cidx`, and the order of the
  minor premises). The block's `ctors` list repeats what the types' lists
  and `cidx` say, but it stays ordered, as in section 9.3: the exporters
  we know write it in one order, so keeping it costs no false difference.
- The order of each recursor's `rules`, which follow the constructors.
- The `all` lists, in order, of every declaration. For an inductive type
  and a recursor, it is the mutual block in its order. For a definition,
  theorem or opaque it names the mutual group the declaration was checked
  with; a kernel does not need its order, but a different list is a
  different declaration, and the exporters we know agree on it.
- Reducibility hints, safety, `isUnsafe`, `k`, the numbers of parameters,
  indices, motives, minors, fields and nested types, `isRec` and
  `isReflexive`, the five flags of a flagged block (and whether a block has
  flags at all), and the quotient kind: a kernel either checks them or
  acts on them.
- The order of the declarations: a kernel checks them in that order.
- Nat and String literals as written: a literal is not unfolded to
  constructors.

What section 9.1 drops (`mdata`, `letE.nondep`) is left out of both
digests.

**Example.** `fun (x : Nat) => x` with any binder name and binder info:
`const Nat` is the first 16 bytes of `SHA256(22 ‖ h(Nat) ‖ 00 00 00 00 00
00 00 00)`, `e3af5a8ee0166bc38c922f6f183a7e1d`, in both digests; `bvar 0`
is `b524830fb1b95fef6024db23ac1d140a`. The `lam` is the first 16 bytes of
`SHA256(2a ‖ h(const Nat) ‖ h(bvar 0))`,
`e4265d6a97e21249b25637451d17621e`. Its exact hash with the name `x` and
the default binder is `e3d53cb12a1829152fe919aa0a80ac9d`.

## 10. Conformance

A conformant **reader** MUST:

1. reject every file that breaks a MUST of sections 3-6 or a "MUST equal"
   check of section 4, and locate the error as in section 8. A rule P
   violation is reported as a declaration failure (section 2);
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

A conformant **packer** MUST write only well-formed files, MUST be
deterministic, and MUST accept and refuse inputs as in section 9.2. A
**canonical** packer MUST write the section 9 layout, with INDEX by default
and without it under `--no-index`. Canonical packers MUST agree byte for
byte on every corpus file, for each setting.

## 11. Test vectors and corpus

- **Format.** A vector is `vectors/{accept,reject,decline}/NAME.susz` plus
  `NAME.expect`. The `.expect` file gives the outcome, class, section, offset
  and record number. For an accept vector it gives the counts and the file
  digest of its declarations (section 9.3). Vectors are generated from a small textual assembler
  (`susz-asm`, a dev tool in the reference crate), so each one can be
  reviewed. Every reject vector is one minimal change to an accept vector,
  and is named after the rule it breaks.
- **Accept:** minimal file (one axiom); MAIN-only file (no PROOFS); file with
  blocks; a block naming frontier items of each kind; varint edge values (0,
  127, 128, 2^63, 2^64−1); `nat` 0, 255, 256, 2^64, 2^200; strings with NUL
  and 4-byte UTF-8; unknown informational section; PAD; a flagged inductive
  block with FLAGS; flagged blocks without `isReflexive` with FLAGS and
  NOREFL. The declarations in
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
  (across records and inside one block); a declaration of the anonymous name;
  `block-exprs` of 2^32; PAD with a non-zero byte; a kind-7 record without
  FLAGS; a kind-5 record with FLAGS; FLAGS without a kind-7 record; FLAGS
  not empty; a flag byte 2; a kind-8 record without NOREFL; a kind-8
  record without FLAGS; a kind-7 record with NOREFL; NOREFL without a
  kind-8 record; NOREFL not empty;
  declaration kind 9. The rule P vectors are
  declaration failures, not malformed files, but they sit with the reject
  vectors because the outcome is rejected.
- **Decline:** major 2; unknown must-understand section.
- **Corpus.** Every canonical packer packs the test exports and Init, with
  and without `--no-index`. For each setting the files must be
  byte-identical. The two settings must give the same full-check outcome.
  The files must round-trip to the export's records, up to what section 9.1
  drops. CI runs the vectors and init-prelude, an export of Lean's
  `Init.Prelude` kept in the repository. Init and larger exports such as
  mathlib are only tested locally.
- **INDEX vectors.** Accept: a file with INDEX, a file without INDEX, and a
  lookup of every declared name in the Init vector that gives the right
  record. Bad INDEX: offset not at a declaration record, kind mismatch,
  block-length mismatch, keys out of order or repeated, `shared` not maximal,
  empty suffix, a declared name missing, a key naming the wrong declaration,
  decl-count mismatch. These are bad-INDEX vectors, which are not reject
  vectors. A full check MUST give the same outcome as for the same file with
  a correct INDEX, or with none. A subset check that relies on the bad entry
  MUST give "index invalid". Accept vectors exist with and without INDEX.
- **Mutations.** The reference crate changes every single byte of the base
  vector to a few values and checks that the reader never panics. That is a
  smoke test, not fuzzing. Fuzzing with cargo-fuzz, and comparing two
  independent readers on mutated files, are not done yet.

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
| A.15 | inductive flags (lean4export 3.2) | declaration kind 7, announced by an empty must-understand FLAGS section; with FLAGS every inductive block is kind 7 | a flags byte in kind 5 (breaks old readers silently); flags in FLAGS as a side table (a subset reader would need the type's ordinal); kind 5 and kind 7 mixed in one file; major 2 |

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

**R3. Limits.** Section 7 has one format limit, the u32 counts, which also
bounds `block-exprs`. Every limit
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

## Appendix C. Changes in the 2026-11-24 revision

The revision adds the flags of lean4export 3.2 (the kernel renovation,
lean4#16595). It is compatible both ways that matter:

- A file packed from a 3.1 export, or from any export without flags, has
  exactly the bytes it had before. Its exact and kernel digests are
  unchanged.
- A reader written before the revision declines a file with flags ("needs
  section 6"), because FLAGS is must-understand. It never misreads one, and
  never rejects one as malformed.

What changed:

| change | where |
| --- | --- |
| declaration kind 7: kind 5 with five bools after each type's `isReflexive` | 5.2 |
| section 6 FLAGS: empty, must-understand, present iff a kind-7 record exists | 4.1, 8.1, 9 |
| with FLAGS every inductive block is kind 7: a kind-5 record there is an error | 4.1, 5.2, 8.1 |
| error class `flags-section` | 4.1, 8.1 |
| INDEX entry kinds 0-7 | 6a.1 |
| packer input: 3.2.x headers; the five keys, all or none, on every inductive type of the export or on none; 3.2.x requires them | 9.2 |
| digest tags `0x47` (exact) and `0x57` (kernel) for flagged blocks | 9.3, 9.4 |
| vectors: `flags`; `flags-without-section`, `flags-mixed-kind5`, `flags-section-without-block`, `flags-section-not-empty`, `flags-bool-2`; `enum-decl-kind` now uses kind 8 | 11 |

Size: 5 bytes per inductive type of a flagged block, and 24 bytes of
directory entry per file.

**R12. Why a new kind and a marker section (A.15).** The flags change what
a kernel does with a block, so a reader that does not know them must not
read the block as if they were absent. A kind-5 record with a flags byte
appended would be misparsed by an old reader. A new declaration kind alone
would make an old reader reject a good file (enum out of range). The
must-understand section makes it decline, which is what section 2 says
"beyond this reader" means. The section is empty because the flags sit in
the records, where a subset reader that jumps to one declaration (INDEX)
finds them. Kind 5 and kind 7 keep "no flags" apart from "every flag off",
as the kernel needs: without flags it decides by the old rules. The
`format.version` of SOURCE is informational (section 4.1); the rule that a
3.2.x export carries flags everywhere is enforced where the version is
read, by the packer and the ndjson digest (section 9.2).

A file is flagged as a whole, not block by block: with FLAGS every
inductive block is kind 7. Kernels that take the flags check every
inductive type by the new rules, and a kind-5 block among kind-7 ones would
have to be checked by the old ones in the same environment. That is unsound
in general: an old-rule `Acc` with large elimination next to types whose
flags were checked by the new rules is not what either set of rules
admits. Kernels already refuse such a file, so the format makes it a
structural error (`flags-section`, at the kind-5 record), and the packer
and the ndjson digest refuse an export whose types do not all agree on
carrying flags (exit 1). A slice of a file with FLAGS keeps FLAGS whenever
it keeps an inductive block, and keeps every block kind 7.

## Appendix D. Changes in the second 2026-11-24 revision

Lean's kernel renovation (lean4#16595) dropped `isReflexive` from
`InductiveVal`, so exports made with it (for instance Lean
`pr-release-16595-55bd690`, used by lean-kernel-arena-beta) no longer write
the key, even under `format.version` 3.1.0 with the flags. Susz 1 as of
Appendix C required it on every inductive type, so the packer refused
those exports ("missing key 'isReflexive'"). The revision lets a flagged
type leave it out, and keeps that apart in the file. It is compatible both
ways that matter:

- A file packed from an export that carries `isReflexive` (every 3.1
  export, and 3.2 ones from Lean before the change) has exactly the bytes
  it had before, with the same exact and kernel digests. Existing files
  read as before.
- A reader written before the revision declines a file without
  `isReflexive` ("needs section 7"), because NOREFL is must-understand. It
  never misreads one, and never rejects one as malformed.

What changed:

| change | where |
| --- | --- |
| declaration kind 8: kind 7 without each type's `isReflexive` byte | 5.2 |
| section 7 NOREFL: empty, must-understand, present iff a kind-8 record exists; with NOREFL every inductive block is kind 8, and FLAGS is present too | 4.1, 5.2, 8.1, 9 |
| error class `flags-section` covers NOREFL as it covers FLAGS | 4.1, 8.1 |
| INDEX entry kinds 0-8 | 6a.1 |
| packer input: a flagged type may leave out `isReflexive`; all or none in an export; a type without flags must carry it | 9.2 |
| digest tags `0x48` (exact) and `0x58` (kernel) for kind-8 blocks | 9.3, 9.4 |
| vectors: `norefl`; `norefl-without-section`, `norefl-without-flags`, `norefl-mixed-kind7`, `norefl-section-without-block`, `norefl-section-not-empty`; `enum-decl-kind` now uses kind 9 | 11 |

Size: one byte less per inductive type of a kind-8 block, and 24 bytes of
directory entry per file.

**R13. Why the format does not fill it in.** Three ways were open: the
packer computes `isReflexive` and writes kind 7 as before; the file says
"not given"; or Susz stops carrying the field. Computing it is not a local
rule. Lean computes it on the block after nested inductives are eliminated:
`inductive T | node : Array (Nat → T) → T` is reflexive only through the
auxiliary type that stands for `Array (Nat → T)`, whose constructor's field
is `Nat → T`. A packer that got this right would carry a part of the
kernel, and the ndjson digest (section 9.3), which shares no code with the
packer and keeps only hashes, would need a second copy to agree with it.
A packer that got it wrong would make a kernel that compares the value
reject a good file. And a Susz file would hold a field its export does not
have.

Kernels do not need it: every checker computes `isReflexive` while it
checks the constructors and only compares it with the export's value. So a
kind-8 block holds what the export holds, and a checker that reads one
skips the comparison. Kinds 5 and 7 are unchanged: there the export gave
the value, and a checker still compares it. Dropping the field for every
file would change the bytes and digests of every file packed so far, and
throw away a value that older exports do give; keeping "not given" apart
from "false" costs one kind and an empty section.

Why a new kind and a marker section, again (R12): a kind-7 record without
the byte would be misparsed by a reader of Appendix C, and an unknown kind
alone would make it reject a good file. NOREFL makes it decline. The rule
is per file, like FLAGS: a Lean either writes the field or does not, and an
export that mixes the two is refused (exit 1).
