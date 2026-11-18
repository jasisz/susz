<p align="center"><img src="assets/logo.svg" width="128" height="128" alt="Susz logo: a dried apple ring with five seeds"></p>

# Susz

Susz is a binary format for Lean 4 kernel exports. It holds the same thing as
a [lean4export](https://github.com/leanprover/lean4export) 3.1 ndjson file,
just without the JSON.

Why bother:

- It's about ten times smaller than the ndjson, and two to three times
  smaller when both are compressed. Mathlib: 6.18 GB of ndjson against
  637 MB of Susz; with `gzip -6`, 975 MB against 367 MB; with `zstd -19`,
  656 MB against 334 MB.
- A checker doesn't have to parse text, so reading the environment is cheap.
- Proofs used by only one theorem sit in their own blocks. A checker can skip
  them until it needs them, or check them in parallel.
- An optional index lets you find a declaration and its proof by name, if you
  only want to check part of a file.

A checker that reads Susz trusts nothing in
it and checks every count, offset and reference itself, so you don't have to
trust the tool that wrote it either.

The format is described in [docs/spec.md](docs/spec.md).
[docs/OPEN.md](docs/OPEN.md) tells which questions came up while
implementing it, and why the spec answers them the way it does.

This repository is the reference implementation: a packer (ndjson to Susz), a
reader that checks the structure, and a command-line tool.

## Install

```sh
cargo install susz
cargo install susz --features mmap   # verify and unpack map the file
```

Or the latest from this repository: `cargo install --git https://github.com/jasisz/susz`.

## Usage

```sh
susz pack IN.ndjson OUT.susz [--no-index] [--threads N]
susz verify FILE.susz [--index]
susz unpack FILE.susz OUT.ndjson|-
susz slice IN.susz OUT.susz [--root NAME]... [--roots-file FILE] [--prefix NS]... [--no-index] [--threads N]
susz axioms FILE.susz [--root NAME]... [--roots-file FILE] [--prefix NS]... [--all] [--threads N]
```

`pack` converts an export. It uses all cores unless `--threads N` says how
many threads to use; the same export always gives the same bytes, no matter
how many threads. `--no-index` leaves the index out. The output
only appears once it is complete, so you never end up with half a file.

`pack` reads the export once, in pieces, and never holds all of it. What it
does hold is the expressions: a 1-byte kind, two 4-byte columns for the
children and a 4-byte owner for each one, which is most of its memory. The
kind has a byte of its own so that the children's ids can use all 32 bits.
That costs about 100 MB on mathlib, and `pack` takes up to 2^32 − 1
expressions, as many as the format allows. Packing mathlib (105 million
expressions) on the M2 Pro below, median of three warm runs (with the
index, two):

| | wall | instructions | peak footprint | max RSS |
| --- | --- | --- | --- | --- |
| 1 thread | 5.1 s | 34.0 G | 1652 MB | 2053 MB |
| 1 thread, `--no-index` | 4.7 s | 31.9 G | 1570 MB | 1976 MB |
| 4 threads | 2.2 s | 34.4 G | 1651 MB | 2149 MB |
| 4 threads, `--no-index` | 1.9 s | 32.4 G | 1600 MB | 2080 MB |
| 8 threads | 1.8 s | 34.5 G | 1772 MB | 2298 MB |
| 8 threads, `--no-index` | 1.5 s | 32.4 G | 1706 MB | 2232 MB |

(MB here are MiB.) The max RSS is higher than the footprint because the
columns `pack` is done with are handed back to the system as it goes; macOS
still counts those pages as resident until it needs them.

`verify` checks the structure of a file: framing, every record, every proof
block. It does not type-check anything; that's the checker's job. The first
problem is reported with where it is, for example
`PROOFS @ 18,342,117: block of Foo.bar, record 12: ...`. With `--index` it
also checks the index.

There are two kinds of problems `verify` can find. A malformed file
(`rejected: malformed: ...`) is one no packer should ever write. A
declaration failure (`rejected: declaration failure: ...`) comes from the
export itself: a theorem whose proof names a constant declared after it.
`pack` writes such an export as it is, and `verify` reports that theorem.

`unpack` turns a Susz file back into ndjson. Packing that again gives the same
bytes. `mdata` and `letE`'s `nondep` flag are dropped on the way in, so they
don't come back. With `-` as the output, `unpack` writes the ndjson to
stdout as it goes, so it can feed a checker through a pipe without the
ndjson ever touching the disk (CFSG's is 169 GB):
`susz unpack cfsg.susz - | checker`. A file output only appears once it is
complete; on stdout, an error stops the stream and what was already written
stays written, so check the exit code.

`slice` writes a Susz file that holds only some declarations and everything
they depend on, in their original order: to check one heavy declaration of a
huge file on a small machine, say. The roots are named with `--root`
(repeatable), one per line in `--roots-file`, or by `--prefix NS`, which
takes every declaration whose dotted name starts with the string `NS`
(`--prefix ""` takes them all). Names are written as `verify` prints them. A
declaration depends on the constants and projections in its type, its value
or its proof block, on its mutual block (`all`), and an inductive block comes
whole, with its constructors and recursors. Two dependencies come from the
kernel, not the terms (spec A.9): a Nat literal brings `Nat`, a string
literal `String`, `Char`, `List` and their constructors, and any quotient
declaration brings all four. The output is the canonical file of the export
that keeps only those records, so `slice --prefix ""` of a canonical file
gives back its bytes, and slicing a slice by the same roots changes nothing.
The roots keep their proofs and values, and so does every other declaration
kept.

`slice` maps or reads the input (`--features mmap` maps it) and reads MAIN
three times; PROOFS only for the proof blocks it keeps. It never holds the
whole file's terms. What it does hold for the whole input, besides what any
reader keeps (canonical names, about 40 bytes a name; frontier tables, 4
bytes an entry; 48 bytes a proof block): 9 bytes a MAIN expression (its
children, or the name of a constant), 8 bytes a reference from a
declaration to an expression or a name, and a bit for each name, level, MAIN
expression and declaration. The output is then built like `pack` builds it,
so that part grows with the slice. On FLT (4.1 GB, 209 M MAIN expressions,
12 M names, 1.7 M declarations), on the M2 Pro: `fermatLastTheoremThree`
(66 k declarations, 8.9 M expressions kept) takes 11.7 s and a 3.5 GB peak
footprint; `--prefix FreyPackage` (1.0 M declarations, 656 M expressions
kept, a 3.6 GB output) takes 86 s and 12.1 GB.

`axioms` lists the axioms some declarations depend on, like Lean's
`#print axioms`, without type-checking anything: the axiom declarations in
the closure `slice` would keep for the same roots (`--root`, `--roots-file`,
`--prefix`, and the same dependencies, proof blocks and kernel ones
included), one dotted name per line, sorted, on stdout. With no root and no
prefix it lists every axiom the file declares. `--all` lists every axiom the
file declares, each after `used ` or `unused `. It writes no file, and reads
what `slice` reads up to the closure. `--threads` is accepted as `slice`
takes it and changes nothing. On CFSG (35 GB, 728 M MAIN expressions, 42 M
declarations; mapped, on the M2 Pro: 150 s, 12.2 GB peak footprint, of
which reading MAIN is 81 s and the closure, 40 M declarations and 1.25 G
proof-block expressions, 68 s):

```sh
$ susz axioms cfsg.susz --root CFSGComparator.classification --all
used Classical.choice
used Quot.sound
used propext
unused sorryAx
```

The answer is about the dependency graph only: it says what the root rests
on if every declaration on the way checks.

## Exit codes

| command | 0 | 1 | 2 |
| --- | --- | --- | --- |
| `pack` | written | the input is not a valid export (bad JSON, an id that is missing or used twice, a cut-off line, a name declared twice, a declaration of the anonymous name) | couldn't pack it (a limit, something this version doesn't know, I/O, a bug) |
| `verify` | fine | malformed, or a declaration fails | needs a newer reader, past a limit, or unreadable |
| `unpack` | written | broken | needs a newer reader, or I/O |
| `slice` | written | the input is rejected, a root names no declaration, or no declaration matches | needs a newer reader, I/O, a limit, or a bug |
| `axioms` | listed | the input is rejected, a root names no declaration, or no declaration matches | needs a newer reader, or unreadable |

A panic counts as a bug: exit 2, and the partial output is removed.

## Library

```rust
let bytes = std::fs::read("Init.susz")?;
match susz::verify(&bytes) {
    susz::Outcome::Accepted(summary) => println!("{:?}", summary.counts),
    susz::Outcome::Rejected(e) | susz::Outcome::Declined(e) => println!("{e}"),
}
```

To read a file into your own structures, use `susz::read::decode`. It goes
over the file once. Each record is checked as it is read and then handed to
your implementation of `susz::read::Visit`: names, levels and expressions in
file order, and each declaration right after its proof block. Strings and
name components are borrowed from the file. Names, levels and expressions
come without an allocation of their own; only an inductive declaration
builds a few vectors. There is no need to call `verify` first. If `decode`
gets to the end without an error, `verify` accepts the file. If there is an
error, `decode` reports the same one, at the same place.

That last part takes a little care. The spec reports an error in MAIN before
an error inside a proof block, but a single pass meets a block before the
rest of MAIN. So when a block turns out broken, `decode` stops calling your
visitor, checks the rest of MAIN anyway, and reports the block's error only
if MAIN has none.

```rust
use susz::read::{decode, Expr, File, Visit};

struct Count(u64);

impl<'a> Visit<'a> for Count {
    type Error = ();
    fn expr(&mut self, _id: u32, _e: &Expr<'a>) -> Result<(), ()> {
        self.0 += 1;
        Ok(())
    }
    fn block_expr(&mut self, _k: u32, _e: &Expr<'_>) -> Result<(), ()> {
        self.0 += 1;
        Ok(())
    }
}

let file = File::open(&bytes)?;
let mut count = Count(0);
match decode(&file, &mut count) {
    Ok(_) => println!("{} expressions", count.0),
    Err(e) => println!("{e:?}"),
}
```

A proof block can also wait. Return `false` from `Visit::open_block` and
decode the block when you need it with `susz::read::decode_block`, which
checks it the same way. `Decoded::unread` counts the blocks left like that.
The file only counts as accepted once each of them has been decoded without
an error.

What reading costs, on the same M2 Pro as below, files mapped, median of
three warm runs. The `decode` rows use a visitor that adds up every field it
is given, so they do a little more than `verify`. "Before" is the reader
before `decode` existed, where a checker that wanted the records had to read
the file a second time.

| | Init: instructions, wall | mathlib: instructions, wall, peak footprint |
| --- | --- | --- |
| `verify`, before | 1.75 G, 0.14 s | 29.8 G, 2.7 s, 210 MiB |
| `verify`, 0.1.0 | 0.82 G, 0.11 s | 13.4 G, 1.9 s, 182 MiB |
| `verify` | 0.51 G, 0.07 s | 8.1 G, 1.3 s, 183 MiB |
| `verify`, then the records again, before | 3.64 G, 0.29 s | 62.6 G, 5.7 s, 335 MiB |
| `decode`, each block at its theorem, 0.1.0 | 1.14 G, 0.12 s | 19.0 G, 2.2 s, 198 MiB |
| `decode`, each block at its theorem | 0.82 G, 0.09 s | 13.6 G, 1.8 s, 198 MiB |
| `decode`, then each block with `decode_block` | 0.81 G, 0.08 s | 13.4 G, 1.6 s, 210 MiB |

Most of the gain over the old reader is not the single pass itself. Varints
of two to eight bytes are read with one 8-byte load instead of a byte at a
time, and the common records (applications, binders, constants, names,
frontier entries) take a fast path: read from a fixed window of the file with
plain loads, accepted only when every check passes, and otherwise read again
by the checked reader, which gives the error and its place. Of the 13.6 G of
`decode` on mathlib, about 5 G is the visitor adding up the fields.

The pieces underneath are public too: `susz::read::File::open` opens a file
and checks its framing, `File::main()` walks the records, `susz::read::Block`
reads one proof block, `susz::pack::pack_file` packs,
`susz::unpack::unpack` writes ndjson to any `Write`, and
`susz::slice::slice_file` slices and `susz::axioms::axioms` lists the
axioms of a closure.

`susz::index::Lookup` finds declarations by name. It decodes the index once
and keeps its place in MAIN between lookups. The binary search is the cheap
part. Each lookup also has to decode MAIN up to the declaration it finds,
unless an earlier lookup already went that far. For a declaration near the
end of mathlib that is nearly all of MAIN. `susz::index::lookup` does one
lookup from scratch.

### Memory-mapped files

The reader only wants a `&[u8]`, so a memory-mapped file works as well as one
read into memory. With the cargo feature `mmap`, `susz::open_mmap(path)` maps
a file read-only and gives back something that derefs to `[u8]`. If the file
can't be mapped (a pipe, say), it reads it into memory instead.

The feature is off by default and is the only thing that pulls in a
dependency (`memmap2`). Cargo has no dependencies just for a binary, so
turning it on by default would give every library user `memmap2` too. That's
why the `susz` command uses mmap only when built with `--features mmap`, and
reads the file otherwise.

`open_mmap` is `unsafe`, for a plain reason: nothing may truncate or change
the file while it is mapped. A change shows up in bytes the reader already
checked, and a truncation makes the next read of a lost page raise `SIGBUS`.
The `susz` command treats its input as a file it doesn't own. It maps it
read-only and never writes to it, and on Linux and macOS it catches `SIGBUS`:
it says the file was truncated or couldn't be read, removes any partial
output, and exits 2.

What it buys, measured on mathlib (Susz 623 MB with INDEX, 608 MB without) on
an M2 Pro, median of three warm runs, with the reader as it was before
`decode` (it is faster now, see above, but mapping changes the same things):

| | wall | instructions | peak footprint | max RSS |
| --- | --- | --- | --- | --- |
| `verify`, read | 2.9 s | 31.3 G | 817 MB | 818 MB |
| `verify`, mmap | 3.0 s | 31.2 G | 210 MB | 818 MB |
| `verify --index`, read | 4.9 s | 48.5 G | 994 MB | 994 MB |
| `verify --index`, mmap | 4.9 s | 48.2 G | 373 MB | 995 MB |
| one late `Lookup`, read | 1.6 s | 16.2 G | 895 MB | 895 MB |
| one late `Lookup`, mmap | 1.6 s | 15.9 G | 273 MB | 594 MB |

(MB here are MiB.) The peak footprint is the memory that belongs to the
process alone. Mapped pages are part of the system's file cache: they count
in the resident size, but the system can drop them and read them again. So
mmap gives the file's size back as private memory, and saving the copy
saves 0.3 to 1.7% of the instructions. The wall time stays the same. A lookup never touches
PROOFS, so those pages are never even read in.

Cold is less rosy. On a fresh copy of the file, written with the cache turned
off for it, mmap was slower: 3.7 s against 2.9 s for `verify`, 1.9 s against
1.6 s for the lookup, in two runs each on a busy machine. Telling the system
the reads would be sequential didn't help.

The reader has one limit of its own: a string component of a name must be
shorter than 2^32 − 2 bytes. A longer one makes it decline.

## Tests

```sh
cargo test --release                 # unit tests, vectors, init-prelude
cargo test --release -- --ignored    # Init, about 20 s
cargo run --example gen-vectors      # regenerate tests/vectors/
```

CI runs the unit tests, the vectors and init-prelude, with and without the
`mmap` feature. It does not run Init or mathlib, and there is no fuzzing
yet.

`tests/vectors/` has small hand-made files: some that must be accepted, and
for each rule a copy of one of them broken in exactly that way, with the error
it should give. The declarations in them are real ones a kernel accepts
(checked with [Pestka](https://github.com/jasisz/pestka)), so you can run a
full checker on them, not just a reader.

`tests/corpus/init-prelude.ndjson.gz` is a lean4export export of Lean's
`Init.Prelude` (see [tests/corpus/README.md](tests/corpus/README.md)). The
corpus tests pack it, check the result, unpack it and pack it again. If the
file is missing they skip it, unless `SUSZ_REQUIRE_CORPORA=1` is set, as in
CI. Larger exports such as Init are read from `SUSZ_CORPORA` (default
`~/pestka-corpora`) and skipped if they aren't there.

## License

MIT or Apache 2.0, at your option. See [LICENSE-MIT](LICENSE-MIT) and
[LICENSE-APACHE](LICENSE-APACHE).
