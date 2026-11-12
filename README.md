<p align="center"><img src="assets/logo.svg" width="128" height="128" alt="Susz logo: a dried apple ring with five seeds"></p>

# Susz

Susz is a binary format for Lean 4 kernel exports. It holds the same thing as
a [lean4export](https://github.com/leanprover/lean4export) 3.1 ndjson file,
just without the JSON.

Why bother:

- It's about ten times smaller. Mathlib goes from 6 GB of ndjson to 608 MB.
- A checker doesn't have to parse text, so reading the environment is cheap.
- Proofs used by only one theorem sit in their own blocks. A checker can skip
  them until it needs them, or check them in parallel.
- An optional index lets you find a declaration and its proof by name, if you
  only want to check part of a file.

The file is input, not evidence. A checker that reads Susz trusts nothing in
it and checks every count, offset and reference itself, so you don't have to
trust the tool that wrote it either.

The format is described in [docs/spec.md](docs/spec.md).
[docs/OPEN.md](docs/OPEN.md) tells which questions came up while
implementing it, and why the spec answers them the way it does.

This repository is the reference implementation: a packer (ndjson to Susz), a
reader that checks the structure, and a command-line tool.

## Install

```sh
cargo install --path .
cargo install --path . --features mmap   # verify and unpack map the file
```

## Usage

```sh
susz pack IN.ndjson OUT.susz [--no-index] [--threads N]
susz verify FILE.susz [--index]
susz unpack FILE.susz OUT.ndjson
```

`pack` converts an export. The same export always gives the same bytes, no
matter how many threads you use. `--no-index` leaves the index out. The output
only appears once it is complete, so you never end up with half a file.

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
don't come back.

## Exit codes

| command | 0 | 1 | 2 |
| --- | --- | --- | --- |
| `pack` | written | the input is not a valid export (bad JSON, an id that is missing or used twice, a cut-off line, a name declared twice, a declaration of the anonymous name) | couldn't pack it (a limit, something this version doesn't know, I/O, a bug) |
| `verify` | fine | malformed, or a declaration fails | needs a newer reader, past a limit, or unreadable |
| `unpack` | written | broken | needs a newer reader, or I/O |

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
| `verify` | 0.82 G, 0.11 s | 13.4 G, 1.9 s, 182 MiB |
| `verify`, then the records again, before | 3.64 G, 0.29 s | 62.6 G, 5.7 s, 335 MiB |
| `decode`, each block at its theorem | 1.14 G, 0.12 s | 19.0 G, 2.2 s, 198 MiB |
| `decode`, then each block with `decode_block` | 1.10 G, 0.11 s | 18.5 G, 2.0 s, 210 MiB |

Most of the gain over the old reader is not the single pass itself. Varints
of two to eight bytes are now read with one 8-byte load instead of a byte at
a time, and the record readers are inlined into the loop.

The pieces underneath are public too: `susz::read::File::open` opens a file
and checks its framing, `File::main()` walks the records, `susz::read::Block`
reads one proof block, and `susz::pack::pack_file` packs.

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
