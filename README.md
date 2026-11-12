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

The format is described in [docs/spec.md](docs/spec.md). Questions that came
up while implementing it, and how we answered them, are in
[docs/OPEN.md](docs/OPEN.md).

This repository is the reference implementation: a packer (ndjson to Susz), a
reader that checks the structure, and a command-line tool.

## Install

```sh
cargo install --path .
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

`unpack` turns a Susz file back into ndjson. Packing that again gives the same
bytes. `mdata` and `letE`'s `nondep` flag are dropped on the way in, so they
don't come back.

## Exit codes

| command | 0 | 1 | 2 |
| --- | --- | --- | --- |
| `pack` | written | the input is not a valid export (bad JSON, an id that is missing or used twice, a cut-off line, a name declared twice) | couldn't pack it (a limit, something this version doesn't know, I/O, a bug) |
| `verify` | fine | broken | needs a newer reader, or unreadable |
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

The main entry points: `susz::read::File::open` opens a file and checks its
framing, `File::main()` walks the records, `susz::read::Block` reads one proof
block, `susz::index::lookup` finds a declaration by name, and
`susz::pack::pack_file` packs.

## Tests

```sh
cargo test --release                 # unit tests, vectors, init-prelude
cargo test --release -- --ignored    # Init, about 10 s
cargo run --example gen-vectors      # regenerate tests/vectors/
```

`tests/vectors/` has small hand-made files: some that must be accepted, and
for each rule a copy of one of them broken in exactly that way, with the error
it should give. The declarations in them are real ones a kernel accepts
(checked with [Pestka](https://github.com/jasisz/pestka)), so you can run a
full checker on them, not just a reader.

The corpus tests read exports from `SUSZ_CORPORA` (default
`~/pestka-corpora`) and are skipped if they aren't there.

## License

MIT or Apache 2.0, at your option. See [LICENSE-MIT](LICENSE-MIT) and
[LICENSE-APACHE](LICENSE-APACHE).
