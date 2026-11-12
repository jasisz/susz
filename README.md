<p align="center"><img src="assets/logo.svg" width="128" height="128" alt="Susz logo: a dried apple ring with five seeds"></p>

# Susz

Susz (`.susz`) is a binary form of a Lean 4 kernel export: the records of a
[lean4export](https://github.com/leanprover/lean4export) 3.1 ndjson file,
without text to parse, with each proof that only one theorem uses kept in a
block of its own, so a checker can read the environment fast and decode
proofs lazily or in parallel. An optional INDEX finds a declaration and its
proof block by name. The format is specified in [docs/spec.md](docs/spec.md)
(Susz 1); open questions found while implementing it are in
[docs/OPEN.md](docs/OPEN.md).

This crate is the reference implementation: a packer from ndjson, a reader
that checks every structural rule of the spec, and a command-line tool.

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

- `pack` writes the canonical layout (spec section 9): the same export gives
  the same bytes for any `--threads`; `--no-index` leaves out the INDEX
  section. `OUT` is written under a temporary name and renamed when
  complete, so it never holds a partial file.
- `verify` is the full structural check (no type checking): framing, every
  MAIN record, every proof block. The first error is reported with its
  section, absolute byte offset and record number, for example
  `PROOFS @ 18,342,117: block of Foo.bar, record 12: ...`. `--index` also
  checks every INDEX entry against the records (reported apart from the
  verdict).
- `unpack` writes an ndjson export back; packing it again gives the same
  bytes. `mdata` and `letE.nondep` are not kept (spec 9.1).

## Exit codes

| command | 0 | 1 | 2 |
| --- | --- | --- | --- |
| `pack` | the file is written | the input is not a valid export (malformed JSON, a dangling or duplicate id, a truncated line, a name declared twice, ...) | it cannot be packed: a limit, a record or field this packer does not know, I/O, an internal error |
| `verify` | accepted | rejected | declined (needs a newer reader) or unreadable |
| `unpack` | written | rejected | declined or I/O |

A panic is an internal error: it exits 2 and removes the partial output.
A process killed from outside (for instance for memory) leaves no `OUT`.

## Library

```rust
let bytes = std::fs::read("Init.susz")?;
match susz::verify(&bytes) {
    susz::Outcome::Accepted(summary) => println!("{:?}", summary.counts),
    susz::Outcome::Rejected(e) | susz::Outcome::Declined(e) => println!("{e}"),
}
```

`susz::read::File::open` checks the framing; `File::main()` iterates MAIN's
records as events; `susz::read::Block` reads one proof block by its range;
`susz::index::lookup` finds a declaration by name and verifies every INDEX
entry it relies on; `susz::pack::pack_file` packs.

## Tests

```sh
cargo test --release                 # unit tests, vectors, init-prelude
cargo test --release -- --ignored    # Init (about 10 s)
cargo run --example gen-vectors      # regenerate tests/vectors/
```

The vectors in `tests/vectors/` are written in a small assembler
(`src/asm.rs`); every reject vector is one mutation of an accept vector,
named after the rule it breaks, with the expected class and location. The
corpus tests read exports from `SUSZ_CORPORA` (default `~/pestka-corpora`).
