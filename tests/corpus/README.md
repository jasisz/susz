# Test corpus

`init-prelude.ndjson.gz` is an export of Lean's `Init.Prelude` module, made
with lean4export 3.1.0 from Lean 4.34.1 (githash
`5045d0056413266e57c625dcd7c365b10e377c52`, as its header line says). It is
gzipped (3.6 MB unzipped). `tests/corpus.rs` packs it, checks the file, and
unpacks and packs it again.

The declarations come from Lean 4's source, which is under the Apache
License 2.0 (see the [Lean 4 repository](https://github.com/leanprover/lean4)
and [LICENSE-APACHE](../../LICENSE-APACHE)).
