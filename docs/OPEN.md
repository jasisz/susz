# Questions settled while implementing Susz 1

Writing the reference crate raised questions that the first text of
[`spec.md`](spec.md) left open. Each one is now answered in the spec, and
the test vectors pin the answers. None of them changed the bytes of the
format. This file only keeps the history and the reasons. The spec is the
contract.

1. **A packer and rule P.** If a theorem's proof names a constant declared
   after it, the packer still writes the file. Rule P is now a declaration
   failure, not a structural error, and a packer must only write well-formed
   files (sections 2 and 9). The export's own failure stays visible to every
   reader, instead of being hidden or turned into a packer error.
2. **A name declared twice.** The packer refuses the export with exit 1
   (section 9.2). Unique declared names is a MAIN rule, so no well-formed
   file can hold it, and Lean rejects such an environment too.
3. **A declaration of the anonymous name.** This is now a structural error
   of MAIN (section 5.2), and the packer refuses it with exit 1. Its INDEX key
   would be empty, and every key needs a non-empty suffix. Making it a MAIN
   rule keeps the outcome the same with and without INDEX.
4. **Name equality.** Unique names, rule P and INDEX keys compare names by
   value, not by name id (section 5.2). MAIN may write the same name twice,
   and comparing ids would miss that.
5. **Error locations.** Where the counts check, PAD and the PROOFS fill are
   reported, the order inside the header, trailer and directory, two broken
   fields in one record, and blocks with the wrong number of records. All of
   these are in section 8. The conformance suite pins the class and the
   location, so each case needed one fixed answer.
6. **Which ndjson a packer accepts.** The dialect and the two refusal
   classes are in section 9.2. Byte-identical packers must also agree on
   which inputs they pack. The rules match the reader of the Aver packer in
   Pestka.
7. **Block expression indices.** `block-exprs` is now limited to 2^32 − 1,
   like the four counts (section 7.1). An index inside a block then fits a
   u32, and a reader decides the limit from the kind-6 record, before it
   decodes the block.
