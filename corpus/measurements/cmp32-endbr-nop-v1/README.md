# Corpus v1 measurement after the comparison/padding ISA batch

These reports run the production `CFG.analyze` and checker on the unchanged
80 frozen v1 function windows. The batch adds exact ENDBR64 under the declared
CET/IBT/shadow-stack-disabled target, register CMP/TEST32 and exact NOPs through
five bytes. The 64-byte/32-instruction profile bounds remain unchanged.

GCC acceptance rises from 0/40 to 5/40; Clang remains 4/40. Accepted GCC symbols:
`c_min_u64`, `c_max_u64`, `c_add_mod64`, `c_sum_u32`, and
`c_atomic_load_acquire64`. This measures decoding and control-flow acceptance.
End-to-end function and artifact certification remain 0/40 and 0/80. In
particular, acceptance of an acquire-load encoding establishes no source
acquire synchronization, and a cyclic CFG establishes no termination.

The immutable initial reports remain under `corpus/v1/`. No compiler option,
function identity, source definition, final ELF byte or frozen seal was changed.
The final ELF SHA-256s are:

- GCC: `3accb2f86b13dfac93c717aa1ac825b6cdf106de09bb2efa7cc5519fcf4646b3`.
- Clang: `d74c7b71cdcc3107c870b7765d589b28f51bd5d451ef1f4e5e07425f05f53b61`.

The source parent is `35eb6249dc82e11315b98c8d6a766c73ee48dffd` plus the ISA
changes included with these reports. `checker-sources.sha256` identifies every
observed `EDSL/X86/*.lean` input. This is a diagnostic provenance manifest, not
an independent proof of source identity, decoder soundness or hardware
conformance. The exact commit and CI bind the checked repository sources;
Lean checking establishes only the claims stated by its formal contracts.
