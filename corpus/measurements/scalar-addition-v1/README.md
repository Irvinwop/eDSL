# Scalar addition extension of corpus v1

This report extends the historical named-comparison measurement from
2/40 functions and 4/80 compiler artifacts to **3/40 functions and 6/80 artifacts**
under the recorded model assumptions. Both compiler outputs must pass for a
function to count. The accepted symbols are `c_min_u64`, `c_max_u64` and
`c_add_mod64`; zero frozen concurrent entries are certified.

The [shared scalar constructor](../../../docs/corpus-scalar-certificates.md)
composes the registered mathematical task, production VCG semantics, complete
literal ELF/name checks and useful current resources at each selected address.
The addition domain includes every pair of full64 values, including overflow.
Existing full files, metadata/layout proofs and caller facts are reused.

| Compiler | Symbol | Address | Offset | Extent |
| --- | --- | ---: | ---: | ---: |
| GCC | `c_min_u64` | 4205904 | 11600 | 15 |
| GCC | `c_max_u64` | 4205920 | 11616 | 15 |
| GCC | `c_add_mod64` | 4205984 | 11680 | 9 |
| Clang | `c_min_u64` | 4199136 | 4832 | 11 |
| Clang | `c_max_u64` | 4199152 | 4848 | 11 |
| Clang | `c_add_mod64` | 4199200 | 4896 | 5 |

Complete file identities remain GCC41016 bytes
`3accb2f86b13dfac93c717aa1ac825b6cdf106de09bb2efa7cc5519fcf4646b3` and
Clang44240 bytes
`d74c7b71cdcc3107c870b7765d589b28f51bd5d451ef1f4e5e07425f05f53b61`.
No frozen file, manifest, source, compiler option or seal was changed.

The target requires long mode, disabled CET/IBT and shadow stacks, supported
modeled NOPs, stable modeled RAM, retained executable text and the registered
current caller/resource assumptions. Useful domains declare new modeled
ownership rather than authenticating native authority. No source/IR, native
Linux startup, physical CPU or concurrent-history refinement is established.
Separate exact model instruction counts are min/max GCC5/Clang4 and addition
GCC3/Clang2; global minimum operations and physical timing are not proved.

Reproduce with `bash scripts/verify-corpus-certificates.sh`. Both complete ELF
files must match before any JSON report is emitted. The gate separately builds,
audits and fresh-replays the six typed instances and checks input rejection and
source/module stability. The full umbrella audit/replay and exact-commit CI are
separate acceptance evidence. Reports concern bytes observed in that read.

`proof-sources.sha256` identifies production Lean and maintained reporting/test
inputs observed for this measurement. It is diagnostic provenance, rather than
a proof of hardware correspondence or native authority. The source parent is
`3369ceca1d9bd75b4fd6508373dac7a118951be4` plus the additions in this measurement's
published commit. The immutable initial corpus and earlier measurements remain
historical checkpoints.
