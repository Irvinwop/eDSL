# Grading counted-store proofs

`edsl-grade countedStore64` checks a data-only proof against the independent
`CountedStore64` contract and exact raw or restricted ELF artifact. Registration
fixes the full64 arguments/count, zero-count retention, modular returned/stored
value, complete memory/permission/ABI frame, actual RET and current OS effects.
Candidate bytes and proof packets cannot select another postcondition or add
an execution-success premise.

`Grading.Claim .countedStore64 bytes` requires total correctness for every
admitted input/state and AF stream, both raw and with current resources.
Every actual ordinary contained store advances the same checked ownership
world. The return hook retains full RAM coupling, owners/epochs, live loans,
permissions and outside contents, with authority for another arbitrary checked
store. This uses `sequentialOwnedWord64X86CallableV1`; atomic instructions,
syscalls and concurrent interference remain outside this task.

The independent domain is inhabited for every nonempty byte list of at most
4096 bytes, including unsupported instructions. Its useful witness has a real
required target change. Universal semantics still covers zero count and all
other admitted values; usefulness does not restrict the semantic quantifier.
An actual unsupported-step theorem refutes a returning claim for `[0xff]`.

Both closed claims are available in the trusted registry:

- `EDSL.Grading.Known.countedStore64GCC`
- `EDSL.Grading.Known.countedStore64Clang`

They prove the same task for the two compiler windows documented in the
[GCC](counted-store64.md) and [Clang](counted-store64-clang.md) profiles.
The grader invokes no convenience shape checker. Instruction selection,
loop layout, intermediate store count and exact instruction costs are absent
from task acceptance. A new implementation must prove the same fixed claim.
This integration demonstrates the two known windows; it does not yet provide
a new client implementation outside them.

```sh
lake build edsl-grade edsl-proof-export
lake env lean -DwarningAsError=true tests/GradingCountedStore64.lean
EDSL_GCC=gcc-13 EDSL_CLANG=clang-18 bash scripts/verify-counted-store64-grading.sh
lake env .lake/build/bin/edsl-proof-export EDSL.Grading.Known \
  EDSL.Grading.Known.countedStore64GCC proof.json
lake env .lake/build/bin/edsl-grade countedStore64 program.bin proof.json
lake env .lake/build/bin/edsl-grade --elf 20 countedStore64 program.elf proof.json
```

Runtime tests use fresh trusted modules and both packet dialects. They require
acceptance of each known exact window and rejection when a packet is reused
for changed bytes or another task. Integration freshly compiles/links both
outputs, exports reference/body packets and grades raw/ELF artifacts. It also
rejects cross-compiler packets and shortened selected spans. These packet
rejections establish no semantic defect in other code.

The native oracle checks 504 finite full64-argument/result, complete-page-frame
and SysV calls per output over practical counts, and six generic owned mutants.
Symbolic Lean proofs cover high-half and maximum counts without executing huge
native loops. Existing [grading limits and trust](grading.md) and ordinary-RAM
environment assumptions remain explicit. This adds no C/volatile/compiler
preservation, whole-OS safety, concurrent visibility, physical timing or global
optimality guarantee. Exact costs remain separate accounting.
