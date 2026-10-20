# Parity and rotation certificates v1

Conditional coverage is **15/40 functions and 30/80 compiler artifacts**,
including one concurrent function under the existing managed model. This
measurement adds both frozen compiler outputs for `c_parity_loop` and
`c_rotl64`. The preceding [unsigned-average measurement](../unsigned-average-v1/)
retains its historical 13/40 score. Source, compiler options and final ELF
contents remain unchanged; 25 functions and 50 artifacts remain uncertified.

| Function | Compiler | File offset | Virtual address | Bytes |
| --- | --- | ---: | --- | ---: |
| `c_parity_loop` | GCC | 11808 | `0x402e20` | 33 |
| `c_parity_loop` | Clang | 5008 | `0x401390` | 36 |
| `c_rotl64` | GCC | 11744 | `0x402de0` | 13 |
| `c_rotl64` | Clang | 4944 | `0x401350` | 9 |

The independent [parity contract](../../../docs/parity.md) counts set input
bit positions modulo two and returns the answer in unsigned low32 RAX. Every
full64 input is admitted; upper32 RAX is unconstrained. Sparse cutpoint proofs
establish termination using a strict unsigned remainder rank. The independent
[rotation contract](../../../docs/rotate.md) specifies each output bit's input
origin after a left rotation by low32 RSI modulo 64, with arbitrary upper32 RSI.
The instruction model preserves all flags for a masked zero count, defines OF
for a count of one, and admits either OF value for larger counts.

Both clients reuse the production decoder, executor, VCG, scalar contracts,
caller resources and complete named-file certificate constructor. Their proofs
quantify over every modeled undefined-flag choice stream. Complete RAM and
permissions, the original caller, current code authority, ABI obligations and
every-prefix read authority are retained. These are conditional machine-code
certificates, not source-language or compiler-preservation results.

## Validation scope

[report.json](report.json) is the actual complete-file report from the accepted
local full-project gate on 2026-10-20. [proof-sources.sha256](proof-sources.sha256)
and [frozen-files.sha256](frozen-files.sha256) identify that gate's exact public
proof/tooling inputs and complete ELF files. These manifests describe the proof
snapshot; later documentation changes do not change those inputs.

- The full build passed **1,059 jobs** with Lean **4.35.0**, warnings as errors
  and no third-party Lean packages.
- The aggregate transitive audit checked **29,955 EDSL declarations**, allowing
  only `propext`, `Quot.sound` and `Classical.choice`.
- Actual `leanchecker --fresh` replay of `CorpusFullReplay` passed from
  **12:30:08 to 12:41:06 UTC**. The aggregate includes `EDSL.All`, the corpus
  CLI and the selected reusable verification regressions.
- **2,287 command expectations passed**, including deterministic complete-file
  reports, exact symbol/extents, useful current-resource admission, packet
  admission/rejection and closing source/module/frozen/tool/binary/receipt
  checks. Expected negative exits are included in that count.
- Installed body and reference packets passed for both compilers under the
  unchanged **300,000 decoder-step / depth-128** limits. Every corresponding
  wrong-task and changed-final-RET control rejected with the required kernel
  `declTypeMismatch` diagnostic.

| Function | GCC body / reference decoder steps | Clang body / reference decoder steps |
| --- | ---: | ---: |
| Parity | 223354 / 224361 | 281711 / 282756 |
| Rotation | 73225 / 73706 | 68230 / 68583 |

These packet decoder steps measure certificate admission, not program execution
cost. Rotation separately proves exactly five modeled retired instructions for
GCC and four for Clang, including RET and GCC ENDBR64. Neither count is a
physical timing or minimum-cost claim.

The complete certificate gate does not execute the ELF files. The separate
`verify-corpus-v1.sh --frozen` gate also passed: both exact frozen executables
passed the independent native harness, all 80 windows matched the manifests,
and synthetic malformed-ELF controls rejected. Its diagnostic CFG counts were
17/40 GCC and 15/40 Clang; those counts are separate from certification coverage.
Finite native conformance establishes no CPU or OS refinement theorem.

Clean-checkout CI is a separate check. This record states local proof and
admission evidence; publication requires CI on the exact commit.
Reproduce the proof gate with:

```sh
bash scripts/verify-corpus-certificates.sh --full-project
```

## Target assumptions

The sequential certificates retain stable ordinary modeled RAM, canonical
addresses, supplied logical ownership and caller loans, disabled CET/IBT/shadow
stacks and no asynchronous interference. Native Linux loading and resource
authority, physical CPU refinement, source/IR/compiler preservation and
concurrency outside the separately recorded managed profile remain open.
Failed or unsupported certification establishes no security defect.
