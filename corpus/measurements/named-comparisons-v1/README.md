# Named comparison certificates for frozen corpus v1

The current result is **2/40 functions and 4/80 compiler artifacts certified
under the recorded model assumptions**: `c_min_u64` and `c_max_u64` for both
ordinary GCC and Clang outputs. Both compiler profiles must meet a function's
contract for the primary numerator to increase. No frozen concurrent entry is
certified; that zero does not describe unrelated TSO32 theorems in the library.
The unchanged initial zero reports remain under `corpus/v1/`.

| Compiler | Function | Virtual address | File offset | Full extent |
| --- | --- | ---: | ---: | ---: |
| GCC | `c_min_u64` | 4205904 | 11600 | 15 bytes |
| GCC | `c_max_u64` | 4205920 | 11616 | 15 bytes |
| Clang | `c_min_u64` | 4199136 | 4832 | 11 bytes |
| Clang | `c_max_u64` | 4199152 | 4848 | 11 bytes |

`EDSL.Corpus.V1.Comparisons.certificate compiler operation` composes one shared
VCG comparison family, complete literal ELF metadata/layout/name checks, the
independent registered full64 unsigned order contract and useful current
caller/code resources at the selected address. Both functions of a compiler
share its complete literal file and table proofs. No per-function interpreter,
step proof or command line driver is added.

The named function certificate proves the registered mathematical result,
unchanged modeled RAM and permissions, actual RET/caller target, stack
adjustment, ABI frame and every-prefix current-resource policy for every
admitted call and AF stream. Its useful domain is a declared new modeled
ownership world, not native authority inferred from readable mappings.
The [API and limitations](../../../docs/corpus-certificates.md) explain the
current-text condition and resource construction.

The target requires long mode, CET/IBT and shadow stacks disabled, multi-byte
NOP support, stable modeled RAM, retained executable text and the registered
caller/code resource assumptions. No source/IR preservation, native Linux
startup, relocation, asynchronous interference, physical CPU refinement or
concurrent-history certificate is established. GCC's original ENDBR64 bytes
remain present. Separate family theorems prove exact retired counts of five
for GCC and four for Clang; these are not globally minimum operation counts,
physical micro-operations or timing bounds.

Reproduce with `bash scripts/verify-corpus-certificates.sh`. It builds the
certificate import closure, audits transitive axioms, replays it in a fresh
kernel, then checks every byte of both supplied complete files before producing
`report.json`. It also validates deterministic reports, supplied-path forms and
rejection of changed code, header/opaque metadata, lengths and compiler files.
An incomplete run or failed source-stability check does not pass this gate.
Run evidence is ignored under `artifacts/corpus-certificates/`; the root CI
also builds/audits/replays the integrated EDSL umbrella.

The complete-file identities are:

- GCC41016 bytes: `3accb2f86b13dfac93c717aa1ac825b6cdf106de09bb2efa7cc5519fcf4646b3`.
- Clang44240 bytes: `d74c7b71cdcc3107c870b7765d589b28f51bd5d451ef1f4e5e07425f05f53b61`.

The source parent is `9077611fe581eb5e0bd90bcab33c35e98b7da086` plus the
certificate additions included with this report. `proof-sources.sha256`
identifies the production Lean tree and maintained reporting inputs observed
for this measurement. This digest is diagnostic provenance, not proof of
hardware correspondence or native authority. The exact published commit/CI
and kernel-checked contracts supply the corresponding source/proof evidence.
No frozen source, compiler option, function identity, final ELF byte or seal
was changed to improve coverage.
