# Compiler corpus

The [corpus guide](../docs/compiler-corpus.md) defines the fixed 40 functions
and 80 default GCC/Clang final-ELF windows. Current conditional certificate
coverage is **16/40 functions, 32/80 artifacts**, including **one concurrent
function**; **24 functions / 48 artifacts** remain. Both compiler outputs must
pass for function credit. The latest
[byte-equality measurement](measurements/byte-equality-v1/) records the validated
certificate gate on source `383d1f1ef928f551b89a8424ae46c8bb019ce2e2`. See
[commit-specific CI results in GitHub Actions](https://github.com/Irvinwop/eDieSeL/actions).

| Path | Purpose |
| --- | --- |
| [`v1/`](v1/README.md) | Frozen source, compiler options, complete ELFs and manifests |
| [`measurements/`](measurements/) | Immutable historical measurements and source identities |
| [`Extract.lean`](Extract.lean) | Extract candidate data; extraction is not proof evidence |
| [`Probe.lean`](Probe.lean) | Diagnose CFG admission and unsupported code; grants no correctness credit |
| [`Certify.lean`](Certify.lean) | Compose typed exact-artifact certificates and report their scope |
| [`../EDSL/Corpus/`](../EDSL/Corpus/) | Shared certificate/resource adapters and actual Lean proofs |

Run the complete certificate gate from the repository root:

```sh
bash scripts/verify-corpus-certificates.sh --full-project
```

It checks final-file identity, positive/negative controls, transitive axiom
policy and a fresh replay of `EDSL.All` plus the corpus CLI. Input ELFs are not
executed. Native/compiler checks are separate evidence.

Use [measured blockers](../docs/corpus-blockers.md) to choose shared feature work.
Do not change frozen bytes or compiler options to improve coverage. Measurement
hashes describe their recorded snapshot, not every later checkout. Later layout
changes get later validation receipts; published records are not rewritten.
