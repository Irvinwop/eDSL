# Validation scripts

Run scripts from the repository root. They orchestrate Lean checks, compiler
fixtures and independent native observations; semantic proofs live in `EDSL/`.
See [validation requirements](../docs/validation.md) for prerequisites and scope.

| Task | Entry point |
| --- | --- |
| Keep tracked Lean command drivers out of the repository root | `bash scripts/check-repository-layout.sh` |
| Complete corpus certificates, artifact rejection, audit and full fresh replay | `bash scripts/verify-corpus-certificates.sh --full-project` |
| Project-wide transitive axiom policy and rejection of an untrusted dependency | `bash scripts/check-audit.sh` after building `EDSL.All` |
| Import owned named ELF functions, prove doubling/current resources, compose modules and reject stale proofs | `bash scripts/check-named-elf-import.sh` |
| Reproduce frozen compiler/CFG diagnostics | `bash scripts/verify-corpus-v1.sh` |
| Check independent CPU observations for supported search/byte instructions | `bash scripts/check-sequential-search-native.sh`, `bash scripts/check-sequential-byte-order-native.sh` |
| Capture and kernel-check owned NEG32/BSWAP64 CPU observations | `bash scripts/verify-sequential-unary.sh` |
| Other compiler, OS, grading and native profiles | Their individual `verify-*.sh` / `check-*.sh` scripts, linked from the [reference index](../docs/README.md) |

The layout guard also works from another working directory: it locates the
checkout from its own script path and checks tracked files.

The corpus gate takes its own Lean locks. Do not put an outer lock around it.
Keep proof replay, artifact binding, resource contracts and native conformance
separate in reports; one successful check does not imply the others.

A new program normally adds a Lean client, not a new script or executable.
Reuse the [verification workflow](../docs/verify-a-function.md) and shared gates.
