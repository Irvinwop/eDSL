# Contract and regression checks

Tests exercise independently specified behavior, exact-byte rejection and
current authority/lifetime rules. They complement the universal library proofs;
native observations do not supply a proof oracle.

For the new-program workflow:

```sh
lake build VerificationTests
```

- [`VerifyFunction.lean`](VerifyFunction.lean) applies the worked function proof
  to useful current OS resources, full64 numeric edge cases and changed bytes.
- [`ELFCertificate.lean`](ELFCertificate.lean) composes a complete named ELF
  with independent results and current caller authority, plus rejection controls.
- [`VerificationImports.lean`](VerificationImports.lean) guards the reusable API's
  transitive module boundary, including task registration and VCG example providers.
- [`ELFFunctionCandidate.lean`](ELFFunctionCandidate.lean) exercises named ELF
  extraction against independently encoded files, including dynamic aliases,
  invalid layouts and stale extracted evidence. Run the IO checks and generated
  kernel-proof integration with `bash scripts/check-named-elf-import.sh`.
- [`ELFStackCaller.lean`](ELFStackCaller.lean) checks complete high-byte return
  reads, permission hide/restore behavior, rounded-page overlap and invalid
  caller conditions against the reusable return-slot provider.
- [`templates/NamedELFFunctional.lean`](templates/NamedELFFunctional.lean) composes
  a fresh named import with the independent doubling contract and a useful
  current-resource execution. The shared script copies and compiles this template
  against its generated `Named` module; it is not an ordinary Lake test root.

Existing loop/resource regressions build through `BoundedScanTests`,
`IndexSearchTests` and `ByteComparisonTests`. `ManagedFetchAdd64Tests` covers the
managed concurrent profile. `UnaryTests` checks the shared NEG32/BSWAP64
instructions, whole scalar routines and final-ELF/current-resource rejection.
`fixtures/` contains proof-packet clients kept
separate from the grader's trusted imports; `native/` holds native check inputs.

The [validation guide](../docs/validation.md) and [CI workflow](../.github/workflows/lean.yml)
list the remaining ISA, OS, ABI, parser and integration checks. Keep their target
profiles explicit. Add tests only when they can catch a plausible behavioral
regression; do not echo assigned fixture fields or mock away the relevant effect.
