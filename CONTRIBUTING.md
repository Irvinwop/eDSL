# Contributing to eDieSeL

The implementation, semantic models and proofs are in **Lean 4**. GNU C23,
GNU C++26, LLVM IR and assembly are the represented/generated domains. Native
fixtures or justified runtime shims may use C/C++/assembly.

Start with the [new-function guide](docs/verify-a-function.md) and
[repository map](docs/repository-layout.md). For a semantic extension, review the
[architecture](docs/architecture.md), [trust model](docs/trust.md), and relevant
resource contract. The [roadmap](docs/roadmap.md) describes remaining work.
Prefer reusable rules and adapters over a new interpreter or driver for each
program. Documentation, examples, and independently specified regressions are
also welcome.

## License and DCO

Contributions are submitted under Apache-2.0, with attribution maintained in
NOTICE where appropriate. Every new contribution commit must include the
commit author's DCO 1.1 sign-off:

```text
Signed-off-by: Your Name <your-email@example.com>
```

Use `git commit -s` after reading the
[Developer Certificate of Origin 1.1](https://developercertificate.org/).
The sign-off certifies that you have the right to submit the contribution under
the stated license. Do not sign for another contributor. The PR DCO check
requires a matching author sign-off on each new commit; the existing bootstrap
commit predates this policy.

Contributors retain copyright. A DCO does not transfer ownership or grant a
separate right to relicense others' contributions. A future license change or
additional commercial licensing arrangement must respect existing licenses and
the permissions of the relevant copyright holders. No CLA is currently used.

NOTICE carries attribution; it does not add restrictions to Apache-2.0.
CITATION.cff requests research citation, which is separate from the license's
redistribution requirements. The canonical terms are in [LICENSE](LICENSE).

## Proof and validation requirements

Run:

```sh
lake build EDSL.All
bash scripts/check-audit.sh
lake env leanchecker --fresh EDSL.All
```

Keep the toolchain/dependencies pinned. Do not use proof holes, added axioms, or
unchecked solver/native execution to advertise a result as proved. Record all
environmental hypotheses and support limitations. Independently define behavior
before implementing a checker and prove the checker's soundness against it.
Review theorem assumptions for nonvacuity and hidden copies of the conclusion.

Each operation needs semantics, ownership/effects, failure and progress rules,
target requirements, native mappings and named proof obligations. Separate
representation, execution, proof and artifact-validation status. Update the
trust report when an implementation crosses a new external boundary.

Optional native probes use the CMake commands in [the validation guide](docs/validation.md). They check GNU dialect
acceptance and atomic/GNU syntax availability, not compiler correctness.

## Meaningful tests and evidence

Tests must check independently defined behavior and catch plausible defects.
Choose unit, integration or end-to-end coverage according to the failure. Do
not mock away the OS or memory behavior that the test claims to check. Avoid
expected results that repeat implementation logic or assert assigned fixtures.
Skip tests without meaningful evidence.

For validators, prioritize malformed/wrong-byte certificates, invalid widths,
unsupported features and artifact mismatches. For OS implementations, use real
threads, waits and mappings plus controlled failure/interruption. Tests and
stress runs complement formal arguments; they do not prove all schedules or a
weak-memory mapping.
