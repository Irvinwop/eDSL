# Trust, assumptions, and evidence

Status: required reporting policy plus the current scaffold's actual boundary.
The end-to-end compiler/OS pipeline is not implemented.

## Current boundary

The Lean library includes a restricted x86-64 decoder/machine model, unbounded
execution proofs, an all-input increment theorem for actual compiler-output
bytes and a narrow certificate CLI. It also retains generic refinement lemmas
and the original toy example. See [coverage](coverage.md) for assumptions and
supported encodings. These results do not prove the model's conformance to
physical hardware, source-language preservation or a complete OS implementation.

`lake build` checks the declarations with Lean 4.35.0. The audit traverses
transitive axiom dependencies of declarations under `EDSL` and permits only
Lean's standard `propext`, `Quot.sound`, and `Classical.choice`. It rejects
`sorryAx` and any additional axiom. No third-party Lean package is currently
required. Review of theorem statements and definitions is still essential.
The audit's negative check requires rejection of an injected external axiom
used by a project theorem. The pinned toolchain's `leanchecker --fresh EDSL`
also replays stored declarations in a fresh kernel environment. This remains
the same kernel implementation, not an independent physical-world validation.

Standard foundational axioms are distinct from an unproved claim that a compiler
or operating system is correct. Environmental assumptions should be visible
parameters in theorem statements and reports, never hidden global axioms.

## Planned trust ledger

Every artifact report must distinguish:

| Item | Planned treatment |
| --- | --- |
| Specification and admitted-input definition | Human-reviewed; needs examples, counterexamples and nonvacuity checks |
| Formal source/ISA/OS definitions | Reviewed models; adequacy to language specifications and real platforms is a separate obligation |
| Lean kernel and logical foundations | Proof-checking trust base; pin toolchain and report accepted axioms |
| Lean elaborator, tactics and proof search | Produce terms checked by the kernel; reject holes and unsupported axioms |
| Native evaluation, FFI, external solvers | Untrusted unless reconstructed/checked through a proved route; any deliberate additional trust must be separately labeled |
| Compiler, optimizer, assembler, linker | Untrusted producers in translation validation; certify their particular final output |
| Parsers, decoders, printers and importers | Proved correspondence or explicit trusted boundary; test success alone is insufficient |
| Libraries and runtime shims | Validate concrete reachable implementations or show their contracts as assumptions |
| Loader and OS implementation | Contract assumptions until a concrete conformance/refinement proof exists |
| CPU, devices, hypervisor, firmware and deployment | Physical/environmental conformance and integrity assumptions; outside a pure Lean theorem unless modeled and justified separately |
| Build, storage and certificate cache | Pin dependencies and check artifact equality; names and hashes alone do not prove semantic correspondence |

Lean's [proof-validation documentation](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)
explains the distinction between checking proofs and trusting additional
execution mechanisms. Pin the reference to the selected toolchain when adopting
new proof-generation routes.

## Avoid vacuous or overstated claims

- Prove or exhibit admitted initial states; an impossible precondition makes
  many theorems trivially true.
- Separate source definedness, target behavior inclusion, target behavior
  existence, and total correctness. Nonempty behavior does not establish
  termination if divergence is an allowed observation.
- Cover all relevant target behaviors and coupled environments. One successful
  run or one favorable schedule is not the desired theorem.
- Record the treatment of source UB, machine faults, deadlock, divergence,
  resource exhaustion, interruption and partial I/O.
- Never describe a finite unrolling bound as a proof about arbitrary loops or
  arbitrary thread counts. Report exact bounds and coverage.
- Keep conformance evidence, testing, model checking, solver search, and
  kernel-checked proofs as distinct evidence categories.
- Review dependencies and hypotheses after every abstraction/lowering change.
  An axiom-free proof can still prove the wrong proposition about the wrong model.

## Release evidence required later

A certified artifact needs exact final bytes, available build provenance,
supported-feature/profile checks and named machine-property proofs. Add source
identity, frontend evidence and refinement proofs for source-preservation claims.
Every route also needs link/load and runtime obligations, the specification,
explicit environmental assumptions, tool/library/model revisions, proof audit
results, and reproduction commands. Cost/security/termination claims each need
their own named theorem and scope. Changed dependencies invalidate cached
certificates until checked again.

The first releases should say **proved under a stated Linux/ISA contract**.
Reducing that boundary means proving more of the concrete runtime, loader,
OS, or hardware relationship; renaming an assumption does not reduce trust.

Direct [binary-first proofs](binary-first.md) can avoid a trusted frontend by
stating the desired behavior directly over final machine-code execution. They
do not thereby prove source equivalence. [OS implementation proofs](os-implementation.md)
can discharge particular kernel/runtime contracts, including the required
caller/interference and hardware assumptions. A failed proof is not evidence
of unsafe code: use the [findings workflow](findings.md) to distinguish missing
analysis support from a checked violation of a justified property.
