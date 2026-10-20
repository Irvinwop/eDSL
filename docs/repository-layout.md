# Repository layout and extension rules

The library is organized by responsibility. New programs are clients of shared
semantics and proof rules, rather than new verification engines.

| Layer | Location | What belongs here |
| --- | --- | --- |
| Abstract behavior | `EDSL/Semantics.lean` | Refinement, safety and composition interfaces |
| Execution | `EDSL/X86/Sequential/`, `EDSL/X86/StoreBuffer/` | Instruction decoding, state transitions, execution and frames |
| Verification | `EDSL/X86/VCGen/` | Sound WP generation, CFG checks, loop cutpoints and shared proof automation |
| Callable contracts | `EDSL/PureCall/`, `EDSL/BufferCall/` | Independent result/ABI contracts and current resource adapters |
| OS and concurrency | `EDSL/OS/`, `EDSL/Concurrency/` | Ownership, lifetimes, effects, scheduling and histories |
| Artifact identity | `EDSL/ELF/`, `EDSL/PureCall/ELFCertificate.lean` | Complete-file checks, named windows and spec-indexed scalar certificates |
| Registered artifacts | `EDSL/Corpus/` | Fixed-contract certificate adapters and frozen clients |
| Worked proofs | `EDSL/Examples/` | Small examples showing how to use the library |
| Frozen clients | `EDSL/Corpus/V1/` | Specific frozen bytes, invariants, witnesses and certificates |
| Other reference clients | e.g. `EDSL/Sum32/`, `EDSL/CallMemory64/` | Existing specialized proofs and grading profiles, with their own documented scope |
| Commands | `Tools/` | Thin executable adapters, keeping logic in the Lean library |
| Validation | `tests/`, `fixtures/`, `scripts/` | Independent behavior checks and reproducible integration gates |

Keep tracked Lean sources at the repository root limited to `EDSL.lean` and
`lakefile.lean`. Command entrypoints belong under `Tools/`; reusable code,
examples and tests belong in their respective directories above. Run
`bash scripts/check-repository-layout.sh` to check this boundary. The guard
checks Git-tracked files, including staged additions, and rejects root drivers.

The older named client families retain their module paths and theorem names.
They demonstrate additional specialized profiles; they are not prerequisites
for every new function. Their contracts are catalogued in the
[documentation index](README.md).

## Choose an import

- `import EDSL` exposes reusable sequential verification, scalar/buffer call
  contracts and spec-indexed scalar ELF certificates. Its imports exclude
  example programs, frozen corpus data and task registrations.
- Import a particular `EDSL.OS.*` or concurrency module for its documented
  execution/resource profile. Sequential and concurrent assumptions differ.
- `import EDSL.All` loads the full proof catalogue. Project-wide audits and
  fresh kernel replay use this explicit entrypoint.

Existing theorem namespaces stay stable. Code that previously relied on the
old eager `import EDSL` can import its actual provider, or use `EDSL.All` for
compatibility. `EDSL.X86.VCGen.Examples` is now an explicit example import too.

Generic call adapters depend on `EDSL.Grading.ReadOnlyTask.Core`; existing
pair/stride registrations remain in `EDSL.Grading.ReadOnlyTask`. The generic
interface does not depend on particular registered tasks. Complete-file inputs
and present ELF caller resources live in `EDSL.ELF`; scalar witness construction
lives in `EDSL.PureCall.Domain`. Existing Corpus names remain compatibility
aliases. Reusable OS support
lives in Core providers; compatibility modules retain existing program bridges.

## Add a program

Start with [the worked function guide](verify-a-function.md). A program normally
needs only a client module: exact bytes/checked CFG, an independent specification,
and generated-WP evidence. Supply sparse invariants and decreasing ranks for
loops. Reuse the current caller or buffer resource adapter and the common
artifact certificate constructor when those fit the contract.

Do not copy an interpreter, decoder, resource manager, whole instruction proof
or command driver into a client. Keep specification/admission separate from
proof evidence; admission must not assume the desired result or a future
successful execution. A new tool executable is warranted only for a distinct
user-facing command, not for every theorem.

## Add a feature

When code fails admission, record the exact unsupported encoding or resource
operation. Extend its shared semantics, failure conditions, permission/effect
rules and sound checker once. Validate the behavior independently, then let all
clients use the extension. Do not alter frozen bytes, reduce compiler options,
weaken a contract or silently select a different execution model for coverage.

The [frozen corpus](compiler-corpus.md) and [blockers](corpus-blockers.md)
select feature work. A corpus function counts only after both compiler outputs
have exact artifact identity, universal contract proofs, current-resource
composition, useful inputs and audited kernel evidence.

## Keep evidence separate

Frozen `corpus/v1/` inputs and published `corpus/measurements/` snapshots are
historical records. Layout changes must not rewrite their hashes. Active
scripts bind current paths; a later validation run records the new layout.
Regenerable builds and private evidence stay ignored. Real security findings
never enter public Git or CI; see [the policy](../findings/README.md).

Keep personal machine instructions, agent handoffs, and temporary resume notes
in ignored local storage such as `.cache/`. Public documentation should explain
the library, its supported contracts, and reproducible validation.
