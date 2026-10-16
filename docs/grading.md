# Fixed-contract proof grading

`edsl-grade` checks a data-only Lean proof packet against a registered task and
the exact supplied artifact. The candidate chooses code and proof; registration
fixes the input domain, mathematical result, return/ABI frame, OS resources and
effect policy. It cannot submit a replacement postcondition or extra premise.

The first registry contains `pair32` (the modular sum of both mathematical
lists) and `stride32` (the modular sum of the even-indexed input words). Both
use `sequentialReadOnlyX86CallableV1`. The existing GCC implementations discharge
these claims through `EDSL.Grading.Known.pair` and `.stride`. A different
implementation must prove the same `EDSL.Grading.Claim id bytes`; matching a
published byte table, CFG, instruction count or read order is not required.

## Required statement

`Task.lean` owns the registered contract. `SemanticClaim` requires total
correctness for every admitted mathematical input and initial machine state,
for every modeled undefined-AF choice stream. The independent resource domain
additionally requires current code/stack/input authority, current full-RAM
coupling and retained admission at return.

`ReadOnlyPolicy` covers every actual reachable pre-state. It requires an actual
decoded read-only instruction, enabled execution for both AF choices, successful
current operand reads with current permission, and memory-preserving ordinary
steps or return. Stores, atomic operations and syscalls are excluded. A temporary
write followed by restoration still violates this policy. Final memory equality
alone would miss that violation.

`Nonvacuous` separately exhibits useful nonempty machine and resource inputs.
`Domain.pair` and `.stride` construct current allocation/loan worlds for **every**
byte list of length 1–4096, including unsupported opcodes. Their construction
does not decode or execute the program. Task preconditions contain no graph
validity assumption, successful-future-run callback or candidate-selected
hypothesis. Tests admit `[0xff]` and prove that it fails even a trivial total
execution claim on a useful input.

The profile is a sequential callable function with stable ordinary RAM,
complete return slot, full-width ABI arguments and no asynchronous interference.
Canonical-address, alignment-control and other machine assumptions remain in
the [coverage report](coverage.md). OS principals and loans are logical
identities. Native loading, CPU conformance, actual thread identity and native
enforcement of authority remain environmental obligations. This registry does
not grade a whole process, concurrent program, kernel or distribution.

## Artifact and client workflow

Build with the pinned toolchain:

```sh
lake build edsl-grade edsl-proof-export
lake env edsl-proof-export EDSL.Grading.Known EDSL.Grading.Known.pair pair.json
lake env edsl-grade pair32 function.bin pair.json
lake env edsl-grade --elf 35 pair32 function.elf pair.json
```

The file must contain an implementation covered by the submitted proof. An ELF
span is explicit and includes any suffix after an early return. Raw code is
limited to 1–4096 bytes. Restricted ELF64LE ET_EXEC files use the existing
bounded parser (at most 65536 file bytes); the entire selected entry span must
be executable and file-backed. BSS is excluded. This admission limit is separate
from the task's semantic input domain and from the older 64-byte CFG importer.

`Artifact.Claim` binds the full file literal, format/span and successful
selection to the fixed raw claim. The driver first checks the submitted proof
against the selected bytes, then constructs `Artifact.certify` and forces a
second kernel check. The kernel recomputes selection from the full file;
acceptance does not trust host parsing or a displayed hash. The controller
quotes full byte lists as a balanced tree of list appends with small literal
leaves, keeping expression depth manageable. The kernel checks that expression
against the same formal selector. `Hex` is an optional proved client utility;
its total `literal` helper alone grants no artifact admission.

`edsl-proof-export MODULE THEOREM OUTPUT.json [--body]` is a **client tool**. It
reads a locally compiled client module and exports the needed fresh safe
definitions, theorems, opaque bodies and simple inductive groups in dependency
order. Body mode exports the theorem's actual proof body. The client may use
Lean elaboration and tactics locally; the grading service receives JSON only.
Export success is not task acceptance. The grader independently chooses the
expected type from its own registry and artifact.

The complete [client fixture](../tests/fixtures/GradingClient.lean) exercises
fresh parameterized headers, recursors, opaque bodies and mutual inductives.
`lake build GradingFixtures` compiles it; export its
`GradingExportClientFixture.pair` theorem from `tests.fixtures.GradingClient`.
The [integration script](../scripts/verify-grading.sh) reproduces that workflow
and checks wrong-code, wrong-task and extra-hypothesis rejection.

## Packet and checking boundary

Version 1 is an array:

```json
["edsl-proof-v1", [], ["const", ["EDSL", "Grading", "Known", "pair"], []]]
```

There are no source files, imports, plugins, options, search paths or expected
types in the protocol. Expression tags are `bvar`, `sort`, `const`, `app`,
`lam`, `forall`, `let`, `nat`, `str` and `proj`. Numeric payloads are bounded
decimal strings. Names preserve string versus numeric components. Universes
support zero/succ/max/imax and explicitly declared auxiliary parameters; the
final proof is closed and monomorphic.

Auxiliary entries are safe `def`, `theorem`, `opaque` or simple nonnested
`inductive` groups, including mutual inductives. Universe parameters are
explicit. Axioms, unsafe declarations, nested inductives and mutual definitions
are outside the protocol. Every explicit/generated name must be fresh; the
certification namespace is reserved. The kernel checks typing and positivity.

`EDSLGrader.Runtime` implements admission and checking. It audits actual
constant types and values, including theorem/opaque bodies, projection owners,
inductive groups/constructors and recursor rules. It rejects unsafe/actual
partial metadata and every axiom except `propext`, `Quot.sound` and
`Classical.choice`. All auxiliary declarations are audited, including unused
ones. Source `partial def` can lower to a safe logical default body; metadata
does not establish correspondence with the client's compiled runtime code.

Every declaration and final expected-type check calls the options-independent
`Lean.Kernel.Environment.addDeclCore`, with no unchecked insertion, compilation
or evaluation of candidate expressions. `debug.skipKernelTC` cannot disable
that call. Each packet starts from a fresh immutable trusted snapshot. Candidate
declarations do not survive into the next submission.

The controller is implemented in Lean, but its IO/parser orchestration is not
advertised as a formally proved service. Operators must provision the pinned
executable, Lean sysroot and sibling library artifacts as trusted immutable
build products. The grader fixes its project-library search path from its own
installation; it does not accept a candidate module/search path. Imports use
trust level zero, no plugins and no extension loading. Import trust level zero
alone does not replay stored imported proofs: CI separately audits the project
and replays its umbrella module with a fresh kernel.

## Limits and outcomes

Proof input is read with a 4 MiB cap while reading, followed by strict UTF-8
validation and bounded JSON token/nesting preflight before recursive parsing.
Defaults limit JSON depth to 192, expression depth to 128, aggregate decoder
steps to 200000, explicit/generated auxiliary names to 256, decoded strings to
4096 bytes and dependency-audit queue pops to 100000. Decimal/name limits are
also explicit in `Runtime.Limits`.

The packet's 10000000 kernel heartbeat quota is divided among all auxiliary
insertions and the final proof; it is not reset per helper. The artifact wrapper
has a separate quota of the same size and recursion limit 32768; packet checks
use recursion limit 512. Limits are admission policy, not a proved runtime or
memory bound. A service still needs external process time/memory isolation.

| Exit | Meaning |
| --- | --- |
| 0 | Fixed task and full-artifact proof accepted |
| 1 | IO/internal/trusted installation failure |
| 2 | Invalid command line or task ID |
| 3 | Unsupported artifact or declaration feature |
| 4 | Malformed packet, expression or UTF-8 |
| 5 | Kernel/type/dependency-audit rejection |
| 6 | Admission or checking resource limit |

Failure, unsupported input and timeout establish no security defect. Real
findings and their evidence remain outside Git and CI under the repository's
[private findings policy](findings.md). Integration uses project-owned fixtures.

The registry currently has two tasks. Expanding competitive-programming input
and output contracts, mutation/ownership policies, concurrent grading, task
registration review and automated invariant generation remains future work.
Instruction costs can be proved separately; acceptance here does not impose a
particular implementation cost or establish global optimality.
