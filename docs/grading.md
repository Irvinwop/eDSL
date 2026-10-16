# Fixed-contract proof grading

`edsl-grade` checks a data-only Lean proof packet against a registered task and
the exact supplied artifact. The candidate chooses code and proof; registration
fixes the input domain, mathematical result, return/ABI frame, OS resources and
effect policy. It cannot submit a replacement postcondition or extra premise.

The registry contains `pair32` (the modular sum of both mathematical lists),
`stride32` (the modular sum of the even-indexed input words), `write32`
(store the low 32 bits of the full-width argument at the fixed input pointer),
and `storeReturn32` (the same store plus the complete target pointer in RAX).
Pair and stride use `sequentialReadOnlyX86CallableV1`; both store tasks use
`sequentialOwnedWord32X86CallableV1`. The existing GCC implementations discharge
these claims through `EDSL.Grading.Known.pair`, `.stride` and `.write`. A different
implementation must prove the same `EDSL.Grading.Claim id bytes`; matching a
published byte table, CFG, instruction count or read order is not required.

The client-only [MOV-initialized stride proof](../tests/fixtures/StrideMov.lean)
demonstrates a different executed implementation of the same task. Its 22 bytes
use `MOV EAX,0` in place of the published 19-byte routine's `XOR EAX,EAX`.
It reuses generic loop assertions and proves the new initialization, offsets,
branches, return, all-choice semantics and current OS authority. The grader's
trusted snapshot does not import this client module.

The client-only [intermediate-store proof](../tests/fixtures/WriteIntermediate.lean)
certifies `INC RSI; store ESI; DEC RSI; store ESI; RET` under the same `write32`
task. Its eleven bytes first write low32(argument+1), then the requested value.
Full-width RSI restoration covers wraparound; both stores advance the current
OS state through the real checked mutation gate. This five-instruction routine
retains current code/stack loans and the same actual returned resource frame.
The first stored value may differ from the final result, as the fixed policy
allows. Its closed claim is `EDSL.WriteIntermediateSupported.claim`.

The client-only [MOV store/readback proof](../tests/fixtures/WriteMoves.lean)
uses seven bytes: `MOV ECX,ESI; MOV [RDI],ECX; MOV ECX,[RDI]; RET`.
All three MOVs use the generic sequential forms. One checked store evolves
the current OS world; the load uses actual owner/ticket authorization and the
word in that same evolved world. It creates no target read loan. Preserved
machine RSP supplies the explicit caller-slot binding for the actual RET.
`EDSL.WriteMovesSupported.claim` proves the unchanged `write32` contract;
`modeled_accounting` derives four instructions and the ordered target4/stack8
reads for every actual returned result. The void task's result remains the
stored word and its frame; the additional load still needs current read authority.

The client-only [pointer-return proof](../tests/fixtures/StoreReturnRcx.lean)
uses nine bytes: `MOV RCX,RDI; MOV [RCX],ESI; MOV RAX,RCX; RET`.
`EDSL.StoreReturnRcx.claim` proves the distinct `storeReturn32` task with one
actual checked OS mutation, retained full RAM coupling and caller loans.
Its four-instruction accounting is separate from the registered contract.
The direct pointer-store certifier's three shapes exclude this implementation;
the general grader accepts its checked proof under unchanged default limits.

## Required statement

`Task.lean` owns the registered contract. `SemanticClaim` requires total
correctness for every admitted mathematical input and initial machine state,
for every modeled undefined-AF choice stream. The independent resource domain
additionally requires current code/stack/input authority, current full-RAM
coupling and retained admission at return. Registration fixes the raw policy,
resource policy and resource-return predicate; these are not packet fields.
The pair/stride contracts retain their original meaning through proved
equivalences with the original read-only contracts in `ReadOnlyTask.lean`.

`ReadOnlyPolicy` covers every actual reachable pre-state. It requires an actual
decoded read-only instruction, enabled execution for both AF choices, successful
current operand reads with current permission, and memory-preserving ordinary
steps or return. Stores, atomic operations and syscalls are excluded. A temporary
write followed by restoration still violates this policy. Final memory equality
alone would miss that violation.

`write32` admits every old/new value pair, arbitrary high RSI bits and the
actual caller's eight-byte return slot. Its independent postcondition requires
the low32 value, actual return and RSP+8, all SysV callee-saved GPRs and
nonarithmetic flags, every outside-target RAM read and complete writable and
executable maps. Volatile registers, instruction count and intermediate stored
values are unconstrained. Every actual decoded store must target the fixed
input pointer. Atomics, syscalls and foreign writes remain excluded, including
temporary foreign writes followed by restoration. Fetches stay within the
admitted code span.

`storeReturn32` reuses exactly the same inputs, present raw/current-resource
preconditions, useful domain, machine/resource policies and actual resource
return predicate. Its independent `StoreReturn32.Post` additionally requires
`final.registers .rax = input.address`, without restricting the pointer to 32 bits.
`storeReturn_claim_write` projects the stronger claim to the original void
contract. An actual admitted store/RET execution proves the reverse implication
false: the unchanged `Known.write` implementation need not return the pointer.
Neither task requires a known instruction sequence or exact instruction count.

The managed write policy uses current code and complete stack loans, a current
owner/epoch ticket for the entire target word, and no live read loan for the
target allocation. Each actual store derives a successful `Borrowing.mutate`
and the matching machine-memory update. Read-only instructions retain the same
OS state. The lifted prefix/return relations carry the actual AF stream,
machine steps and operand reads from the registered seed; final resource
authority cannot be supplied by an unrelated new world. Allocations, loans,
permissions and outside-target cells are retained throughout. Target reads
require current owner authorization, full-word containment and actual load
success; stack reads require the current complete-slot loan.

`Nonvacuous` separately exhibits useful nonempty machine and resource inputs.
`Domain.pair` and `.stride` construct current allocation/loan worlds for **every**
byte list of length 1–4096, including unsupported opcodes. Their construction
does not decode or execute the program. Task preconditions contain no graph
validity assumption, successful-future-run callback or candidate-selected
hypothesis. Tests admit `[0xff]` and prove that it fails even a trivial total
execution claim on a useful input.
`Write32.Domain.candidate` similarly constructs useful raw/current-resource
inputs for every 1–4096-byte candidate without decoding it. Its useful witness
requires the old value to differ from the requested low32 value. Separate
regression theorems reject both unsupported code and a successfully returning
RET-only implementation, so a no-op cannot satisfy an already-equal-only domain.

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

For the owned-word task, export `EDSL.Grading.Known.write` and select `write32`.
The owned GCC fixture has three bytes, `89 37 c3`; the independent contract is
defined in `EDSL.Grading.Write32.Contract`, rather than inferred from those bytes.

For the pointer-result task, select `storeReturn32`. The closed known export
targets are `EDSL.Grading.Known.storeReturnStoreCopy`, `.storeReturnCopyStore`
and `.storeReturnCopyStoreRax`. Export a fresh implementation independently:

```sh
lake build edsl-grade edsl-proof-export GradingFixtures
lake env edsl-proof-export tests.fixtures.StoreReturnRcx EDSL.StoreReturnRcx.claim rcx.json
lake env edsl-grade storeReturn32 function.bin rcx.json
lake env edsl-grade --elf 9 storeReturn32 function.elf rcx.json
EDSL_GCC=gcc-13 EDSL_CLANG=clang-18 bash scripts/verify-store-return-grading.sh
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
It also exports `EDSL.StrideMov.claim` from `tests.fixtures.StrideMov`, checks
its assembled raw/ELF bytes, and compares native behavior with the existing
independent modular-sum/ABI/guard-page oracle. Client elaboration metadata is
not a packet input; the final proof terms are independently kernel-checked.
The write fixture checks reference/body packets and the complete restricted
ELF artifact. Its separate native observer checks the full data-page footprint,
full-width arguments, unaligned/page-edge targets and ABI frames. Six owned
mutants exercise missing/wide/shifted/wrong-source stores and register/DF damage.
The same oracle observes the separately assembled intermediate-store routine,
including full-width argument wraparound. Its client-only reference/body
packets, raw and complete ELF artifacts, changed-code and one-byte wrong-value
mutation checks use unchanged service limits. Acceptance of both two- and
five-instruction implementations demonstrates that cost proofs remain separate
from functional/resource grading.
The same pipeline checks the seven-byte MOV client in both packet modes and
as a complete restricted ELF. Reversing its first copy rejects proof reuse and
fails the independent native write contract. Its four instructions and extra
target read retain the same task, service limits and returned-resource contract.
`lake build GradingFixtures` builds the kernel-compiling client modules under
`tests/fixtures/`; the grader's trusted imports exclude these modules.
Each client-isolation check runs in its own Lean process to bound the number
of imported proof environments retained in memory.

The [pointer-result integration](../scripts/verify-store-return-grading.sh)
checks all three known implementations and the fresh RCX client in both packet
modes against raw and full explicit-span ELF artifacts. A valid void-store
proof on the same original bytes passes `write32` and fails `storeReturn32`.
Changed task/code/span and pointer truncation prevent proof reuse. Trusted
snapshot isolation is checked before replay. The independent full-pointer
native oracle executes the same four final artifacts in 336 calls and rejects
six owned mutants; native observation remains separate from universal proofs.

## Packet and checking boundary

New clients emit version 2. Each expression field has its own topologically
ordered table of shared syntax nodes:

```json
["edsl-proof-v2", [], ["dag", [["const", ["EDSL", "Grading", "Known", "pair"], []]], "0"]]
```

Version 1 tree packets remain accepted. `encodeTreePacket` explicitly emits
that legacy format; `encodePacket` emits version 2. Version selection applies
to every auxiliary type/value/constructor field and the final proof. Mixed
representations and unknown versions reject.

There are no source files, imports, plugins, options, search paths or expected
types in the protocol. Expression tags are `bvar`, `sort`, `const`, `app`,
`lam`, `forall`, `let`, `nat`, `str` and `proj`. Numeric payloads are bounded
decimal strings. Names preserve string versus numeric components. Universes
support zero/succ/max/imax and explicitly declared auxiliary parameters; the
final proof is closed and monomorphic.

In a version 2 `dag` field, leaves retain the version 1 shape. Compound-node
children are decimal-string IDs instead of nested expressions: for example,
`["app","2","0"]`. Every reference must point to an earlier row. The final
string is the root ID, and every row must be reachable from that root. A new
pool is created for each field with its own declared universe context; rows
cannot refer into another field's pool.

Nodes share raw expression syntax. They contain no cached type judgments,
substitutions or metaprogram state. The decoder tracks the minimum enclosing
binder count required by each node, requires a closed root, and computes the
actual expanded path depth including universes. Small JSON nesting cannot hide
an excessive expression depth. Structural encoder keys preserve binder
annotations; binder names, metadata and the irrelevant let flag are canonicalized
as in version 1. The same kernel checks the complete term against the
independent expected proposition.

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

Version 2 charges its aggregate decoder budget for rows, references, name and
universe parsing, and the reverse reachability pass. It does not expand shared
nodes into duplicated trees. Bound-variable indices must be below the expression
depth bound before expression construction; projection indices must be below
the decoder-work bound. The client encoder separately uses the default depth
and visit caps per field and can conservatively reject source metadata nesting.
Kernel heartbeats still bound checking work; syntax sharing does not establish
a wall-clock or allocation bound for arbitrary proofs.

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

The registry currently has four tasks. Expanding input and output contracts,
multiple-target mutation policies, concurrent grading, task
registration review and automated invariant generation remains future work.
Instruction costs can be proved separately; acceptance here does not impose a
particular implementation cost or establish global optimality. The separate
`Write32.Accounting.claim_minimum` theorem proves at least two modeled
instructions for every actual accepted word-store execution on a useful input.
The checked store/RET routine attains two while retaining its actual OS return
history. See the [cost model](cost-model.md) for candidate scope, the necessary
useful-input condition and the distinction from CPU time.
