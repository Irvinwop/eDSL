# Compiled counter verification

`EDSL.Corpus.V1.CounterCounted.claim compiler` proves the full independent
`EDSL.Grading.ConcurrentTask.Counted64.Claim (CounterCounted.image compiler)`
for each complete frozen GCC or Clang `c_counter_worker` function. It covers
every independently admitted finite worker population, every uint32 request
per actual slot and every successful finite interleaving in the production
TSO64 model. Each requested operation is a unit RMW of a shared full64 cell.

The independent contract and the compiler candidate proof have separate
modules. The candidate reuses the existing compiler loop annotations and ranks;
admission supplies current machine and resource facts. Exact complete-file
certification, grading registration and a useful-execution certificate remain
separate integration work. Coverage remains **20/40 functions**, **40/80
artifacts** and **three distinct concurrent functions**.

## Use the independent counted-call contract

Import `EDSL.Grading.ConcurrentTask.Counted64.Contract` for the behavioral
specification, in namespace `EDSL.Grading.ConcurrentTask.Counted64`. Import
`EDSL.Corpus.V1.CounterCounted.Claim` for the proved frozen candidates, in
namespace `EDSL.Corpus.V1.CounterCounted`. Its `image compiler` names the
original callable base and complete function bytes: 49 bytes for GCC and
86 bytes for Clang. One Claim concerns one compiler's image shared by all slots.

`Requests before` is `Fin before.workers.length → BitVec 32`. The actual worker
list determines every slot, including the empty-population case. Independent
`Pre image target cell before requests` requires a well-formed `.ownedOnly`
state, initially empty FIFOs, a live valid common target and current entry
facts for every slot. RDI names that cell's address; low32 RSI equals that
slot's unsigned request. Zero and the maximum uint32 value are admitted, upper
RSI bits are arbitrary, and the initial target word is any full64 value.
Resource actors need not equal scheduler indices or be pairwise distinct.
Initial ordinary-store sequence counters are arbitrary.

Entry also requires the exact function code and original protected caller read,
current resources and grants, and the first authorized matching atomic handle
in the actual ordered handle list. Caller regions are pairwise disjoint and
separate from the function window. `ScalarCall64.Entry` supplies scalar stack
alignment, a clear direction flag, a nonwrapping stack pop and canonical
post-pop RSP; the protected continuation is canonical. Other initial registers
and flag bits are constrained only by these entry facts. `Pre` has no future
schedule, desired final value, compiler annotation, rank, or completion premise.

The full Claim proves all five obligations:

| Claim field | Guarantee from independent admission |
| --- | --- |
| `prefixes` | Every successful finite schedule satisfies `SafePrefix`, with full memory-cell frames, exact original resources/selectors and authenticated unit RMWs; own RMW counts never exceed requests |
| `completed` | Any such execution whose workers have returned has the complete same-run `Post`, including exact RET positions, per-slot counts, chronological history and the modular total |
| `enabled` | After any successful prefix, every current running slot has a successful retiring issue for either AF choice |
| `completion` | From every successful cut, a finite chosen suffix reaches `Finished` and the full `Post`; its issue bound is chosen before all future choice functions and offsets |
| `ownProgress` | One positive input-dependent bound per original slot applies to every successful finite interleaving and AF choice; no trace exceeds it, and reaching it entails an actual returned worker with an empty queue |

`SafePrefix.memory` equates the entire optional `AddressSpace.Cell` outside
`AddressSpace.qwordRegion cell.address`. It preserves mappedness, stored bytes
even behind inaccessible permissions, and every permission bit. Prefixes also
retain empty queues, the original population, resources, ordinary-store
counters, code, protected caller reads, the exact ordered selector and the
nonarithmetic flag mask. Every original observation retires one instruction;
drains and blocked attempts are excluded by the candidate proof. Callee-saved
registers have their ABI preservation obligation at return.

Each `Outcome` identifies the unique actual RET in the original action and
observation lists, with its checked `ReturnOrigin` and actual prefix state.
Every own RMW position is strictly before that RET, and the entire same-run
own count equals the independent request. A zero request still requires a RET.
`ReturnFrame` retains the original protected continuation, callee-saved GPRs,
nonarithmetic flags, clear DF, canonical RSP after adding eight, current
resources, an empty queue and the original store counter. `collect` observes
the actual returned RAX; this void call prescribes no RAX result and performs
no resource retirement through collection.

`Post` reads both the initial and current full64 counter words from the actual
RAM. Its `incrementCalls` history contains every RMW in chronological order,
using original observation indices and actual scheduler tids. Repeated event
payloads retain separate occurrences. The proof authenticates all events
against the common cell and unit delta; the history has no target or
expected-value filter and no supplied serial permutation. Peers may increment
between any two of a call's own increments. A whole void invocation is never
treated as one atomic fetch-add. The final equation is

`current.toNat = (old.toNat + Counted64.requestedTotal requests) % 2^64`.

`requestedTotal` sums the independent uint32 requests in Nat across all actual
Fin slots; reduction occurs only at the final full64 word.

Completion starts from the same collectively lifted ghosts at the exact
supplied cut. For `choices : Nat → Nat → Bool` and `offset : Nat → Nat`, a
suffix uses index `offset tid + ChoiceTrace.issues tid prior` for each thread.
The prior need not match those choices. When it does, the concatenated trace
retains the choices continuously; otherwise the suffix alone has the stated
choice property. Its full `Post` is for that concatenated actual execution.
Already-returned slots keep their replies and require no further own issues.

The separate `ownProgress` bound is fixed before all actual traces, using the
positive initial measure of each slot's existing compiler rank. Its proof
retains those exact trace ghosts and bounds own issues plus residual measure
by the initial measure. It covers every successful finite interleaving, beyond
the particular suffix constructed by completion. A scheduler may still
withhold a worker's turns. These bounds require no fairness and establish no
minimum operation count, CPU-time bound or wall-clock termination guarantee.

This client uses only independent inputs and the public proved Claim:

```lean
import EDSL.Corpus.V1.CounterCounted.Claim

open EDSL EDSL.OS
open EDSL.Grading.ConcurrentTask.Counted64

example (compiler : Corpus.V1.CounterCommon.Compiler)
    (before : TSO64.State) (target : Atomics64.CellId64)
    (cell : Atomics64.Cell) (requests : Requests before)
    (pre : Pre (Corpus.V1.CounterCounted.image compiler)
      target cell before requests)
    (actions : List TSO64.Action)
    (actual : TSO64.State × List TSO64.Observation)
    (run : TSO64.schedule before actions .ownedOnly .arithmetic = .ok actual) :
    SafePrefix (Corpus.V1.CounterCounted.image compiler)
      target cell before requests actual := by
  have proved : Claim (Corpus.V1.CounterCounted.image compiler) :=
    Corpus.V1.CounterCounted.claim compiler
  exact proved.prefixes before target cell requests pre actions actual run
```

The candidate's `Admission` module derives the existing per-slot subjects,
ranked cohort and initial ghosts from independent `Pre`. `PrefixEvents`,
`PrefixMemory` and `PrefixFrames` prove prefix safety. `Conservation`, `Outcomes`
and `Post` supply the complete history and returns; `Progress` supplies
enabledness and the universal own-issue budgets. `Completion` connects the
chosen suffix to the full output, and `Claim` assembles all five fields.

These are conditional machine-model results. The coherent scalar WB RAM,
full64 address/alignment profile, stable translation without hidden aliases,
long-mode/CET-off, represented CPU feature state and protected-resource
assumptions remain explicit. Physical CPU/Linux, whole-kernel, source/compiler
and native join correspondence remain outside the result.

## Compiler annotations and earlier adapters

The complete frozen GCC and Clang `c_counter_worker` windows have per-worker
annotations against the production TSO64 scheduler. For every admitted actual
finite schedule whose selected worker has returned, the proofs establish exactly
`iterations.toNat` unit increments and the common void-call return contract.
They cover every unsigned 32-bit iteration count, arbitrary upper RSI bits and
initial flags, and well-formed incoming FIFOs.

| Direct import | Complete window | Public APIs |
| --- | --- | --- |
| `EDSL.Corpus.V1.CounterGCC` | 49 bytes / 17 nodes | `rules`, `annotations`, `entry_of_pre`, `completed_count` |
| `EDSL.Corpus.V1.CounterClang` | 86 bytes / 28 nodes | `rules`, `annotations`, `entry_of_pre`, `completed_count` |

The namespaces match their modules. `entry_of_pre` derives the current Entry
from the common independent `Pre`; it takes no future run or generated block.
The builders use canonical caller and original-stack facts supplied by that Pre.
GCC retains both RET paths and its two-increment loop; Clang retains the
remainder loop, eight-increment loop and zero-remainder path with arbitrary RDX.
Their complete checked graphs are described in [mixed instruction graphs](mixed-cfg.md).

The earlier APIs below compose these annotations over the production scheduler.
Returned-run theorems apply to a supplied successful execution. Ranked completion
constructs one finite returned execution from present admission, exact worker
slots and empty queues. It can then establish the two-worker value, byte frame
and logical resource cleanup for that same execution. The loaded-input adapter
constructs the present admissions from one complete frozen ELF and actual
resource setup and attachment. A fixed-count adapter also constructs an actual
overlapping prefix and completes and cleans up that same execution. The complete
corpus certificate gates remain open, so coverage is unchanged. None of these results
asserts that every scheduler returns a worker.

Import `EDSL.Corpus.V1.CounterAssertions` for the common assertions, in namespace
`EDSL.Corpus.V1.CounterCommon`:

- `Call` independently names the pointer, unsigned 32-bit iteration count,
  atomic target cell and return address. `Site` fixes the compiler window and
  original worker/resources. `descriptor` reuses the complete checked graph.
- `Pre` requires current loaded code, well-formed resources, running entry PC,
  RDI, low32 RSI, protected caller stack, a canonical return target and the
  scheduler's actual first matching atomic selector linked to the target cell.
  It requires no future execution, initial shared-word value, empty FIFO,
  upper32 RSI value, or initial flag value. Actor and worker index are distinct.
- `LiveData` carries the pointer, caller stack, saved ABI context and current
  selector. `OwnIncrements` authenticates every earlier own RMW with its real
  typed issue and compiler-specific ADD or INC tag, along with unit delta and
  independently named actor, pointer and target.
- `Inv` combines those shared facts with compiler-local register arithmetic,
  parameterized by the exact natural-number count of the full history.
  `Inv.idle` preserves them through authenticated peer issues, FIFO drains and
  unchanged own blocked attempts.
- `Post` requires exactly the requested number of own RMWs, authenticated unit
  increments, actual returned phase and caller PC, callee-saved registers,
  nonarithmetic flags, and the original RSP plus eight in modular Word arithmetic.
  It makes no RAX-result or current shared-memory assertion. `stablePost` allows
  later idle positions; `completed_count` projects to the entire observation
  list of a successful finite returned schedule **given separately proved
  compiler annotations and current Entry**.

The shared `EDSL.Corpus.V1.CounterIncrement` adapter constructs current locked
continuations from the actual selected effect, preserving the complete typed
issue, next frame and context, historical unit-increment witnesses and exact
Nat tally. The compiler modules supply their register arithmetic and graph edges.

`Mixed.LocalRules` combines an idle-stable invariant and one current instruction
rule per graph node. `LocalRules.annotations` generates the existing finite
blocks from the checked depth decrease, so neither compiler repeats scheduler
or block-induction proofs. See [mixed resumption](mixed-resumption.md).

The generic current ordinary-step adapter is in
`EDSL.OS.TSO64.EffectSimulation.Mixed.CallerContinuation` and the public
`EDSL.OS.TSO64.EffectSimulation` umbrella. `One.of_callerContinuation` takes CPU
execution, protected reads and a result continuation for every flag choice.
It derives current authority, read/queue readiness and the real ordinary or
returned finish with the existing FIFO. It has no additional byte-window bound.

`EDSL.OS.TSO64.Increment64` specializes an actual arithmetic machine effect to
INC or encoded ADD-imm8(1). It retains the complete effect, current old/new word,
authorized handle/cell, actual instruction length, RIP, and every GPR. It does
not establish the scheduler's first selector by itself. XADD is excluded.

`EDSL.X86.Sequential.CounterArithmetic` supplies unsigned32 Nat laws for SUB2,
signed ADD-imm8(-8), LEA32(base-1) despite arbitrary upper bits, AND7 modulo eight,
and low-byte AND1 modulo two. Arithmetic parity is separate from the CPU parity
flag; ADD and SUB retain their different flag semantics.

Build the support directly with `lake build CounterContractSupport`. The target
has 51 roots for the independent contract, compiler adapters, complete-file
certificates and generic helper modules. Their imports also
belong to `EDSL.All` and the full-project fresh certificate aggregate.
Universal Lean proofs check the stated laws; no additional fixed-value tests
are needed for these adapters.

Import `EDSL.Corpus.V1.CounterCohort` for the common
`two_completed_total` theorem. It takes two independently admitted calls, their
actual initial scheduler slots zero and one, an exhaustive two-worker initial
state, an independently registered common cell and its current initial word.
For an actual successful finite owned-only arithmetic schedule whose two workers
have returned, it derives an actual final RAM read with

`final.toNat = (initial.toNat + left.iterations.toNat + right.iterations.toNat) % 2^64`.

Either worker may use GCC or Clang, and the uint32 requests may differ. Actors
remain separate from scheduler slots. Counts retain every occurrence in the
complete observation list, including identical event payloads. Each worker's
event facts come from its own checked completion proof; no equality between
independently produced stateful ghost histories is assumed. The final RAM value
uses the actual OS history conservation theorem. Nonempty initial FIFOs are
permitted for this value theorem because checked owned-only publications cannot
modify registered atomic allocations.

`EDSL.OS.TSO64.EffectSimulation.Mixed.Cohort` supplies the separate generic
queue-closure API. Independently annotated subjects share a family/profile and
a source caller-only policy law. Present initial Entries, exhaustive live-slot
coverage and empty initial FIFOs derive empty FIFOs throughout the actual run.
Every original action/observation position is retained as an ordinary, RET or
native RMW issue; successful drains and blocked attempts are excluded. Each
subject keeps its own related ghost at the same actual prefix state. Each
subject may have a different instruction graph.

For frozen counter calls, import `EDSL.Corpus.V1.CounterCohortClosure` and provide
a collection of `CohortSubject` values with their present `Pre` and owned-only
profile. `counterCohort` selects the existing GCC/Clang annotations, and
`counterCohort_entries` derives all initial Entries. With exhaustive initial slot
coverage and empty queues, `counterCohort_closed` supplies the generic closure
result. Clients do not reprove instruction rules or scheduler induction.

The supporting `Mixed.IssuePreservation` API extracts the actual current typed
ordinary issue and proves exact queue, store-counter, resource and world
preservation under the caller-only policy, including RET. `Mixed.EventCounts`
partitions RMW occurrences across a duplicate-free exhaustive tid list in Nat,
and connects same-target unit events to the OS history's mathematical input sum.
Neither list arithmetic nor queue closure alone establishes a final RAM value.

For logical resource cleanup after an actual returned execution, import
`EDSL.Corpus.V1.CounterRetirement`. `counterCohort_retireAll` derives current
cleanup admission and capability separation from the original manifests,
initial empty queues and the same successful schedule.
`two_completed_retired_total` carries the modular RAM sum through that actual
cleanup. The three generic lifecycle modules provide the reusable operations
and proofs; see [Worker resource cleanup](resource-cleanup.md) for admission,
outputs and limits.

## Preserve RAM outside the counter

Import `EDSL.Corpus.V1.CounterFrame` for `two_completed_frame` and
`two_completed_total_frame`, in `CounterCommon`. For an actual finite returned
pair, initial empty queues and the independently registered common cell derive
byte equality outside that cell's modular eight-byte span. The precise query
condition is `8 ≤ (query - cell.address).toNat`. The combined theorem retains
the modular total above and this byte frame for the same final RAM.

The generic `Mixed.Cohort.schedule_frame` proof obtains actual RMW addresses
from checked authorization and the stable cell registry. Clients supply the
observed cell identities, not desired operand addresses or a future RAM frame.
Current caller-only issue evidence handles ordinary instructions and RET;
cohort closure retains empty queues through the same actual schedule.

An inherited FIFO may still drain writes. The earlier count and value APIs
permit those queues under their stated profiles; this stronger byte-frame API
requires them to be initially empty.

## Construct a finite returned execution

Import `EDSL.Corpus.V1.CounterCompletion` for the following `CounterCommon`
APIs:

| API | Inputs and result |
| --- | --- |
| `counterCohort_complete` | Independently admitted subjects, exact slots `0..n-1`, a well-formed initial state with exactly `n` workers, empty queues and arbitrary per-thread AF choices yield an actual finite returned schedule |
| `two_complete_total_frame` | Two independent admissions in slots zero and one, exactly two workers, empty queues and one registered common target yield that schedule, its modular sum and its outside-byte frame |
| `two_complete_retired_total_frame` | The same initial inputs, cleanup shapes and capability separation additionally yield actual production resource retirement, capability revocations and preservation of the result and byte frame |

The compiler adapters select existing local rules and rank laws directly from
each independent `Pre`. The initial invariant comes from that admission;
clients do not provide a future successful schedule, a returned state, a desired
result or a termination oracle. Different compilers may be selected only when
their independent loaded-code admissions hold together in the same initial
state; the APIs do not arrange such a combined image.

The returned `RankedCohort.Suffix` contains actual scheduler execution,
well-formed final state, empty final queues, actual returned workers, retained
per-worker histories and typed retirement positions. Every AF value follows
that thread's own issue index. Its `issue_upper_bound` bounds the length of the
constructed issue-only trace by the initial sum of ranks. This proves existence
of one finite completion for every choice function, with no fairness premise.
It does not force an arbitrary scheduler to finish, compute a minimum number
of operations or measure CPU time. The proof does not add a native execution
witness or corpus certificate.

## Construct inputs from the complete loaded ELF

The following three modules construct and complete two calls to the same frozen
counter function in one compiler's complete loaded ELF:

| Direct import | Public APIs |
| --- | --- |
| `EDSL.Corpus.V1.CounterResources.Image` | `admitted`, `programSpace_eq`, `setup_total`, `resources_setup`, `full_image` |
| `EDSL.Corpus.V1.CounterResources` | `initial`, `first_attached`, `second_attached`, `pre`, `wellFormed`, `quiescent`, `cleanupShape`, `separate`, `registered`, `initial_read`, `full_image` |
| `EDSL.Corpus.V1.CounterLoadedInputs` | `Execution`, `Output`, `complete` |

Each namespace matches its module. `Image.admitted` retains the original full
file, tables, named symbol and entire declared extent, with the original GCC
64-byte and Clang 128-byte admission caps. The selected functions remain 49 and
86 bytes respectively. `programSpace_eq` identifies the indexed space with the
complete installed ELF space, including nontext mappings outside the function
window.

`Image.resources_setup` records the actual checked `PlainResources.setup`
operation. The manager adopts the function allocation, borrows it separately
for the two logical actors, allocates and protects their private caller slots,
initializes a fresh target qword, enrolls that cell and issues two handles.
`setup_total` proves success for either compiler and every initial word.
`CounterResources.initial` is the output of two successive production
`TSO64.attach` operations; the second consumes the first operation's result.
The attached workers occupy exactly scheduler slots zero and one. Their logical
actors are 11 and 12; these are model principals, with no native identity
authentication claim.

All parameters to `CounterLoadedInputs.complete` are ordinary input values:

| Parameter | Domain |
| --- | --- |
| `compiler : CounterCommon.Compiler` | GCC or Clang; one compiler supplies both calls |
| `old : X86.Word` | Any 64-bit initial counter word |
| `count : Fin 2 → BitVec 32` | Two independent uint32 counts, including zero and the maximum value |
| `upper : Fin 2 → BitVec 32` | Independent upper RSI halves; each RSI is `upper slot ++ count slot` |
| `flags : Fin 2 → X86.Word` | Independent complete modeled initial flag words, without a DF restriction |
| `choices : Nat → Nat → Bool` | Arbitrary AF choices indexed by scheduler slot and that slot's own issue index, starting at zero |

This constructor fixes RDI to the target at `0x10000`, RSP to `0x700008` or
`0x710008`, and RIP to the original compiler-specific function address. The
protected caller words contain `0x654320` and `0x654330`. Every GPR other than
RDI, RSI and RSP initially equals `0x8877665544332211`; the construction does
not quantify over all initial GPR assignments. Each store sequence counter
starts at zero independently of the iteration count.

The actual setup and attachments derive both independent `Pre` proofs,
well-formedness under `.ownedOnly`, exact worker slots and exhaustive coverage,
empty queues, cleanup shapes and capability separation. They also derive
current code, protected caller reads, the ordered atomic selector, the live
cell registry and the read of `old`. These facts are proved inputs to the
completion adapter; clients supply no admission proof, setup-success premise,
future successful schedule, returned state or desired counter value.

`CounterLoadedInputs.complete` proves
`Nonempty (Output compiler old count upper flags choices)`. Each `Output`
retains the following evidence for the same constructed execution:

| Output | Meaning |
| --- | --- |
| `execution` | Actual finite production TSO64 schedule, well-formed returned endpoint with empty queues, lifted per-worker histories, typed retirement positions, chosen AF issues and a modeled issue upper bound |
| `retired`, `valid`, `workers`, `contexts`, `history`, `revoked` | Successful `Lifecycle.retireAll execution.final`, a well-formed cleaned state with no workers, contexts in reverse worker order, an actual logical cleanup history and revoked worker capabilities |
| `resources`, `cells`, `ram`, `targetLive` | Cleanup retains the execution endpoint's resource store, cell registry and current published RAM; the target stays registered |
| `counter`, `total` | A successful read from the cleaned world's current RAM and `value.toNat = (old.toNat + (count 0).toNat + (count 1).toNat) % 2^64` |
| `frame` | For every `query` with `8 ≤ (query - PlainResources.standard.target).toNat`, the cleaned RAM byte equals the actual initial RAM byte |
| `image` | Every cell loaded from the original complete ELF remains exactly equal in the cleaned resource space, including its byte and every permission bit, also in nontext mappings outside the executable function window |

The full-cell result combines target freshness, readable loaded cells, the
schedule's permission frame and the outside-byte frame. It retains each loaded
cell's mappedness and complete permission record as well as its contents.
Cleanup follows this execution's actual returned state and retains its current
RAM. It does not restore a snapshot from an earlier return.

GCC and Clang are separate homogeneous cases. The constructor does not combine
the different compiler images in one address space or establish a compatible
mixed-image admission. The theorem constructs one finite returning model
execution for each choice function. It does not require fairness or establish
termination of every schedule, a prescribed overlapping prefix, optimal cost,
native execution or join correspondence, hardware/source/compiler refinement,
or whole-OS security. The existing long-mode/CET-off, coherent scalar WB RAM,
stable translation/no-alias and protected-resource assumptions remain explicit.

## Construct an overlapping prefix and complete the same execution

`EDSL.Corpus.V1.CounterOverlap` provides `construct_prefix` and `complete`,
`LoadedPrefix` and `LoadedOutput` use the `Prefix`, `Output` and `Cleanup`
records.
It uses the same loaded-resource constructor with fixed uint32 requests
**3 and 9**. The compiler, old64 word, upper RSI halves, complete modeled
initial flags and per-thread AF choices remain arbitrary; other registers
retain the documented constructor values. GCC and Clang remain separate
homogeneous cases.

`construct_prefix` constructs three actual schedule segments selected in order
zero, one, zero, each ending at its segment's first actual RMW observation. The
actual concatenated observation list has RMW issuer projection **`[0, 1, 0]`**.
At the cut, actual observations and the exact final ghost histories each have
RMW counts **2 and 1**, and both actual workers are still live and running.
Other instructions remain in the recorded action and observation lists.

`complete` proves `Nonempty (LoadedOutput compiler old upper flags choices)`.
Its `lead` retains that prefix; `suffix` starts from `lead.final` and precisely
`lead.finalGhosts`. Each suffix AF offset counts that thread's issues over the
whole prefix. The `actual`, `lifted` and `chosen` fields retain the concatenated
production schedule, its same exact ghosts and histories, and continuous AF
choices for the entire execution. No successful future prefix, schedule, return
or desired memory value is a caller-supplied premise.

`cleanup` records successful production `Lifecycle.retireAll suffix.final`,
well-formedness, no remaining workers, reverse-order contexts, revocations and
an actual logical cleanup history. It retains that endpoint's current resource
store, cell registry and RAM, keeps the target registered, and proves a current
counter read equal to **`(old.toNat + 12) % 2^64`**. Its outside-byte frame
compares the cleaned current RAM with the actual initial RAM. This output has
no additional full loaded-ELF cell-preservation field; the arbitrary-count
`CounterLoadedInputs.Output.image` theorem above is a separate result.

These loaded-input and overlap modules are registered in the catalogue and
full-project fresh imports. The overlap result remains specific to requests
3/9 and one constructed model execution. The universal counted-call Claim
above applies separately to every independently admitted finite population.
Neither result supplies native correspondence, fairness, minimum cost or
additional corpus credit.

## Reuse the completion infrastructure

The `EDSL.OS.TSO64.EffectSimulation` umbrella exposes the generic layers;
none imports a frozen counter client or grading:

| Direct import under `EDSL.OS.TSO64.EffectSimulation.Mixed` | Reusable contract |
| --- | --- |
| `LocalInvariant` | Retain the every-node invariant on the same explicit ghost through actual steps and traces |
| `RankedLocal` | Positive local ranks, idle stability and strict decrease on actual own retirement; current running-worker enabledness |
| `RankedPotential` | Finite sums of Nat measures, pointwise nonincrease and one-component strict decrease |
| `ChoiceTrace` | Issue-only AF choices from arbitrary per-thread offsets and concatenation for interleaved threads |
| `RankedCohort` | One subject per actual slot; finite returned completion and an issue upper bound from present current invariants |
| `RankedPrefix` | Retain exact collective ghosts across an executed prefix and construct its finite completion with continuous per-thread choices |
| `CohortFrame` | Byte preservation outside a registered common cell through an actual caller-only schedule |

For another program, provide its checked mixed graph, independent entry and
postconditions, and `LocalRules` with an invariant at each node. These reuse
the existing scheduler and local-invariant fold. To construct completion, also
prove `RankLaws`: positivity at running nodes, equality under authenticated
idle extensions, and strict decrease for both running successor continuations
of an actual retirement. Assemble subjects with a common profile and RMW
family, exact exhaustive slots and caller-only policy. With present empty
queues, `RankedCohort.complete_from_current` works from the current ghosts and
arbitrary choice offsets; `complete` starts each offset at zero. The generic
fold preserves each subject's own full history through the same actual steps.

After an interleaved prefix has executed, `RankedCohort.complete_after_prefix`
lifts its exact current ghosts and constructs a new suffix. It proves execution
and choice accounting for the concatenated trace. Only the prefix is supplied
as a successful run; the future suffix follows from the current invariants and
ranks. Its action bound is the prefix length plus the potential at the cut.

`ChoiceTrace.chosen_append` accounts for every thread's issues in the entire
prefix, including repeated and interleaved issuers. The separate
`EDSL.Grading.ConcurrentTask.ChoiceTrace` bridge proves that the zero-offset
predicate equals the existing Plain64 grading predicate. OS modules have no
grading dependency. Program-specific functional results, target-cell evidence
and lifecycle admission remain separate obligations.

The following additional helpers are reusable through their direct imports.
They supply generic proofs; counter-specific unit deltas, independent requests
and entry-to-candidate admission are proved in `CounterCounted`.

| Direct import | Public API and scope |
| --- | --- |
| `EDSL.OS.TSO64.EffectSimulation.Mixed.RankBudget` | `RankedCohort.prefix_with_own_issue_budget`, `own_issue_budget_of_schedule` and `returned_at_own_issue_budget`: own issues plus residual rank for the exact trace ghosts, with actual returned phase at the budget |
| `EDSL.OS.TSO64.CellFrame` | `CellFrame.schedule_frame`: whole optional cells outside a registered qword for actual schedules without drains, with every actual RMW targeting that cell; either authority profile and RMW family |
| `EDSL.OS.TSO64.PositionHistory` | `PositionHistory.schedule_sequential`: chronological original positions and actual tids, preserving every RMW occurrence and the actual initial/current words under complete target coverage in `.ownedOnly` |
| `EDSL.Concurrency.ModuloCounter.Relabel` | `ModuloCounter.Sequential.relabel`: preserve chronological input/output values while changing point and thread labels, without an injectivity requirement |
| `EDSL.OS.TSO64.RMWSelection` | `TSO64.rmw_selection`: recover the actual RMW's first current authorized matching handle, selected cell, operand address and resource actor |
| `EDSL.OS.TSO64.ReturnPositions` | `ReturnPositions.returned_position_of_final`, `returned_unique` and `rmw_before_return`: recover exact RET boundaries and origin, preserve returned frames and exclude later own issues/RMWs |
| `EDSL.OS.TSO64.EffectSimulation.Mixed.RetirementTrace` | `Cohort.RetirementTrace.no_drains` and `all_retired`: derive whole-trace facts from the classification of every original scheduler position |

The generic cell frame does not require initially empty queues: its explicit
no-drain premise is enough. The counted candidate derives that premise from
caller-only closure and its independently required empty initial queues.
Position history permits arbitrary deltas; unit increments and request totals
are separate counter proofs. The rank-budget helper consumes the same lifted
trace and never replaces its ghosts with another closure witness.

## Construct a counted-stage rank

Import `EDSL.OS.TSO64.EffectSimulation.Mixed.CountedRank` to build the existing
`Mixed.RankLaws` from a counted-loop stage certificate. Call
`Mixed.RankLaws.ofCountedStages rules requested stride stage bounds ordinary room`.
The descriptor, postcondition and local rules can describe any supported mixed
graph; the constructor contains no compiler-specific graph or stage table.

| Input | Required evidence |
| --- | --- |
| `rules` | Existing local invariant and actual instruction continuations |
| `requested` | Independent Nat bound on this thread's RMW occurrences |
| `stride`, `stage` | Every graph node has a positive stage strictly below the stride |
| `ordinary` | Stage decreases across every ordinary graph edge, including arrivals at cutpoints |
| `room` | At a locked node, the invariant implies the full own-RMW count is still below the request |

The returned rank is
`stride * (requested - Counts.logRMW d.tid history) + stage node`.
The shared proof derives idle stability and strict successor decrease from the
actual retirement evidence and issued observation. Both cut and interior
arrivals retain their invariant. A RET retains the original postcondition.
Strict room prevents Nat subtraction from saturating when another RMW occurs;
the positive stage also accounts for ordinary instructions on a zero-request
return path.

The GCC and Clang `CounterRanks.rankLaws` adapters now supply their existing
stage and room witnesses to this constructor. Their public contracts and the
independent completed-call Claim remain unchanged. The older compiler rank
helper names delegate retirement and arrival proofs to the shared implementation.

This rank counts occurrences regardless of an RMW's payload. Correct target,
unit delta, ABI and memory preservation require their separate proofs. The
constructor supplies no fairness, minimum-operation, hardware correspondence,
packet-admission or additional corpus result.

## Artifact certificates and coverage

The generic [complete-file certificate](counted-certificates.md) is
implemented in `EDSL.Corpus.CountedCertificate`. It binds an externally
supplied complete ELF file, exact symbol name and explicit byte cap to the
unrestricted independent Claim and a separate completed overlapping execution
from actual loaded resources. `EDSL.Corpus.V1.CountedCertificates.gcc` and
`.clang` construct these certificates for both complete frozen compiler files.

The loaded adapter covers every old64 word, upper RSI pair and DF-clear
modeled flag pair. Its useful overlap family covers every per-thread AF stream;
the original 0,1,0 RMW positions precede both actual RETs of the same completed
execution. The stored Post preserves every installed optional memory cell,
including permissions, through that execution and its logical cleanup.

An installed data-only Counted64 grader, task/registry integration and complete
corpus admission remain pending. The existing packet policy has not been
shown to admit these full-file proofs. There is no new certified corpus row:
coverage remains **20/40 functions**, **40/80 artifacts** and **three distinct
concurrent functions**.

All results retain the existing long-mode/CET-off, coherent scalar WB RAM,
stable translation/no-alias, ownership and protected-loan assumptions. Complete
corpus admission, source/compiler preservation, physical CPU/Linux and native
join correspondence remain separate work. No fairness, minimum-operation or
whole-system security guarantee follows from these model theorems.
