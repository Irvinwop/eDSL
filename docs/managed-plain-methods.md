# Reusable managed load/store methods

`EDSL.X86.VCGen.PlainMethods` uses one proof family for checked padding followed
by a qword load into RAX or a qword store, then RET. New byte windows supply an
operation descriptor, padding and current OS resources. The shared proofs handle
instruction execution, interference, queue draining, return frames and the own
instruction count; clients do not repeat an induction for each compiler output.

The family also extracts indexed machine calls and complete finite call cohorts.
The complete scanner event list matches those calls under the declared interface
orders. At an initialized empty-queue boundary, the shared history theorem also
constructs their legal finite atomic graph. Shared rules construct a returned
mixed cohort from an actual execution prefix and frame all RAM cells outside
its target and incoming-queue footprints. A separate, present-state admission
contract connects registered load/store images to this engine. The full
independent `Plain64.Claim` combines safety, behavior, chosen completion and
closed history for any supported catalog. Useful exact-ELF resource populations,
their homogeneous/mixed executions and source-order justification remain
separate obligations.

## Describe and check the code

`Operation.load address` reads into RAX. `Operation.store address source` captures
the source register before execution. Both use the existing address semantics,
including supported base/index/displacement forms and register aliases. RSP may
be a store source; a load that overwrites RSP is available through the lower-level
primitive rule, with no total-return guarantee from this family.

The checker uses the production decoder at every padding, access and RET node.
It checks the exact final extent and retains the existing 64-byte window limit.
It rejects a matching prefix with extra suffix bytes, incorrect operands or width,
missing RET and undeclared padding. Larger or richer functions need their own
supported block/CFG interface.

```lean
import EDSL.X86.VCGen.PlainMethods
open EDSL X86 VCGen.PlainMethods

def loadBytes : List Byte :=
  [0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x8b, 0x07, 0xc3]

example : Shape loadBytes (.load (.base .rdi)) 0 [.endbr64] :=
  (check_sound (by decide +kernel :
    check loadBytes (.load (.base .rdi)) [.endbr64] = true)).2
```

This establishes code shape. Functional results additionally require the current
machine/resource admission below. ENDBR64 retains the explicit CET-off target
assumption; recognizing its bytes does not establish the physical control state.

## Supply current resources

`Method` records the operation, exact bytes and code base, original registers and
flags, resources, complete managed reference, original queue/counter boundary
and canonical caller return. Its effective address uses the original registers;
it is not reevaluated after a load overwrites RAX. The source request fixes an
acquire load or release store independently of observed memory. MOV bytes alone
do not establish source-language intent.

`Current` requires current well-formed resources under `sharedCell`, current
published code within the original code loan, the original protected caller read,
and the exact current atomic-handle selection. It stores no invocation-memory
snapshot, desired result, successful future execution or graph-legality premise.
`At` supplies the checked entry/cutpoint, full register/flag/resource assertions
and a queue frame. Initial queues may contain any currently valid mixed entries.

`ManagedAccess.issue_loadMem64` and `issue_storeMem64` derive real enabled
primitive steps from these current conditions. A load obtains its value from the
actual own overlay or current published RAM. A store appends the complete
selected reference, original source value and actual counter to the existing
FIFO, then increments the counter once. It leaves the published world unchanged.
Ordinary-grant exclusion at a managed cell follows from current reservation and
allocation separation; the proof does not silently override lookup priority.

`ManagedReturn.step_ret` derives RET under either authority profile with valid
nonempty queues. It uses the current original caller slot and canonical target,
preserving the world, authority, FIFO and counter. Its response is the saved
full-width RAX. A logical store reply is unit, separately from that machine value.

## Admit a registered image independently

`Grading.ConcurrentTask.Plain64` defines a current-state contract independently
of method cutpoints and future execution. A `Catalog` lists sites, each pairing
an acquire-load or release-store `Kind` with a complete callable `Image`
(base and bytes). Each actual initial worker slot selects an `Input` containing
that image, the persistent target identity and full cell descriptor, a logical
occurrence label, and a full64 value for stores. Loads have no supplied reply
and leave their unused RSI unconstrained. The logical occurrence label does not
stand in for the machine's store-allocation counter.

`Entry` binds the running worker to executable code, RDI and any store RSI,
current whole-qword authority, the protected original caller and scalar ABI
entry conditions. These include stack alignment, clear DF, a nonwrapping pop,
canonical post-pop RSP and a canonical caller continuation. `Pre` covers every
actual slot, current resource validity, private caller regions and code/caller
separation. Its resource validity includes each actual incoming FIFO entry;
nonempty queues and nonzero counters are permitted. `ClosedPre` separately adds
empty initial queues for whole-graph admission.

`Pre` contains no method, checked shape, cutpoint, desired reply or successful
future-run premise. `OS.PlainCallAdmission64.StaticShapes catalog` supplies
separate static proof evidence: the production checker accepts each site's bytes
and padding for its fixed load from `[RDI]` into RAX or store of RSI to `[RDI]`.
That evidence is reusable across values, cells, actors and worker slots.
`admit_slot` combines it with the actual slot's `Pre.entry` to derive an
`Admitted` invocation:

```lean
import EDSL.OS.PlainCallAdmission64
open EDSL
open Grading.ConcurrentTask.Plain64

example {catalog : Catalog} (static : OS.PlainCallAdmission64.StaticShapes catalog)
    {initial : OS.TSO64.State} {inputs : Fin initial.workers.length → Input}
    (pre : Pre catalog initial inputs) (tid : Fin initial.workers.length) :
    Nonempty (OS.PlainCallAdmission64.Admitted (inputs tid) initial tid.val) :=
  OS.PlainCallAdmission64.admit_slot static pre tid
```

`Admitted` retains the exact bytes/base, fixed operation, target descriptor,
current selected reference, independent request, scalar entry facts and logical
occurrence. Its `initialQueue` is the actual worker's full FIFO and counter.
`invocations static pre` supplies the complete initial family for the completion,
footprint and history APIs below. The admission bridge supplies the actual
invocations used by the full contract; useful final-ELF resource instances
remain a separate certification gate.

## Use the full independent contract

Import `EDSL.OS.PlainCall64` and apply `OS.PlainCallClaim64.claim static`.
The result is `Plain64.Claim catalog`, with these obligations proved for every
current-state `Pre` admitted by that catalog:

| Field | Guarantee |
| --- | --- |
| `prefixes` | Every actual successful finite prefix satisfies `SafePrefix` |
| `completed` | Every actual returned cohort has the complete independent `Post` |
| `whole` | `ClosedPre` and an actual finished run yield the full `ClosedPost` |
| `enabled` | Each currently running worker can retire its next instruction for either AF choice |
| `completion` | Any successful prefix admits an issue-only suffix with chosen AF per thread and every worker returned |
| `closure` | A returned cohort admits actual production drain closure, `Finished`, the concatenated run and `Post`; an empty initial boundary also yields `ClosedPost` |
| `bounded` | A positive uniform own-issue upper bound; the shared proof supplies 64 |

For example, the same claim constructs completion for arbitrary admitted sites,
full64 input words, resources and successful prefixes:

```lean
import EDSL.OS.PlainCall64
open EDSL Grading.ConcurrentTask.Plain64

example {catalog : Catalog}
    (static : OS.PlainCallAdmission64.StaticShapes catalog)
    {initial : OS.TSO64.State} {inputs : Fin initial.workers.length → Input}
    (pre : Pre catalog initial inputs) {prior : List OS.TSO64.Action}
    {actual : OS.TSO64.State × List OS.TSO64.Observation}
    (success : OS.TSO64.schedule initial prior .sharedCell = .ok actual)
    (choices : Nat → Nat → Bool) :
    ∃ suffix finished, ChosenIssues choices suffix ∧
      OS.TSO64.schedule actual.1 suffix .sharedCell = .ok finished ∧
      OS.TSO64.Returned finished.1 :=
  (OS.PlainCallClaim64.claim static).completion
    initial inputs pre prior actual success choices
```

Clients supply the separate checked code shapes and independent present
resources, then reuse the contract. They do not prove a program-specific
execution induction or supply a desired result, successful future step or
history. `Claim.mono` restricts a mixed catalog to a subcatalog without repeating
its behavioral proofs. The claim concerns the modeled finite cohort;
certification of the frozen ELF artifacts still needs useful populations and
actual homogeneous/mixed executions from the complete loaded files.

## Reuse the body proofs

`advance` derives the next actual own issue at each unfinished cutpoint.
`schedule_preserves` covers every successful finite interleaving of the admitted
scheduler, including peer issues and own/peer drains. `complete` constructs a
completion from any current cutpoint using exactly its remaining own issues,
with the exact caller-supplied AF sequence. Its conclusion identifies the action
list as `List.range remaining` mapped to those issues. It requires no preparatory
drain or empty FIFO.

`all_completed` gives a full register/flag/caller/resource result for an actual
completed run, exactly `padding.length + 2` own instructions, and `OneAccess`.
That access witness retains its original action position, same-run prefix,
actual decoded instruction/effect, and the load's actual local read/source or the
store's original value/reference/occurrence. Coverage excludes an unrecorded
second own access; equal observed values cannot replace the supplied execution.
The load reply is retained through RET and subsequent interference.

The queue frame permits head drains between stages and after return. The store
may therefore have returned with its entry pending or with it already published.
Neither case is treated as publication inside the call interval. Arbitrary
initial entries retain an explicit provenance boundary: validity alone supplies
no earlier issue history or globally unique occurrence tags.

The completion theorem constructs one schedule. It implies no scheduler fairness
or eventual completion of every schedule. Own instructions, drain actions and
physical elapsed time are different costs; this count is no unrestricted
minimum-instruction or CPU-timing theorem.

## Complete a mixed cohort from an actual prefix

`cohort_complete_after_prefix` takes one `Invocation` for each actual initial
worker and an arbitrary successful prefix under `sharedCell`. The methods may
have different load/store operations, bytes, padding, resources and incoming
queues. It derives every present cutpoint through `Invocation.cut_after_prefix`;
the caller supplies no future cutpoint, completed family or successful suffix.

```lean
import EDSL.X86.VCGen.PlainMethods.Completion
open EDSL X86.VCGen.PlainMethods

example {initial : OS.TSO64.State}
    (invocations : (tid : Fin initial.workers.length) → Invocation initial tid.val)
    {prior : List OS.TSO64.Action}
    {actual : OS.TSO64.State × List OS.TSO64.Observation}
    (success : OS.TSO64.schedule initial prior .sharedCell = .ok actual)
    (choices : Nat → Nat → Bool) :
    ∃ suffix result, OS.TSO64.schedule actual.1 suffix .sharedCell = .ok result ∧
      OS.TSO64.Returned result.1 := by
  obtain ⟨cuts, result, completion, _wholeRun, _batch⟩ :=
    cohort_complete_after_prefix invocations success choices
  exact ⟨_, result, completion.scheduled, completion.returned⟩
```

The constructed suffix is `cohortActions`: increasing worker slots, each with
exactly its actual cutpoint's remaining own issues. `choices tid offset` fixes
AF at each worker's suffix-local own-issue offset, with no restriction on those
choices. `cohortActions_length` gives the sum of remaining counts;
`CohortCompletion.issueCount` gives each slot's exact count. Already-returned
workers contribute zero issues. All slots remain present, and every final
worker has a returned body contract. `prior_reply` and `prefix_reply` retain
already observed typed replies, even if later peers change RAM. The complete
prefix observations are retained, and the concatenated run yields `BatchResult`.

Returning the cohort does not drain its stores. `CohortCompletion.close` appends
the production drain schedule and retains its actual `DrainClosure.Certificate`;
`cohort_closed_after_prefix` composes that closure with the original prefix and
issue suffix. The separate well-formed-state premise handles the empty cohort
as well. The additional drain phase establishes `Finished`: every worker
returned and all queues empty. It preserves every CPU response, while RAM can
change through actual publications after RET. These theorems construct a chosen
finite schedule; they imply no fairness or completion of every schedule.

The independent `ChosenIssues choices suffix` additionally binds every action's
AF to `choices tid (issues tid (suffix.take index))` at its original suffix index.
Peer blocks and the already executed invocation prefix do not increment that
thread-local suffix count. `OS.PlainCallCompletion64.complete` transports this
property, exact remaining counts, saved replies and the same-run `Post` from
the shared cohort engine. `completion` is the independent contract projection;
`closure` separately returns the actual drain certificate, `Finished`, complete
concatenated execution, `Post` and equality of every CPU response before/after
draining. A returned store can still publish during that separate phase.

## Frame complete RAM cells

`Footprint.cells_frame` covers every successful finite interleaving of an
initial invocation cohort, with no completion or final-quiescence requirement.
Its fixed affected region is the union of every admitted target qword and the
exact address/width regions of every **actual initial FIFO entry**. Those
boundary entries may be ordinary or managed. The frame does not count an
already-drained prefix described by `Method.initialQueue` as still incoming.

```lean
import EDSL.X86.VCGen.PlainMethods.Footprint
open EDSL X86.VCGen.PlainMethods

example {initial : OS.TSO64.State}
    (invocations : (tid : Fin initial.workers.length) → Invocation initial tid.val)
    {actions : List OS.TSO64.Action}
    {result : OS.TSO64.State × List OS.TSO64.Observation}
    (success : OS.TSO64.schedule initial actions .sharedCell = .ok result)
    (query : X86.Word) (outside : ¬ Footprint.affected invocations query) :
    result.1.world.legacy.shared.resources.space.cells query =
      initial.world.legacy.shared.resources.space.cells query :=
  Footprint.cells_frame invocations success query outside
```

The equality preserves complete `Space.cells`, including mappedness,
permissions and inaccessible byte contents. Actual store-history provenance
classifies each drain as an incoming entry or an exact store issued by an
admitted worker; the client supplies no future write set or drain-classification
oracle. `cells_frame_empty` removes the incoming-entry footprint when the actual
initial queues are empty, while allowing nonzero counters. Separately,
`TSO64.schedule_stable` preserves resource metadata and per-address permissions
under either authority profile; `schedule_current_resources` retains each
original slot's resource identity and current authority. Metadata stability
alone does not preserve stored bytes at affected addresses.

`OS.PlainCallFrames64.prefix_frame` composes these rules directly from the
independent `Pre`, separate static shapes and an actual successful schedule.
Its independent `Plain64.PrefixFrame` states current target authority, original
resources, fixed worker population and complete-cell preservation using the
input cells and actual initial queues. Clients need no method cutpoint:

```lean
import EDSL.OS.PlainCallFrames64

example {catalog : Grading.ConcurrentTask.Plain64.Catalog}
    (static : OS.PlainCallAdmission64.StaticShapes catalog)
    {initial : OS.TSO64.State}
    {inputs : Fin initial.workers.length → Grading.ConcurrentTask.Plain64.Input}
    (pre : Grading.ConcurrentTask.Plain64.Pre catalog initial inputs)
    {actions : List OS.TSO64.Action}
    {result : OS.TSO64.State × List OS.TSO64.Observation}
    (success : OS.TSO64.schedule initial actions .sharedCell = .ok result) :
    Grading.ConcurrentTask.Plain64.PrefixFrame initial result.1 inputs :=
  OS.PlainCallFrames64.prefix_frame static pre success
```

`returned_slot` additionally derives the scalar ABI frame for an actual returned
worker relative to its actual initial slot. `returned_cohort` combines those
frames when every worker has returned, with pending publications still permitted.

## Derive safety and progress

`import EDSL.OS.PlainCall64` exposes the full claim and its admission, frame,
safety, progress, behavior, completion and history adapters. Once a new byte
window has its static shape proof and its workers satisfy independent `Pre`,
the same rules apply to every
successful prefix:

```lean
import EDSL.OS.PlainCall64
open EDSL Grading.ConcurrentTask.Plain64

example {catalog : Catalog}
    (static : OS.PlainCallAdmission64.StaticShapes catalog)
    {initial : OS.TSO64.State}
    {inputs : Fin initial.workers.length → Input}
    (pre : Pre catalog initial inputs)
    {actions : List OS.TSO64.Action}
    {result : OS.TSO64.State × List OS.TSO64.Observation}
    (success : OS.TSO64.schedule initial actions .sharedCell = .ok result) :
    SafePrefix initial result.1 inputs ∧ Enabled result.1 ∧ Bounded 64 actions result.1 :=
  ⟨OS.PlainCallSafety64.safe_prefix static pre success,
    OS.PlainCallProgress64.enabled static pre success,
    OS.PlainCallProgress64.bounded static pre success⟩
```

`SafePrefix` adds actual FIFO suffix and allocation-counter progress to the
complete-cell frame. It preserves the same original and current target
reference, complete flags, callee-saved registers, full code image and original
protected caller reads. Incoming queues remain actual boundary data.

Enabledness means a currently running worker can retire its next instruction
for either AF choice. The 64-issue upper bound follows from positive instruction
lengths and the supported complete 64-byte window; drains consume no own issue.
It is neither a hardware timing result nor a minimum-operation theorem, and
neither result assumes scheduler fairness or publication at RET.

`OS.PlainCallBehavior64.post` additionally derives independent `Plain64.Post`
for any actual successful run in which all workers returned. Each outcome
records its unique same-run data access and RET, the selected full64 read and
FIFO/published source or exact store enqueue/reference/counter, and its scalar
ABI, register and queue frames. The postcondition covers every recognized MOV64
access and every RET, excluding RMW and blocked observations. Valid nonempty
incoming FIFOs remain allowed; a returned store need not have published.

For closed runs, `OS.PlainCallHistory64.behavior_history_of_closed` joins that
independent Post to the constructed legal atomic History with exactly the same
call list. Clients do not write dependent casts between observed values and
logical replies. The full Claim composes these adapters. Useful exact-file
resource populations and their required homogeneous/mixed executions remain
open gates before the pending compiler functions receive corpus credit.

## Extract calls and match scanner events

`completed_call` derives a `CompletedCall` from the same present admission,
actual successful schedule and returned final worker. The witness retains that
complete execution, the actual access and unique actual RET, and the strict
ordering between their original action positions. `ResponseAt` includes the
real prefix, selected action and observation, saved RAX and production
`ReturnOrigin`; a final-state value alone cannot establish it.

`CompletedCall.call occurrence` produces the independent typed atomic call.
Invocation position zero denotes the admitted machine entry. It does not assert
a source or native invocation event. Its logical occurrence label is distinct
from the buffered-store allocation counter.

`AtomicEvents` connects those access origins to the existing production atomic
scanner in both directions. It retains the exact reference, full value, writer
source and store occurrence, advancing the writer map over every action,
including drains. Its declared interface uses acquire loads and release stores;
decoding MOV does not establish a source program's memory order. Supplied writer
maps and initial queue entries remain explicit provenance boundaries.

`Invocation` supplies present admission for one initial worker slot.
`completed_batch` extracts all such calls from an actual run in which every slot
has returned. `BatchResult.calls` orders them by actual access position and
proves complete coverage of independently recognized MOV64 accesses and observed
RETs, unique keys and valid intervals. This adapter covers one invocation per
initial worker in the scheduler's fixed resource universe. It does not yet
model repeated invocations or worker creation.

```lean
example {initial : OS.TSO64.State}
    (invocations : (tid : Fin initial.workers.length) → Invocation initial tid.val)
    {actions : List OS.TSO64.Action}
    {result : OS.TSO64.State × List OS.TSO64.Observation}
    (executed : OS.TSO64.schedule initial actions .sharedCell = .ok result)
    (returned : ∀ tid : Fin initial.workers.length, ∃ worker,
      result.1.workers[tid.val]? = some worker ∧ worker.phase = .returned) :
    Nonempty (BatchResult initial actions result invocations) :=
  completed_batch invocations executed returned
```

`Correspondence.machine_events` derives the complete scanner event list from
the admitted cohort, retaining every reference, reply, writer key and original
position. `positioned_events` and `source_events` then match the entire ordered
list to the independent calls under the declared acquire/release interface.
These equations are derived from actual execution and both coverage directions.
Clients do not supply the desired call-event equality.

`Correspondence.realizes` supplies structural `AtomicCalls.Realizes` when a
candidate is bound to that actual scanner list and its initializer shape is
established. Neither structural correspondence nor sorting proves reads-from
legality, coherence or `C23Atomic.Legal`. The history composition below derives
those facts through the operational graph layer. Repeated invocations and
dynamic worker lifecycle remain outside this adapter.

## Construct the complete atomic history

`OS.PlainCallHistory64.history_of_closed` is the direct route from independent
`ClosedPre`, separate static shapes and an actual successful `Finished` run.
It derives the scan result and enumerates every live initial registered cell
from current resource validity. The caller supplies no initializer table,
selected source, `Captured` witness or desired graph. Arbitrary initial machine
counters remain allowed; the closed boundary requires empty queues.

`OS.PlainCallClosed64.post` packages the full independent `ClosedPost`. It
retains the same independent `Post`, the actual scanner execution, complete
live-cell manifest with its original RAM words, per-slot source identities,
and equality of the entire machine-event list with the outcomes in call order.
Full references, values, machine allocation counters and original positions
remain visible, including an arbitrary external scanner offset. The output also
contains actual builder success, structural correspondence and the same calls'
atomic `History`, complete-cell preservation outside target qwords and collection
for each actual final worker. Empty final queues justify collection; neither
RET nor the general `Post` requires a store to have published.
`ClosedPost.initialized` and `positioned_events` expose complete initialization
and event correspondence to clients without another graph or source-key proof.

The generic `AtomicTrace.Graph.captured_of_schedule` supplies the same raw
capture route for either authority profile, independently of this method family.
Scanner faults remain exactly the production scheduler faults. It does not
prove that an arbitrary schedule succeeds or finishes.

`Correspondence.history` joins the admitted initial cohort to
[`Graph.Captured`](checked-atomic-traces.md#graph-construction-from-actual-execution).
It constructs both the actual graph and the complete call batch. Initial values,
writer identities, read values, publication ranks, event equality and legality
come from that same run. None is a caller-supplied history oracle.

```lean
open OS.TSO64.C23Projection

example {initial : OS.TSO64.State} {actions : List OS.TSO64.Action}
    {offset : Nat} {run : AtomicTrace.Result} {initials : List AtomicTrace.Initials.Entry}
    (captured : AtomicTrace.Graph.Captured initial actions .sharedCell offset run initials)
    (invocations : (tid : Fin initial.workers.length) → Invocation initial tid.val)
    (returned : ∀ tid : Fin initial.workers.length, ∃ worker,
      run.state.workers[tid.val]? = some worker ∧ worker.phase = .returned) :
    ∃ table,
      AtomicTrace.Graph.build (AtomicTrace.Graph.runInputs initials run offset)
        AtomicEvents.orders = some table ∧
      ∃ batch : BatchResult initial actions run.execution invocations,
        Concurrency.AtomicCalls.History (initials.map AtomicTrace.Graph.initialEvent)
          batch.calls table.toCandidate :=
  Correspondence.history captured invocations returned
```

`history_of_batch` provides the same composition when `completed_batch` has
already produced the actual batch. These theorems retain arbitrary scan offsets,
logical occurrence labels, full words and nonzero initial store counters.
They cover one invocation per initial worker with empty initial and final
queues. A store can return before publication; the final queue boundary closes
its publication history without moving that publication into the call interval.
The executable verifier retains its full legality checker.

## Represented scalar ABI frames

`OS.ScalarCall64.Entry` independently states scalar stack alignment, clear DF,
a nonwrapping stack pop and canonical post-pop RSP. These requirements are
additional to the base method's protected caller and code admission.
`BodyPost.return_frame` transports the shared engine's entry/body evidence to
`OS.ScalarCall64.ReturnFrame`: actual returned worker, retained current resources,
callee-saved GPRs, all flags, stack pop and canonical original caller continuation.
Both initial and final worker slots are recorded in that independent frame.
Applications must establish the scalar entry requirements from their admitted
resources; the adapter does not assume them for every `Method`.

The return frame permits a pending store. Its separate `collect` theorem requires
an empty own queue because the production collection API observes both return
and publication. Neither the return frame nor collection releases resources.

`Corpus.V1.PlainWindows` binds both operations to the exact complete named
GCC/Clang ELF windows and checks their shared decoder shapes. GCC's ENDBR64
remains present. These file and shape checks establish no behavioral contract
or useful loaded-resource population by themselves.

## Scope and validation

The [regressions](../tests/PlainMethods.lean) use the four frozen GCC/Clang windows
and synthetic real executions with nonempty queues. They distinguish saved load
responses from later RAM, full64 stores from truncation, FIFO order and counters
from queue length, and pre-RET RSP capture from the popped stack pointer.

The [admission examples](../tests/PlainMethodAdmission.lean) construct current
resources through checked allocation, initialization, protection, borrowing and
worker attachment. Both MOV directions use `enabled`, exact-AF `complete` and
`all_completed` from that entry, without assuming a future successful run or
returned cutpoint. These examples start with empty FIFOs and no peer; the
separate execution regressions exercise mixed queues and interference.

The [call-origin clients](../tests/PlainCallOrigins.lean) connect both admitted
MOV directions to the actual scanner and check literal full64 events and RET
values. The [admitted interference client](../tests/PlainCallInterference.lean)
creates its ordinary own FIFO and managed peer FIFO through actual instructions,
then instantiates the shared method and call proofs. It checks the retained old
reply after a peer publishes a different value, with the intervening drain kept
between access and response positions.
The [cohort client](../tests/PlainCallBatch.lean) admits both workers before their
managed accesses and requires chronological call order `[1, 0]`, with access
positions `[0, 1]` and RET positions `[3, 4]`. These expectations follow the real
dispatches and observations, independently of the adapter's sorting algorithm.
The [complete scanner client](../tests/PlainEventCorrespondence.lean) derives
scanner success from that same actual run and checks its full ordered event
list, including distinct handles, writer identity and a nonzero position offset.
The [history client](../tests/PlainMethodHistories.lean) starts after a real
pre-invocation drain, retaining a nonzero store counter. Its peer returns before
publication; the reader loads the old full word during that interval and retains
it after RAM changes. Independent expectations check the actual call positions,
read source and later publication rank against the constructed history. Its
model caller slots do not supply the separate scalar ABI admission above.

The shared rules inherit the existing long-mode, CET-off, supported-padding,
aligned normal-RAM, translation/alias and managed-resource assumptions. They do
not establish physical x86/Linux correspondence, dynamic resource lifecycle,
source/compiler preservation, full C23 semantics or a full OS/kernel result.
Finite atomic-fragment legality is established for the raw history boundary
above. The full independent Claim and its completion/closed-output adapters have
passed scoped strict checks. Whole-ELF resource construction remains under
validation, and useful homogeneous/mixed execution gates for all four frozen
load/store artifacts remain open. Coverage remains **16/40 functions and
32/80 artifacts**, including **one distinct concurrent function**. See
[atomic call contracts](atomic-call-contracts.md) and
[checked finite atomic traces](checked-atomic-traces.md) for the adjacent layers.
