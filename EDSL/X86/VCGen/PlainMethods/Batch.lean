/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.PlainMethods.Calls
import Init.Data.List.Nat.Pairwise
import Init.Data.List.Sort.Lemmas

/-!
Completed-call extraction for the entire finite initial worker cohort. Every
actual worker slot admits one plain method at its present entry, and the actual
successful schedule returns every such worker. Intermediate cutpoints, replies,
access origins and unique RET origins are obtained from `completed_call`.

The output traverses the slots in strictly increasing actual access position.
Positions are original action indices, including peer actions and FIFO drains.
The logical occurrence is an invocation label, separate from `nextStore`.

The scheduler has a fixed worker/resource universe: this adapter covers one
invocation per initial worker slot, with distinct logical threads for distinct
slots. Repeated invocations, worker creation and resource lifecycle are outside
this contract. Initial queues need not be empty; a returned buffered store need
not be published. Physical correspondence retains the method model's explicit
long-mode, CET-off, scalar-RAM, translation/alias and resource assumptions.

`BatchResult.realizes` supplies structural call/event correspondence only when
the candidate's complete event list and initializer shape are established
separately. It neither manufactures a candidate nor proves C23 legality,
read-from identities, scanner equality or `AtomicCalls.History`.
-/

set_option autoImplicit false

namespace EDSL.X86.VCGen.PlainMethods
open OS OS.TSO64 AtomicMethods Concurrency

/-- One admitted invocation at an actual worker slot. All admission facts are
about the initial state. The logical occurrence is not a machine store number. -/
structure Invocation (state : OS.TSO64.State) (tid : Nat) where
  method : Method
  padding : List Padding
  occurrence : Nat
  initial : Worker
  current : Current method state
  live : state.workers[tid]? = some initial
  entry : At method (.preamble 0 padding) initial

private theorem batch_step_workers_length {state : OS.TSO64.State} {action : Action}
    {result : OS.TSO64.State × Observation} {profile : Profile}
    (success : OS.TSO64.step state action profile = .ok result) :
    result.1.workers.length = state.workers.length := by
  cases step_origin success with
  | ordinary live running code caller fetched effect =>
    cases effect with
    | intro supported bounds decoded reads queue executed finish =>
      cases finish <;> simp only [install, List.length_set]
  | blocked => rfl
  | rmw => simp only [install, List.length_set]
  | drained => simp only [install, List.length_set]

private theorem batch_schedule_workers_length {state : OS.TSO64.State}
    {actions : List Action} {result : OS.TSO64.State × List Observation} {profile : Profile}
    (success : schedule state actions profile = .ok result) :
    result.1.workers.length = state.workers.length := by
  induction actions generalizing state result with
  | nil =>
    have same : (state, []) = result := Except.ok.inj success
    subst result
    rfl
  | cons action rest ih =>
    obtain ⟨first, tail, actual, following, same⟩ := schedule_cons_ok success
    rw [same]
    exact (ih following).trans (batch_step_workers_length actual)

private theorem batch_returned_live {state after : OS.TSO64.State} {action : Action}
    {tid : Nat} {profile : Profile}
    (success : OS.TSO64.step state action profile = .ok (after, .returned tid)) :
    ∃ worker, state.workers[tid]? = some worker := by
  cases step_origin success with
  | ordinary live running code caller fetched effect =>
    cases effect with
    | intro supported bounds decoded reads queue executed finish =>
      cases finish with
      | returned outcome => exact ⟨_, live⟩

private theorem batch_dispatched_bound {state : OS.TSO64.State} {actions : List Action}
    {result : OS.TSO64.State × List Observation} {tid index : Nat}
    (dispatched : DispatchedAt tid state actions result index) : tid < state.workers.length := by
  obtain ⟨before, action, first, prefixRun, selected, actual, own⟩ := dispatched
  obtain ⟨af, worker, instruction, issuing, live, fetched, access⟩ := own
  have bound := (List.getElem_of_getElem? live).1
  have length : before.workers.length = state.workers.length := batch_schedule_workers_length prefixRun
  omega

private theorem batch_returned_bound {state : OS.TSO64.State} {actions : List Action}
    {result : OS.TSO64.State × List Observation} {tid index : Nat}
    (success : schedule state actions .sharedCell = .ok result)
    (observed : result.2[index]? = some (.returned tid)) : tid < state.workers.length := by
  obtain ⟨before, action, next, prefixRun, selected, actual⟩ :=
    ScheduleTrace.observation_at success observed
  obtain ⟨worker, live⟩ := batch_returned_live actual
  have bound := (List.getElem_of_getElem? live).1
  have length : before.workers.length = state.workers.length := batch_schedule_workers_length prefixRun
  omega

private theorem batch_access_issue {method : Method} {tid index : Nat}
    {state : OS.TSO64.State} {actions : List Action}
    {result : OS.TSO64.State × List Observation} {reply : method.operation.Reply}
    (access : AccessAt method tid state actions result index reply) :
    ∃ af, actions[index]? = some (.issue tid af) := by
  obtain ⟨before, action, first, prefixRun, selected, actual, own⟩ := access.dispatched
  obtain ⟨af, worker, instruction, issuing, live, fetched, recognized⟩ := own
  exact ⟨af, by simpa only [issuing] using selected⟩

/-- OneAccess covers an independently recognized own dispatch, including one
whose reply and method annotation were not supplied by the observer. -/
theorem CompletedCall.performed_unique {method : Method} {tid : Nat}
    {state : OS.TSO64.State} {actions : List Action}
    {result : OS.TSO64.State × List Observation}
    (completed : CompletedCall method tid state actions result) {index : Nat}
    (dispatched : DispatchedAt tid state actions result index) : index = completed.performed := by
  obtain ⟨position, origin, unique⟩ := completed.oneAccess
  exact (unique index dispatched).trans
    (unique completed.performed completed.access.dispatched).symm

/-- Equal actual access positions force equal issuing threads. This uses the
selected `.issue tid af` action, independently of request/reply equality. -/
theorem CompletedCall.thread_eq_of_performed_eq {firstMethod secondMethod : Method}
    {firstTid secondTid : Nat} {state : OS.TSO64.State} {actions : List Action}
    {result : OS.TSO64.State × List Observation}
    (first : CompletedCall firstMethod firstTid state actions result)
    (second : CompletedCall secondMethod secondTid state actions result)
    (same : first.performed = second.performed) : firstTid = secondTid := by
  obtain ⟨firstAF, firstAt⟩ := batch_access_issue first.access
  obtain ⟨secondAF, secondAt⟩ := batch_access_issue second.access
  rw [same] at firstAt
  exact (Action.issue.inj (Option.some.inj (firstAt.symm.trans secondAt))).1

/-- A same-run completed witness for every actual initial slot, together with
an access-ordered permutation of those slots. `calls` exposes the corresponding
independent call list; all its structural and coverage properties are derived
below, rather than being separate admission premises. -/
structure BatchResult (initial : OS.TSO64.State) (actions : List Action)
    (result : OS.TSO64.State × List Observation)
    (invocations : (tid : Fin initial.workers.length) → Invocation initial tid.val) where
  success : schedule initial actions .sharedCell = .ok result
  completed : (tid : Fin initial.workers.length) →
    CompletedCall (invocations tid).method tid.val initial actions result
  slots : List (Fin initial.workers.length)
  slots_perm : slots.Perm (List.finRange initial.workers.length)
  slots_ordered : slots.Pairwise (fun first second =>
    (completed first).performed < (completed second).performed)

namespace BatchResult
variable {initial : OS.TSO64.State} {actions : List Action}
  {result : OS.TSO64.State × List Observation}
  {invocations : (tid : Fin initial.workers.length) → Invocation initial tid.val}

/-- The exact declared request, actual typed reply and unique actual RET for
one slot; the invocation boundary is the admitted initial entry. -/
def call (batch : BatchResult initial actions result invocations)
    (tid : Fin initial.workers.length) : AtomicCalls.Call Atomics64.CellId64 Word :=
  (batch.completed tid).call (invocations tid).occurrence

/-- Actual performed order, retaining original action positions. -/
def calls (batch : BatchResult initial actions result invocations) :
    List (AtomicCalls.Call Atomics64.CellId64 Word) := batch.slots.map batch.call

theorem length (batch : BatchResult initial actions result invocations) :
    batch.calls.length = initial.workers.length := by
  simpa only [calls, List.length_map, List.length_finRange] using batch.slots_perm.length_eq

theorem slot_mem (batch : BatchResult initial actions result invocations)
    (tid : Fin initial.workers.length) : tid ∈ batch.slots :=
  batch.slots_perm.mem_iff.mpr (List.mem_finRange tid)

theorem call_mem (batch : BatchResult initial actions result invocations)
    (tid : Fin initial.workers.length) : batch.call tid ∈ batch.calls :=
  List.mem_map.mpr ⟨tid, batch.slot_mem tid, rfl⟩

/-- Each output call retains its original admitted method and CompletedCall
witness through the named slot. In particular its reply and RET are not
reconstructed from values in another worker or from the final machine state. -/
theorem origin (batch : BatchResult initial actions result invocations)
    {actual : AtomicCalls.Call Atomics64.CellId64 Word} (member : actual ∈ batch.calls) :
    ∃ tid : Fin initial.workers.length,
      actual = (batch.completed tid).call (invocations tid).occurrence := by
  obtain ⟨tid, _, same⟩ := List.mem_map.mp member
  exact ⟨tid, same.symm⟩

theorem slots_nodup (batch : BatchResult initial actions result invocations) :
    batch.slots.Nodup := batch.slots_perm.symm.nodup (List.nodup_finRange _)

/-- One call per actual worker slot, even when logical occurrence labels or
request/reply values agree across different slots. -/
theorem threads (batch : BatchResult initial actions result invocations) :
    (batch.calls.map (fun actual => actual.thread)).Nodup := by
  unfold calls
  rw [List.map_map]
  apply List.pairwise_map.mpr
  apply batch.slots_nodup.imp
  intro first second different same
  exact different (Fin.ext same)

theorem keys (batch : BatchResult initial actions result invocations) :
    (batch.calls.map AtomicCalls.Call.key).Nodup := by
  unfold calls
  rw [List.map_map]
  apply List.pairwise_map.mpr
  apply batch.slots_nodup.imp
  intro first second different same
  exact different (Fin.ext (congrArg Prod.fst same))

theorem ordered (batch : BatchResult initial actions result invocations) :
    batch.calls.Pairwise (fun first second => first.performed < second.performed) :=
  List.pairwise_map.mpr batch.slots_ordered

theorem intervals (batch : BatchResult initial actions result invocations)
    (actual : AtomicCalls.Call Atomics64.CellId64 Word) (member : actual ∈ batch.calls) :
    actual.invoked ≤ actual.performed ∧ actual.performed < actual.returned := by
  obtain ⟨tid, rfl⟩ := batch.origin member
  exact (batch.completed tid).intervals (invocations tid).occurrence

theorem thread_unique (batch : BatchResult initial actions result invocations)
    {first second : AtomicCalls.Call Atomics64.CellId64 Word}
    (firstMem : first ∈ batch.calls) (secondMem : second ∈ batch.calls)
    (same : first.thread = second.thread) : first = second := by
  obtain ⟨firstTid, rfl⟩ := batch.origin firstMem
  obtain ⟨secondTid, rfl⟩ := batch.origin secondMem
  have equal : firstTid = secondTid := Fin.ext same
  subst secondTid
  rfl

theorem coverage (batch : BatchResult initial actions result invocations)
    (tid : Fin initial.workers.length) :
    ∃ actual ∈ batch.calls, actual.thread = tid.val ∧
      ∀ other ∈ batch.calls, other.thread = tid.val → other = actual := by
  refine ⟨batch.call tid, batch.call_mem tid, rfl, ?_⟩
  intro other member same
  exact batch.thread_unique member (batch.call_mem tid) same

/-- This nonoverlap theorem uses the current one-invocation-per-slot contract;
it is not a repeated-invocation or worker-reuse result. -/
theorem threadOrder (batch : BatchResult initial actions result invocations)
    (first : AtomicCalls.Call Atomics64.CellId64 Word) (firstMem : first ∈ batch.calls)
    (second : AtomicCalls.Call Atomics64.CellId64 Word) (secondMem : second ∈ batch.calls)
    (same : first.thread = second.thread) (earlier : first.performed < second.performed) :
    first.returned ≤ second.invoked := by
  have equal := batch.thread_unique firstMem secondMem same
  rw [equal] at earlier
  exact False.elim (Nat.lt_irrefl _ earlier)

/-- Every independently recognized actual own MOV64 dispatch belongs to the
initial cohort and names precisely its extracted call's access position. -/
theorem dispatched (batch : BatchResult initial actions result invocations)
    {tid index : Nat} (actual : DispatchedAt tid initial actions result index) :
    ∃ extracted ∈ batch.calls, extracted.thread = tid ∧ extracted.performed = index := by
  let slot : Fin initial.workers.length := ⟨tid, batch_dispatched_bound actual⟩
  refine ⟨batch.call slot, batch.call_mem slot, rfl, ?_⟩
  exact ((batch.completed slot).performed_unique actual).symm

/-- Every observed RET names precisely one extracted response position. The
CompletedCall witness retained by `origin` also contains its ReturnOrigin. -/
theorem responded (batch : BatchResult initial actions result invocations)
    {tid index : Nat} (observed : result.2[index]? = some (.returned tid)) :
    ∃ extracted ∈ batch.calls, extracted.thread = tid ∧ extracted.returned = index := by
  let slot : Fin initial.workers.length := ⟨tid, batch_returned_bound batch.success observed⟩
  refine ⟨batch.call slot, batch.call_mem slot, rfl, ?_⟩
  exact ((batch.completed slot).responseUnique index observed).symm

/-- Structural realization requires an independently established complete
candidate event list and initializer shape. No RF or legality fact is inferred
from constructing calls, and no proposed future history is an admission input. -/
theorem realizes (batch : BatchResult initial actions result invocations)
    {initials : List (C23Atomic.Event Atomics64.CellId64 Word)}
    {candidate : C23Atomic.Candidate Atomics64.CellId64 Word}
    (events : candidate.events = initials ++ batch.calls.map AtomicCalls.Call.event)
    (initialized : ∀ event ∈ initials, event.thread = none ∧
      ∃ value, event.access = .initialize value) :
    AtomicCalls.Realizes initials batch.calls candidate :=
  ⟨events, initialized, batch.keys, batch.ordered, batch.intervals, batch.threadOrder⟩

end BatchResult

/-- Extract every completed call from present per-slot admission and an actual
successful complete run. Each final-worker premise is just liveness/returned
phase: replies, future At assertions and histories are conclusions. Sorting
compares actual performed positions; uniqueness comes from actual issue tids. -/
theorem completed_batch {initial : OS.TSO64.State}
    (invocations : (tid : Fin initial.workers.length) → Invocation initial tid.val)
    {actions : List Action} {result : OS.TSO64.State × List Observation}
    (success : schedule initial actions .sharedCell = .ok result)
    (returned : ∀ tid : Fin initial.workers.length,
      ∃ final, result.1.workers[tid.val]? = some final ∧ final.phase = .returned) :
    Nonempty (BatchResult initial actions result invocations) := by
  classical
  have finished : ∀ tid : Fin initial.workers.length,
      Nonempty (CompletedCall (invocations tid).method tid.val initial actions result) := by
    intro tid
    obtain ⟨final, finalLive, returnedPhase⟩ := returned tid
    exact completed_call (invocations tid).current (invocations tid).live
      (invocations tid).entry success finalLive returnedPhase
  let completed : (tid : Fin initial.workers.length) →
      CompletedCall (invocations tid).method tid.val initial actions result :=
    fun tid => Classical.choice (finished tid)
  have injective : ∀ first second : Fin initial.workers.length,
      (completed first).performed = (completed second).performed → first = second := by
    intro first second same
    exact Fin.ext ((completed first).thread_eq_of_performed_eq (completed second) same)
  let le : Fin initial.workers.length → Fin initial.workers.length → Bool :=
    fun first second => decide ((completed first).performed ≤ (completed second).performed)
  let slots := (List.finRange initial.workers.length).mergeSort le
  have perm : slots.Perm (List.finRange initial.workers.length) := List.mergeSort_perm _ _
  have nodup : slots.Nodup := perm.symm.nodup (List.nodup_finRange _)
  have sorted : slots.Pairwise (fun first second => le first second = true) := by
    apply List.pairwise_mergeSort
    · intro first middle last firstLe lastLe
      change decide ((completed first).performed ≤ (completed last).performed) = true
      change decide ((completed first).performed ≤ (completed middle).performed) = true at firstLe
      change decide ((completed middle).performed ≤ (completed last).performed) = true at lastLe
      exact decide_eq_true (Nat.le_trans (of_decide_eq_true firstLe) (of_decide_eq_true lastLe))
    · intro first second
      change (decide ((completed first).performed ≤ (completed second).performed) ||
        decide ((completed second).performed ≤ (completed first).performed)) = true
      apply Bool.or_eq_true_iff.mpr
      rcases Nat.le_total (completed first).performed (completed second).performed with forward | backward
      · exact Or.inl (decide_eq_true forward)
      · exact Or.inr (decide_eq_true backward)
  have weak : slots.Pairwise (fun first second =>
      (completed first).performed ≤ (completed second).performed) :=
    sorted.imp (fun related => of_decide_eq_true related)
  have strict : slots.Pairwise (fun first second =>
      (completed first).performed < (completed second).performed) := by
    apply (weak.and nodup).imp
    intro first second related
    have different : (completed first).performed ≠ (completed second).performed :=
      fun same => related.2 (injective first second same)
    have earlier := related.1
    omega
  exact ⟨⟨success, completed, slots, perm, strict⟩⟩

end EDSL.X86.VCGen.PlainMethods

#audit_edsl
