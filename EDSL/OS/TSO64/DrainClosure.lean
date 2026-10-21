/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.StoreHistory
import EDSL.OS.TSO64.ScheduleTrace

/-!
Constructive finite publication through the production TSO64 scheduler. The
action list is computed from the actual initial FIFOs, in worker-index order;
`drainAll` is just `schedule` on that list, including its exact faults.

Current `WellFormed` authority suffices under either existing profile, with no
restriction on worker phase, context, queue length, or ordinary/managed mixing
allowed by that profile. In particular, `ownedOnly` still excludes managed
entries. No instruction is issued and no resource is released. This is a finite
chosen schedule, not a fairness or liveness assertion about other schedules.

An arbitrary valid initial FIFO supplies an explicit queue boundary, not an
instruction-issue history or `Sequenced` premise. Publication origins are exact
entries at their original threads. A supplied successful prefix connects those
entries to the existing StoreHistory boundary-or-issue result; an empty boundary
then gives actual issues in that prefix. No origin is inferred from equal values
or numerical store occurrences.
-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.DrainClosure
open X86

/-- The finite number of entries across the actual worker FIFOs. -/
def pendingCount : List Worker → Nat
  | [] => 0
  | worker :: rest => worker.pending.length + pendingCount rest

def totalPending (state : State) : Nat := pendingCount state.workers

/-- Drain each initial FIFO in order, without executing any user instruction. -/
def actionsFrom (base : Nat) : List Worker → List Action
  | [] => []
  | worker :: rest =>
      List.replicate worker.pending.length (.drain base) ++ actionsFrom (base + 1) rest

def actions (state : State) : List Action := actionsFrom 0 state.workers

/-- No new executor or fault translation: this is the production schedule. -/
def drainAll (state : State) (profile : Profile := .ownedOnly) :
    Except Fault (State × List Observation) := schedule state (actions state) profile

/-- Even outside the invariant, the original scheduler's fault is retained. -/
theorem drainAll_error_iff (state : State) (profile : Profile) (fault : Fault) :
    drainAll state profile = .error fault ↔
      schedule state (actions state) profile = .error fault := Iff.rfl

def DrainOnly (steps : List Action) : Prop :=
  ∀ action ∈ steps, ∃ tid, action = .drain tid

theorem actionsFrom_length (base : Nat) (workers : List Worker) :
    (actionsFrom base workers).length = pendingCount workers := by
  induction workers generalizing base with
  | nil => rfl
  | cons worker rest ih =>
    simp only [actionsFrom, List.length_append, List.length_replicate, pendingCount, ih]

theorem actions_length (state : State) : (actions state).length = totalPending state :=
  actionsFrom_length 0 state.workers

theorem actionsFrom_drainOnly (base : Nat) (workers : List Worker) :
    DrainOnly (actionsFrom base workers) := by
  induction workers generalizing base with
  | nil => intro action member; cases member
  | cons worker rest ih =>
    intro action member
    change action ∈ List.replicate worker.pending.length (.drain base) ++
      actionsFrom (base + 1) rest at member
    rcases List.mem_append.mp member with here | later
    · exact ⟨base, List.eq_of_mem_replicate here⟩
    · exact ih (base + 1) action later

theorem actions_drainOnly (state : State) : DrainOnly (actions state) :=
  actionsFrom_drainOnly 0 state.workers

private theorem pendingCount_zero_iff (workers : List Worker) :
    pendingCount workers = 0 ↔ ∀ worker ∈ workers, worker.pending = [] := by
  induction workers with
  | nil =>
    constructor
    · intro _zero worker member
      cases member
    · intro _empty
      rfl
  | cons worker rest ih =>
    constructor
    · intro zero
      change worker.pending.length + pendingCount rest = 0 at zero
      have headZero : worker.pending.length = 0 := by omega
      have tailZero : pendingCount rest = 0 := by omega
      intro other member
      rcases List.mem_cons.mp member with rfl | later
      · exact List.length_eq_zero_iff.mp headZero
      · exact ih.mp tailZero other later
    · intro empty
      have headEmpty := empty worker List.mem_cons_self
      have tailEmpty : ∀ other ∈ rest, other.pending = [] :=
        fun other member => empty other (List.mem_cons_of_mem worker member)
      have tailZero := ih.mpr tailEmpty
      simp only [pendingCount, headEmpty, List.length_nil, Nat.zero_add, tailZero]

theorem totalPending_zero_iff (state : State) :
    totalPending state = 0 ↔ Quiescent state := pendingCount_zero_iff state.workers

private theorem pendingCount_remove {workers : List Worker} {tid : Nat}
    {worker : Worker} {head : Pending} {tail : List Pending}
    (live : workers[tid]? = some worker) (fifo : worker.pending = head :: tail) :
    pendingCount (workers.set tid { worker with pending := tail }) + 1 =
      pendingCount workers := by
  induction workers generalizing tid with
  | nil => simp at live
  | cons other rest ih =>
    cases tid with
    | zero =>
      have same : other = worker := Option.some.inj live
      subst other
      change tail.length + pendingCount rest + 1 =
        worker.pending.length + pendingCount rest
      rw [fifo, List.length_cons]
      omega
    | succ tid =>
      have smaller := ih (tid := tid) live
      change (other.pending.length +
        pendingCount (rest.set tid { worker with pending := tail })) + 1 =
          other.pending.length + pendingCount rest
      omega

/-- Every successful production drain removes exactly one total pending entry,
without any WF, phase, provenance, or queue-numbering premise. -/
theorem drain_totalPending {state : State} {tid : Nat} {result : State × Observation}
    {profile : Profile} (success : drain state tid profile = .ok result) :
    totalPending result.1 + 1 = totalPending state := by
  obtain ⟨worker, head, tail, output, live, fifo, _gate, _effect, same⟩ :=
    drain_effect success
  rw [same]
  exact pendingCount_remove live fifo

theorem drain_decreases {state : State} {tid : Nat} {result : State × Observation}
    {profile : Profile} (success : drain state tid profile = .ok result) :
    totalPending result.1 < totalPending state := by
  have decrease := drain_totalPending success
  omega

/-- Erasing only the FIFO retains the entire context, phase, original resources
and nextStore counter. Final worker equality uses this literal record update. -/
def clearPending (worker : Worker) : Worker := { worker with pending := [] }

private theorem clearPending_eq (worker : Worker) (empty : worker.pending = []) :
    clearPending worker = worker := by
  cases worker with
  | mk context resources phase pending nextStore =>
    change pending = [] at empty
    subst pending
    rfl

private theorem quiescent_clear {state : State} (quiet : Quiescent state) :
    state.workers.map clearPending = state.workers := by
  calc
    state.workers.map clearPending = state.workers.map (fun worker => worker) :=
      List.map_congr_left fun worker member => clearPending_eq worker (quiet worker member)
    _ = state.workers := List.map_id' _

private theorem drain_workers {state : State} {tid : Nat} {result : State × Observation}
    {profile : Profile} (success : drain state tid profile = .ok result) :
    result.1.workers.map clearPending = state.workers.map clearPending := by
  obtain ⟨worker, _head, tail, output, live, _fifo, _gate, _effect, same⟩ :=
    drain_effect success
  rw [same]
  change (state.workers.set tid { worker with pending := tail }).map clearPending =
    state.workers.map clearPending
  rw [List.map_set]
  change (state.workers.map clearPending).set tid (clearPending worker) =
    state.workers.map clearPending
  have mapped : (state.workers.map clearPending)[tid]? = some (clearPending worker) := by
    rw [List.getElem?_map, live]
    rfl
  have indexed := List.getElem_of_getElem? mapped
  simpa only [indexed.2] using (List.set_getElem_self indexed.1)

private theorem stable_trans {before middle after : World}
    (first : Stable before middle) (second : Stable middle after) : Stable before after :=
  ⟨second.allocations.trans first.allocations, second.frontier.trans first.frontier,
    second.loans.trans first.loans, second.nextLoan.trans first.nextLoan,
    second.cells.trans first.cells, second.nextCell.trans first.nextCell,
    second.handles.trans first.handles, second.nextHandle.trans first.nextHandle,
    second.legacyHandles.trans first.legacyHandles,
    second.legacyNextHandle.trans first.legacyNextHandle,
    fun query => (second.permissions query).trans (first.permissions query)⟩

/-- The worker and world metadata frames for any successful drain-only run. -/
theorem schedule_frames {state : State} {steps : List Action}
    {result : State × List Observation} {profile : Profile}
    (only : DrainOnly steps) (success : schedule state steps profile = .ok result) :
    result.1.workers.map clearPending = state.workers.map clearPending ∧
      Stable state.world result.1.world := by
  induction steps generalizing state result with
  | nil =>
    have same : (state, []) = result := Except.ok.inj success
    subst result
    exact ⟨rfl, Stable.refl _⟩
  | cons action rest ih =>
    obtain ⟨tid, rfl⟩ := only action List.mem_cons_self
    have onlyRest : DrainOnly rest :=
      fun next member => only next (List.mem_cons_of_mem (.drain tid) member)
    obtain ⟨first, tail, stepped, following, same⟩ := schedule_cons_ok success
    obtain ⟨workers, stable⟩ := ih onlyRest following
    rw [same]
    exact ⟨workers.trans (drain_workers stepped), stable_trans (step_stable stepped) stable⟩

/-- An arbitrary successful drain-only schedule consumes exactly its length. -/
theorem schedule_count {state : State} {steps : List Action}
    {result : State × List Observation} {profile : Profile}
    (only : DrainOnly steps) (success : schedule state steps profile = .ok result) :
    totalPending result.1 + steps.length = totalPending state := by
  induction steps generalizing state result with
  | nil =>
    have same : (state, []) = result := Except.ok.inj success
    subst result
    rfl
  | cons action rest ih =>
    obtain ⟨tid, rfl⟩ := only action List.mem_cons_self
    have onlyRest : DrainOnly rest :=
      fun next member => only next (List.mem_cons_of_mem (.drain tid) member)
    obtain ⟨first, tail, stepped, following, same⟩ := schedule_cons_ok success
    have remaining := ih onlyRest following
    have decrease := drain_totalPending stepped
    rw [same]
    simp only [List.length_cons]
    omega

/-- Every observed publication is an exact initial FIFO entry at the same
thread. There can be no new store issue in a drain-only suffix. Duplicated
initial tags are allowed; this theorem does not claim occurrence uniqueness. -/
theorem schedule_publications {state : State} {steps : List Action}
    {result : State × List Observation} {profile : Profile}
    (only : DrainOnly steps) (success : schedule state steps profile = .ok result) :
    ∀ observation ∈ result.2, ∃ tid entry,
      observation = .drained tid entry ∧ StoreHistory.Queued state tid entry := by
  induction steps generalizing state result with
  | nil =>
    have same : (state, []) = result := Except.ok.inj success
    subst result
    intro observation member
    cases member
  | cons action rest ih =>
    obtain ⟨tid, rfl⟩ := only action List.mem_cons_self
    have onlyRest : DrainOnly rest :=
      fun next member => only next (List.mem_cons_of_mem (.drain tid) member)
    obtain ⟨first, tail, stepped, following, same⟩ := schedule_cons_ok success
    intro observation member
    have observed : observation ∈ first.2 :: tail.2 := by simpa only [same] using member
    rcases List.mem_cons.mp observed with here | later
    · obtain ⟨worker, entry, _pending, _output, live, fifo, _gate, _effect, firstEq⟩ :=
        drain_effect stepped
      refine ⟨tid, entry, here.trans (congrArg Prod.snd firstEq), worker, live, ?_⟩
      rw [fifo]
      exact List.mem_cons_self
    · obtain ⟨publisher, entry, published, queued⟩ := ih onlyRest following observation later
      refine ⟨publisher, entry, published, ?_⟩
      rcases StoreHistory.step_pending_origin stepped queued with boundary | issued
      · exact boundary
      · cases issued with
        | ordinary issuing _ _ _ _ _ _ _ => cases issuing

/- The head of the plan always selects a real nonempty FIFO. Publishing that
head leaves exactly the rest of the plan, independently of the changed RAM. -/
private theorem actionsFrom_head (workers : List Worker) (base : Nat)
    (nonempty : actionsFrom base workers ≠ []) :
    ∃ tid worker head tail rest,
      workers[tid]? = some worker ∧ worker.pending = head :: tail ∧
      actionsFrom base workers = .drain (base + tid) :: rest ∧
      actionsFrom base (workers.set tid { worker with pending := tail }) = rest := by
  induction workers generalizing base with
  | nil => exact False.elim (nonempty rfl)
  | cons worker workers ih =>
    cases fifo : worker.pending with
    | nil =>
      have restNonempty : actionsFrom (base + 1) workers ≠ [] := by
        simpa only [actionsFrom, fifo, List.length_nil, List.replicate_zero,
          List.nil_append] using nonempty
      obtain ⟨tid, current, head, tail, rest, live, pending, plan, remaining⟩ :=
        ih (base + 1) restNonempty
      refine ⟨tid + 1, current, head, tail, rest, live, pending, ?_, ?_⟩
      · simp only [actionsFrom, fifo, List.length_nil, List.replicate_zero, List.nil_append]
        have position : base + (tid + 1) = (base + 1) + tid := by omega
        rw [position]
        exact plan
      · change actionsFrom base (worker :: workers.set tid { current with pending := tail }) = rest
        simpa only [actionsFrom, fifo, List.length_nil, List.replicate_zero,
          List.nil_append] using remaining
    | cons head tail =>
      refine ⟨0, worker, head, tail,
        List.replicate tail.length (.drain base) ++ actionsFrom (base + 1) workers,
        rfl, fifo, ?_, rfl⟩
      simp only [actionsFrom, fifo, List.length_cons, List.replicate_succ,
        List.cons_append, Nat.add_zero]

private theorem drainAll_enabled (count : Nat) {state : State} {profile : Profile}
    (valid : WellFormed state profile) (size : totalPending state = count) :
    ∃ result, drainAll state profile = .ok result := by
  induction count generalizing state with
  | zero =>
    have empty : actions state = [] :=
      List.length_eq_zero_iff.mp ((actions_length state).trans size)
    exact ⟨(state, []), by simp only [drainAll, empty, schedule]⟩
  | succ count ih =>
    have nonempty : actions state ≠ [] := by
      intro empty
      have length := actions_length state
      rw [empty] at length
      simp only [List.length_nil] at length
      omega
    obtain ⟨tid, worker, head, tail, rest, live, fifo, plan, remaining⟩ :=
      actionsFrom_head state.workers 0 nonempty
    have planned : actions state = .drain tid :: rest := by
      simpa only [actions, Nat.zero_add] using plan
    have gate := (valid.2 worker (List.mem_of_getElem? live)).2 head
      (by rw [fifo]; exact List.mem_cons_self)
    obtain ⟨output, published⟩ := Queue.publish_enabled valid.1 gate
    let next := install state tid output.1 { worker with pending := tail }
    have stepped : drain state tid profile = .ok (next, .drained tid head) := by
      simp [drain, live, fifo, published, next]
    have nextPlan : actions next = rest := remaining
    have decrease : totalPending next + 1 = totalPending state := drain_totalPending stepped
    have nextSize : totalPending next = count := by omega
    obtain ⟨result, executed⟩ := ih (drain_wellFormed valid stepped) nextSize
    have following : schedule next rest profile = .ok result := by
      change schedule next (actions next) profile = .ok result at executed
      rwa [nextPlan] at executed
    refine ⟨(result.1, .drained tid head :: result.2), ?_⟩
    change schedule state (actions state) profile = _
    rw [planned]
    simp only [schedule, step, stepped, ok_bind, following, pure_ok]

/-- A successful actual closure, with explicit frames and initial provenance
boundary. The worker equality retains all fields except the cleared FIFOs. -/
structure Certificate (initial : State) (result : State × List Observation)
    (profile : Profile) : Prop where
  scheduled : schedule initial (actions initial) profile = .ok result
  wellFormed : WellFormed result.1 profile
  quiescent : Quiescent result.1
  workers : result.1.workers = initial.workers.map clearPending
  stable : Stable initial.world result.1.world
  drainOnly : DrainOnly (actions initial)
  actionCount : (actions initial).length = totalPending initial
  observationCount : result.2.length = totalPending initial
  publications : ∀ observation ∈ result.2, ∃ tid entry,
    observation = .drained tid entry ∧ StoreHistory.Queued initial tid entry
  retired : ∀ observation ∈ result.2, observation.retired = 0

/-- Construct the successful final state and its exact finite drain schedule
from the current invariant alone. No future step successes, desired final state,
instruction validity, Sequenced, or empty-initial-queue premise is required. -/
theorem drainAll_complete {state : State} {profile : Profile}
    (valid : WellFormed state profile) :
    ∃ result, drainAll state profile = .ok result ∧ Certificate state result profile := by
  obtain ⟨result, executed⟩ := drainAll_enabled (totalPending state) valid rfl
  have scheduled : schedule state (actions state) profile = .ok result := executed
  have only := actions_drainOnly state
  have count := schedule_count only scheduled
  rw [actions_length] at count
  have zero : totalPending result.1 = 0 := by omega
  have quiet := (totalPending_zero_iff result.1).mp zero
  obtain ⟨workers, stable⟩ := schedule_frames only scheduled
  have publications := schedule_publications only scheduled
  refine ⟨result, executed, ⟨scheduled, schedule_wellFormed valid scheduled, quiet,
    (quiescent_clear quiet).symm.trans workers, stable, only, actions_length state,
    (ScheduleTrace.length scheduled).trans (actions_length state), publications, ?_⟩⟩
  intro observation member
  obtain ⟨tid, entry, rfl, _queued⟩ := publications observation member
  rfl

/-- The exact final worker at every original index. Its context (RF/RIP/flags),
resources, phase and nextStore are definitionally those of `prior`. -/
theorem Certificate.worker {state : State} {result : State × List Observation}
    {profile : Profile} (certificate : Certificate state result profile)
    {tid : Nat} {prior : Worker} (live : state.workers[tid]? = some prior) :
    result.1.workers[tid]? = some (clearPending prior) := by
  rw [certificate.workers, List.getElem?_map, live]
  rfl

/-- This initial-queue origin does not require WF or Sequenced: it follows
from the successful production run and its drain-only actions. -/
theorem drainAll_queued_origin {state : State} {result : State × List Observation}
    {profile : Profile} {tid : Nat} {entry : Pending}
    (success : drainAll state profile = .ok result)
    (observed : .drained tid entry ∈ result.2) : StoreHistory.Queued state tid entry := by
  obtain ⟨publisher, original, same, queued⟩ :=
    schedule_publications (actions_drainOnly state) success (.drained tid entry) observed
  cases same
  exact queued

/-- Publication after a history-backed prefix reuses that exact prefix's
existing boundary-or-real-issue origin, including complete managed descriptors. -/
theorem publication_origin_after_prefix {initial state : State} {historyActions : List Action}
    {prefixObservations : List Observation} {result : State × List Observation}
    {profile : Profile} {tid : Nat} {entry : Pending}
    (history : schedule initial historyActions profile = .ok (state, prefixObservations))
    (success : drainAll state profile = .ok result)
    (observed : .drained tid entry ∈ result.2) :
    StoreHistory.Origin initial historyActions (state, prefixObservations) profile tid entry :=
  StoreHistory.schedule_pending_origin history (drainAll_queued_origin success observed)

/-- An empty history boundary eliminates the initial-queue alternative. No
numerical occurrence integrity is used to invent this actual issuing event. -/
theorem publication_issued_after_prefix {initial state : State} {historyActions : List Action}
    {prefixObservations : List Observation} {result : State × List Observation}
    {profile : Profile} {tid : Nat} {entry : Pending} (empty : Quiescent initial)
    (history : schedule initial historyActions profile = .ok (state, prefixObservations))
    (success : drainAll state profile = .ok result)
    (observed : .drained tid entry ∈ result.2) :
    StoreHistory.IssuedIn profile tid entry initial historyActions (state, prefixObservations) :=
  StoreHistory.schedule_pending_issued empty history (drainAll_queued_origin success observed)

private theorem schedule_append {state : State} {historyActions suffix : List Action}
    {middle result : State × List Observation} {profile : Profile}
    (firstRun : schedule state historyActions profile = .ok middle)
    (lastRun : schedule middle.1 suffix profile = .ok result) :
    schedule state (historyActions ++ suffix) profile = .ok (result.1, middle.2 ++ result.2) := by
  induction historyActions generalizing state middle with
  | nil =>
    have same : (state, []) = middle := Except.ok.inj firstRun
    subst middle
    exact lastRun
  | cons action rest ih =>
    obtain ⟨first, tail, stepped, following, same⟩ := schedule_cons_ok firstRun
    rw [same] at lastRun ⊢
    have appended := ih following lastRun
    simp only [List.cons_append, schedule, stepped, ok_bind, appended, pure_ok]

/-- Close an actual history prefix and concatenate the actual drain run. The
only future premise is current WF; publication origins remain in the supplied
history, with its original initial-queue boundary still explicit. -/
theorem drainAll_after_prefix {initial state : State} {historyActions : List Action}
    {prefixObservations : List Observation} {profile : Profile}
    (history : schedule initial historyActions profile = .ok (state, prefixObservations))
    (valid : WellFormed state profile) :
    ∃ result, drainAll state profile = .ok result ∧ Certificate state result profile ∧
      schedule initial (historyActions ++ actions state) profile =
        .ok (result.1, prefixObservations ++ result.2) ∧
      (∀ tid entry, .drained tid entry ∈ result.2 →
        StoreHistory.Origin initial historyActions (state, prefixObservations) profile tid entry) := by
  obtain ⟨result, executed, certificate⟩ := drainAll_complete valid
  refine ⟨result, executed, certificate, schedule_append history certificate.scheduled, ?_⟩
  intro tid entry observed
  exact publication_origin_after_prefix history executed observed

end EDSL.OS.TSO64.DrainClosure
