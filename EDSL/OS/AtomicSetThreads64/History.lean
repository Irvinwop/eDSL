/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.AtomicSetThreads64.Lifecycle
import EDSL.OS.AtomicSetThreads64.Dispatch

set_option warningAsError true

namespace EDSL.OS.AtomicSetThreads64
open X86 AddressSpace

/-- Only successful managed wrappers can change this history. In particular,
there is no constructor admitting an arbitrary lower resource history. -/
inductive Step : State → Option Atomics64.Event → State → Prop where
  | spawn {before parent start available result}
      (success : AtomicSetThreads64.spawn before parent start available = .ok result) :
      Step before none result.1
  | dispatch {before identifier af result}
      (success : AtomicSetThreads64.dispatch before identifier af = .ok result) :
      Step before result.2 result.1
  | join {before parent identifier result}
      (success : AtomicSetThreads64.join before parent identifier = .ok result) :
      Step before none result.1
  | mutate {before operation result}
      (success : AtomicSetThreads64.mutate before operation = .ok result) :
      Step before none result.1
  | retire {before owner cell after}
      (success : AtomicSetThreads64.retire before owner cell = .ok after) :
      Step before none after
  | idle {state} : Step state none state

/-- Administrative positions and all actual optional instruction labels are
retained. An explicit idle consumes one position. -/
inductive History : State → List (Option Atomics64.Event) → State → Prop where
  | refl {state} : History state [] state
  | next {before middle after label labels} (first : Step before label middle)
      (tail : History middle labels after) : History before (label :: labels) after

theorem Step.event_dispatch {before after : State} {event : Atomics64.Event}
    (step : Step before (some event) after) :
    ∃ identifier af, AtomicSetThreads64.dispatch before identifier af = .ok (after, some event) := by
  generalize labelEq : some event = label at step
  cases step with
  | @dispatch identifier af result success =>
    exact ⟨identifier, af, success⟩
  | spawn _ => cases labelEq
  | join _ => cases labelEq
  | mutate _ => cases labelEq
  | retire _ => cases labelEq
  | idle => cases labelEq

theorem History.trans {before middle after : State}
    {firstLabels lastLabels : List (Option Atomics64.Event)}
    (first : History before firstLabels middle) (last : History middle lastLabels after) :
    History before (firstLabels ++ lastLabels) after := by
  induction first with
  | refl => exact last
  | next first _ induction => exact .next first (induction last)

/-- The entire immutable origin is retained, including internal identities and
the literal body. Private contexts and current RAM are deliberately absent. -/
structure WorkerOrigin where
  parent : Nat
  entry : Context
  bytes : List Byte
  operations : List Sequential.LogicalOp
  cell : Atomics64.CellId64
  returnAddress : Word
  handle : Atomics64.HandleId64
  codeLoan : Nat
  stackLoan : Nat

def Worker.origin (worker : Worker) : WorkerOrigin :=
  ⟨worker.parent, worker.entry, worker.bytes, worker.operations, worker.cell,
    worker.returnAddress, worker.handle, worker.codeLoan, worker.stackLoan⟩

/-- Old live identities can disappear only; surviving workers retain their
origin and stored event prefix. Exact accounting of the newly observed suffix
is proved separately; this predicate does not authenticate an earlier past. -/
def Advances (before after : State) : Prop :=
  before.nextThread ≤ after.nextThread ∧
    ∀ identifier, identifier < before.nextThread → ∀ worker,
      after.workers identifier = some worker →
      ∃ previous, before.workers identifier = some previous ∧
        previous.origin = worker.origin ∧ previous.events <+: worker.events

theorem Advances.refl (state : State) : Advances state state :=
  ⟨Nat.le_refl _, fun _ _ worker live => ⟨worker, live, rfl, ⟨[], by simp⟩⟩⟩

theorem Advances.trans {before middle after : State} (first : Advances before middle)
    (last : Advances middle after) : Advances before after := by
  refine ⟨Nat.le_trans first.1 last.1, ?_⟩
  intro identifier below worker live
  obtain ⟨previous, previousAt, origin, eventPrefix⟩ :=
    last.2 identifier (Nat.lt_of_lt_of_le below first.1) worker live
  obtain ⟨original, originalAt, oldOrigin, oldPrefix⟩ := first.2 identifier below previous previousAt
  exact ⟨original, originalAt, oldOrigin.trans origin, oldPrefix.trans eventPrefix⟩

theorem replace_workerAdvances (state : State) (identifier : Nat) (previous current : Worker)
    (shared : Atomics64.State) (live : state.workers identifier = some previous)
    (origin : previous.origin = current.origin) (eventPrefix : previous.events <+: current.events) :
    Advances state { replace state identifier (some current) with shared := shared } := by
  refine ⟨Nat.le_refl _, ?_⟩
  intro query _ worker found
  by_cases own : query = identifier
  · subst query
    simp [replace] at found
    cases found
    exact ⟨previous, live, origin, eventPrefix⟩
  · exact ⟨worker, by simpa [replace, own] using found, rfl, ⟨[], by simp⟩⟩

theorem spawn_advances (state : State) (parent : Nat) (start : Start) (available : Bool)
    (result : State × Nat) (success : spawn state parent start available = .ok result) :
    Advances state result.1 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, same⟩ :=
    spawn_ok _ _ _ _ _ success
  rw [same]
  refine ⟨by simp [install], ?_⟩
  intro identifier below worker found
  have old : identifier ≠ state.nextThread := by omega
  exact ⟨worker, by simpa [install, old] using found, rfl, ⟨[], by simp⟩⟩

theorem join_advances (state : State) (parent identifier : Nat) (result : State × Context)
    (success : join state parent identifier = .ok result) : Advances state result.1 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, same⟩ := join_ok _ _ _ _ success
  rw [same]
  refine ⟨Nat.le_refl _, ?_⟩
  intro query _ worker found
  dsimp only [replace] at found
  split at found
  · cases found
  · exact ⟨worker, found, rfl, ⟨[], by simp⟩⟩

theorem mutate_advances (state : State) (operation : Ownership.Mutation)
    (result : State × Option Ownership.Ticket) (success : mutate state operation = .ok result) :
    Advances state result.1 := by
  obtain ⟨_, _, same⟩ := mutate_ok _ _ _ success
  rw [same]
  exact .refl _

theorem retire_advances (state : State) (owner : Nat) (cell : Atomics64.CellId64) (after : State)
    (success : retire state owner cell = .ok after) : Advances state after := by
  obtain ⟨_, _, _, same⟩ := retire_ok _ _ _ _ success
  rw [same]
  exact .refl _

/-- Allocation preservation frames all eight current bytes, rather than only
the cell registration or a remembered event's after-word. -/
theorem cell_read_of_preserves (before after : Atomics64.State)
    (identifier : Atomics64.CellId64) (cell : Atomics64.Cell)
    (valid : Atomics64.WellFormed before) (live : before.cells identifier = some cell)
    (frame : Ownership.PreservesAllocation before.legacy.shared.resources
      after.legacy.shared.resources cell.ticket.identifier) :
    loadQWord (toMemory after.legacy.shared.resources.space) cell.address =
      loadQWord (toMemory before.legacy.shared.resources.space) cell.address := by
  obtain ⟨allocation, found, _, _, fits, _⟩ := (valid.cells _ _ live).2.1
  have regionValid := (valid.legacy.shared.1.1 _ _ found).2.1
  let loan : Borrowing.Loan := ⟨cell.ticket, cell.owner, cell.owner, allocation.region⟩
  have subregion : Borrowing.Subregion (qwordRegion cell.address) loan.region := of_decide_eq_true fits
  apply loadQWord_congr
  intro offset bound
  exact (toMemory_agrees_at _ _ _ ((frame allocation found).2 _
    (Borrowing.qword_inside loan regionValid cell.address subregion offset bound))).1

theorem mutate_cell_read (state : State) (operation : Ownership.Mutation)
    (result : State × Option Ownership.Ticket) (identifier : Atomics64.CellId64) (cell : Atomics64.Cell)
    (valid : WellFormed state) (live : state.shared.cells identifier = some cell)
    (success : mutate state operation = .ok result) :
    loadQWord (toMemory result.1.shared.legacy.shared.resources.space) cell.address =
      loadQWord (toMemory state.shared.legacy.shared.resources.space) cell.address := by
  obtain ⟨shared, changed, same⟩ := mutate_ok _ _ _ success
  rw [same]
  exact cell_read_of_preserves _ _ identifier cell valid.1 live
    (Atomics64.mutate_preserves_cell _ _ _ valid.1 changed identifier cell live)

theorem retire_resources (state : State) (owner : Nat) (identifier : Atomics64.CellId64) (after : State)
    (success : retire state owner identifier = .ok after) :
    after.shared.legacy.shared.resources = state.shared.legacy.shared.resources := by
  obtain ⟨_, _, retired, same⟩ := retire_ok _ _ _ _ success
  obtain ⟨_, _, _, lowerSame⟩ := Atomics64.retire_ok _ _ _ _ retired
  rw [same, lowerSame]
  rfl

-- Pending concrete Dispatch handoff; planned checked composition, no new model axioms.

theorem Step.wellFormed {before after : State} {label : Option Atomics64.Event}
    (step : Step before label after) (valid : WellFormed before) : WellFormed after := by
  cases step with
  | spawn success => exact spawn_wellFormed _ _ _ _ _ valid success
  | dispatch success => exact dispatch_wellFormed _ _ _ _ valid success
  | join success => exact join_wellFormed _ _ _ _ valid success
  | mutate success => exact mutate_wellFormed _ _ _ valid success
  | retire success => exact retire_wellFormed _ _ _ _ valid success
  | idle => exact valid

theorem History.wellFormed {before after : State} {labels : List (Option Atomics64.Event)}
    (history : History before labels after) (valid : WellFormed before) : WellFormed after := by
  induction history with
  | refl => exact valid
  | next first _ induction => exact induction (first.wellFormed valid)

theorem Step.borrowing {before after : State} {label : Option Atomics64.Event}
    (step : Step before label after) (valid : WellFormed before) :
    Borrowing.History before.shared.legacy.shared after.shared.legacy.shared := by
  cases step with
  | spawn success => exact (spawn_history _ _ _ _ _ success).borrowing
  | dispatch success => exact dispatch_borrowing _ _ _ _ valid success
  | join success => exact (join_history _ _ _ _ success).borrowing
  | mutate success => exact (mutate_history _ _ _ success).borrowing
  | retire success => exact (retire_history _ _ _ _ success).borrowing
  | idle => exact .refl

theorem History.borrowing {before after : State} {labels : List (Option Atomics64.Event)}
    (history : History before labels after) (valid : WellFormed before) :
    Borrowing.History before.shared.legacy.shared after.shared.legacy.shared := by
  induction history with
  | refl => exact .refl
  | next first _ induction =>
    exact Atomics.borrowing_trans (first.borrowing valid) (induction (first.wellFormed valid))

theorem Step.atomicAdvances {before after : State} {label : Option Atomics64.Event}
    (step : Step before label after) (valid : WellFormed before) :
    Atomics64.Advances before.shared after.shared := by
  cases step with
  | spawn success => exact (spawn_history _ _ _ _ _ success).advances
  | dispatch success => exact dispatch_advances _ _ _ _ valid success
  | join success => exact (join_history _ _ _ _ success).advances
  | mutate success => exact (mutate_history _ _ _ success).advances
  | retire success => exact (retire_history _ _ _ _ success).advances
  | idle => exact .refl _

theorem History.atomicAdvances {before after : State} {labels : List (Option Atomics64.Event)}
    (history : History before labels after) (valid : WellFormed before) :
    Atomics64.Advances before.shared after.shared := by
  induction history with
  | refl => exact .refl _
  | next first _ induction => exact (first.atomicAdvances valid).trans (induction (first.wellFormed valid))

theorem dispatch_workerAdvances (state : State) (identifier : Nat) (af : Bool)
    (result : State × Option Atomics64.Event) (valid : WellFormed state)
    (success : dispatch state identifier af = .ok result) : Advances state result.1 := by
  obtain ⟨worker, live, effect⟩ := dispatch_effect _ _ _ _ valid success
  cases effect with
  | logical _ _ _ => exact replace_workerAdvances _ _ _ _ _ live rfl (List.prefix_append _ _)
  | returning _ _ => exact replace_workerAdvances _ _ _ _ _ live rfl List.prefix_rfl

theorem Step.advances {before after : State} {label : Option Atomics64.Event}
    (step : Step before label after) (valid : WellFormed before) : Advances before after := by
  cases step with
  | spawn success => exact spawn_advances _ _ _ _ _ success
  | dispatch success => exact dispatch_workerAdvances _ _ _ _ valid success
  | join success => exact join_advances _ _ _ _ success
  | mutate success => exact mutate_advances _ _ _ success
  | retire success => exact retire_advances _ _ _ _ success
  | idle => exact .refl _

theorem History.advances {before after : State} {labels : List (Option Atomics64.Event)}
    (history : History before labels after) (valid : WellFormed before) : Advances before after := by
  induction history with
  | refl => exact .refl _
  | next first _ induction => exact (first.advances valid).trans (induction (first.wellFormed valid))

/-- No lower OR history is asserted for generic logical instructions. -/
theorem History.loan_stable {before after : State} {labels : List (Option Atomics64.Event)}
    (history : History before labels after) (valid : WellFormed before)
    (identifier : Nat) (below : identifier < before.shared.legacy.shared.nextLoan)
    (loan : Borrowing.Loan) (live : after.shared.legacy.shared.loans identifier = some loan) :
    before.shared.legacy.shared.loans identifier = some loan ∧
      ∀ query, loan.region.Contains query →
        after.shared.legacy.shared.resources.space.cells query = before.shared.legacy.shared.resources.space.cells query :=
  (history.borrowing valid).loan_stable valid.1.legacy.shared identifier below loan live

theorem History.handle_revoked {before after : State} {labels : List (Option Atomics64.Event)}
    (history : History before labels after) (valid : WellFormed before) {identifier : Atomics64.HandleId64}
    (revoked : Atomics64.HandleRevoked before.shared identifier) :
    Atomics64.HandleRevoked after.shared identifier := revoked.persists (history.atomicAdvances valid)

theorem History.cell_revoked {before after : State} {labels : List (Option Atomics64.Event)}
    (history : History before labels after) (valid : WellFormed before) {identifier : Atomics64.CellId64}
    (revoked : Atomics64.CellRevoked before.shared identifier) :
    Atomics64.CellRevoked after.shared identifier := revoked.persists (history.atomicAdvances valid)

theorem History.loan_revoked {before after : State} {labels : List (Option Atomics64.Event)}
    (history : History before labels after) (valid : WellFormed before) {identifier : Nat}
    (revoked : Borrowing.Revoked before.shared.legacy.shared identifier) :
    Borrowing.Revoked after.shared.legacy.shared identifier :=
  revoked.persists valid.1.legacy.shared (history.borrowing valid)

def Revoked (state : State) (identifier : Nat) : Prop :=
  identifier < state.nextThread ∧ state.workers identifier = none

theorem Revoked.persists {before after : State} {labels : List (Option Atomics64.Event)} {identifier : Nat}
    (revoked : Revoked before identifier) (valid : WellFormed before)
    (history : History before labels after) : Revoked after identifier := by
  have advances := history.advances valid
  refine ⟨Nat.lt_of_lt_of_le revoked.1 advances.1, ?_⟩
  cases found : after.workers identifier with
  | none => rfl
  | some worker =>
    obtain ⟨original, originalAt, _, _⟩ := advances.2 identifier revoked.1 worker found
    rw [revoked.2] at originalAt
    cases originalAt

theorem Revoked.dispatch_denied {state : State} {identifier : Nat}
    (revoked : Revoked state identifier) (af : Bool) :
    dispatch state identifier af = .error .missingThread := by simp [dispatch, revoked.2]

theorem join_revokes_thread (state : State) (parent identifier : Nat) (result : State × Context)
    (valid : WellFormed state) (success : join state parent identifier = .ok result) :
    Revoked result.1 identifier := by
  obtain ⟨worker, _, _, _, live, _⟩ := join_ok _ _ _ _ success
  have frames := join_workers _ _ _ _ success
  exact ⟨by rw [frames.2.1]; exact (valid.2 _ _ live).1, frames.1⟩

theorem joined_for_history {before after : State} {middle : State × Context}
    {labels : List (Option Atomics64.Event)} (parent identifier : Nat)
    (valid : WellFormed before) (joined : join before parent identifier = .ok middle)
    (history : History middle.1 labels after) : Revoked after identifier :=
  (join_revokes_thread before parent identifier middle valid joined).persists
    (join_wellFormed _ _ _ _ valid joined) history

theorem joined_resources_for_history {before after : State} {middle : State × Context}
    {labels : List (Option Atomics64.Event)} (parent identifier : Nat)
    (valid : WellFormed before) (joined : join before parent identifier = .ok middle)
    (history : History middle.1 labels after) :
    ∃ worker, before.workers identifier = some worker ∧ Atomics64.HandleRevoked after.shared worker.handle ∧
      Borrowing.Revoked after.shared.legacy.shared worker.codeLoan ∧
      Borrowing.Revoked after.shared.legacy.shared worker.stackLoan := by
  obtain ⟨worker, live, handle, code, stack⟩ := join_revokes _ _ _ _ valid joined
  have nextValid := join_wellFormed _ _ _ _ valid joined
  exact ⟨worker, live, history.handle_revoked nextValid handle,
    history.loan_revoked nextValid code, history.loan_revoked nextValid stack⟩

theorem History.origin_and_prefix {before after : State} {labels : List (Option Atomics64.Event)}
    (history : History before labels after) (valid : WellFormed before)
    (identifier : Nat) (previous current : Worker)
    (live : before.workers identifier = some previous) (survives : after.workers identifier = some current) :
    previous.origin = current.origin ∧ previous.events <+: current.events := by
  obtain ⟨original, originalAt, origin, eventPrefix⟩ := (history.advances valid).2 identifier
    (valid.2 _ _ live).1 current survives
  have same := Option.some.inj (originalAt.symm.trans live)
  subst original
  exact ⟨origin, eventPrefix⟩

def emittedFor (identifier : Nat) (label : Option Atomics64.Event) : Option Atomics64.Event :=
  label.bind (fun event => if event.actor = principal identifier then some event else none)

/-- Exact own-event projection of the rich managed labels. Administrative and
RET positions stay in the source history; no emitted occurrence is collapsed. -/
def workerEvents (identifier : Nat) (labels : List (Option Atomics64.Event)) : List Atomics64.Event :=
  labels.filterMap (emittedFor identifier)

theorem dispatch_worker_events (state : State) (identifier query : Nat) (af : Bool) (worker : Worker)
    (result : State × Option Atomics64.Event) (valid : WellFormed state)
    (live : state.workers query = some worker) (success : dispatch state identifier af = .ok result) :
    ∃ current, result.1.workers query = some current ∧
      current.events = worker.events ++ workerEvents query [result.2] := by
  by_cases own : query = identifier
  · subst query
    obtain ⟨actual, found, effect⟩ := dispatch_effect _ _ _ _ valid success
    have same := Option.some.inj (found.symm.trans live)
    subst actual
    cases effect with
    | @logical op updated _ _ changed =>
      have actor := (Atomics64.logicalUpdate_sound _ _ _ _ _ _ changed).2.2.2.2.1
      exact ⟨{ worker with
        context := applied worker.context updated.2.logical.event.after af,
        cursor := worker.cursor + 1, events := worker.events ++ [updated.2] },
        by simp [replace], by simp [workerEvents, emittedFor, actor]⟩
    | returning _ _ =>
      exact ⟨{ worker with context := returned worker.context worker.returnAddress, phase := .completed },
        by simp [replace], by simp [workerEvents, emittedFor]⟩
  · have kept := ((dispatch_frame _ _ _ _ valid success).2 query own).trans live
    refine ⟨worker, kept, ?_⟩
    obtain ⟨_, _, effect⟩ := dispatch_effect _ _ _ _ valid success
    cases effect with
    | logical _ _ changed =>
      have actor := (Atomics64.logicalUpdate_sound _ _ _ _ _ _ changed).2.2.2.2.1
      have different : principal identifier ≠ principal query := by
        intro equality
        exact own (Nat.add_right_cancel equality.symm)
      simp [workerEvents, emittedFor, actor, different]
    | returning _ _ => simp [workerEvents, emittedFor]

theorem Step.worker_events {before after : State} {label : Option Atomics64.Event}
    (step : Step before label after) (valid : WellFormed before) (identifier : Nat)
    (previous current : Worker) (live : before.workers identifier = some previous)
    (survives : after.workers identifier = some current) :
    current.events = previous.events ++ workerEvents identifier [label] := by
  cases step with
  | spawn success =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, same⟩ :=
      spawn_ok _ _ _ _ _ success
    rw [same] at survives
    have old : identifier ≠ before.nextThread := Nat.ne_of_lt (valid.2 _ _ live).1
    have found : before.workers identifier = some current := by simpa [install, old] using survives
    have equal := Option.some.inj (live.symm.trans found)
    subst current
    simp [workerEvents, emittedFor]
  | dispatch success =>
    obtain ⟨actual, found, exactEvents⟩ := dispatch_worker_events _ _ _ _ _ _ valid live success
    have equal := Option.some.inj (found.symm.trans survives)
    subst actual
    exact exactEvents
  | @join parent joined result success =>
    have frames := join_workers _ _ _ _ success
    by_cases own : identifier = joined
    · subst identifier
      rw [frames.1] at survives
      cases survives
    · have found := (frames.2.2 identifier own).symm.trans survives
      have equal := Option.some.inj (live.symm.trans found)
      subst current
      simp [workerEvents, emittedFor]
  | mutate success =>
    obtain ⟨_, _, same⟩ := mutate_ok _ _ _ success
    rw [same] at survives
    have equal := Option.some.inj (live.symm.trans survives)
    subst current
    simp [workerEvents, emittedFor]
  | retire success =>
    obtain ⟨_, _, _, same⟩ := retire_ok _ _ _ _ success
    rw [same] at survives
    have equal := Option.some.inj (live.symm.trans survives)
    subst current
    simp [workerEvents, emittedFor]
  | idle =>
    have equal := Option.some.inj (live.symm.trans survives)
    subst current
    simp [workerEvents, emittedFor]

/-- Exact extension holds across checked lifecycle/metadata changes as well as
peer RMWs. Survival uses the original monotone identity, never reinstallation. -/
theorem History.worker_events {before after : State} {labels : List (Option Atomics64.Event)}
    (history : History before labels after) (valid : WellFormed before) (identifier : Nat)
    (previous current : Worker) (live : before.workers identifier = some previous)
    (survives : after.workers identifier = some current) :
    current.events = previous.events ++ workerEvents identifier labels := by
  induction history generalizing previous current with
  | refl =>
    have equal := Option.some.inj (live.symm.trans survives)
    subst current
    simp [workerEvents]
  | @next before middle after label labels first tail induction =>
    have nextValid := first.wellFormed valid
    obtain ⟨middle, middleAt, _, _⟩ := (tail.advances nextValid).2 identifier
      (Nat.lt_of_lt_of_le (valid.2 _ _ live).1 (first.advances valid).1) current survives
    have initial := first.worker_events valid identifier previous middle live middleAt
    have rest := induction nextValid middle current middleAt survives
    rw [rest, initial, List.append_assoc]
    cases emitted : emittedFor identifier label <;> simp [workerEvents, emitted]

/-- Collection exposes the current resources that authorize its returned ABI
frame. The return value contains only private registers/RIP/flags. -/
theorem join_current (state : State) (parent identifier : Nat) (result : State × Context)
    (valid : WellFormed state) (success : join state parent identifier = .ok result) :
    ∃ worker, state.workers identifier = some worker ∧ WorkerValid state.shared identifier worker ∧
      worker.phase = .completed ∧ result.2 = worker.context ∧
      result.1.shared.legacy.shared.resources = state.shared.legacy.shared.resources ∧
      result.1.shared.cells = state.shared.cells := by
  obtain ⟨worker, _, _, _, live, _, completed, _, _, _, same⟩ := join_ok _ _ _ _ success
  exact ⟨worker, live, (valid.2 _ _ live).2, completed, by rw [same], join_resources _ _ _ _ success⟩

theorem joined_private_frame {before after : State} {labels : List (Option Atomics64.Event)}
    (history : History before labels after) (valid : WellFormed before)
    (identifier : Nat) (worker : Worker) (live : before.workers identifier = some worker)
    (parent : Nat) (result : State × Context) (joined : join after parent identifier = .ok result) :
    result.2.registers .rsp = worker.entry.registers .rsp + 8 ∧
      result.2.rip = worker.returnAddress ∧
      (∀ register, register ≠ .rsp → result.2.registers register = worker.entry.registers register) ∧
      result.2.flags &&& ~~~arithmeticFlagMask = worker.entry.flags &&& ~~~arithmeticFlagMask := by
  obtain ⟨current, currentAt, currentValid, completed, context, _⟩ :=
    join_current _ _ _ _ (history.wellFormed valid) joined
  have origin := (history.origin_and_prefix valid identifier worker current live currentAt).1
  have entry : worker.entry = current.entry := congrArg WorkerOrigin.entry origin
  have target : worker.returnAddress = current.returnAddress := congrArg WorkerOrigin.returnAddress origin
  obtain ⟨_, rsp, rip, registers, flags⟩ := currentValid.completed_result completed
  rw [context, entry, target]
  exact ⟨rsp, rip, registers, flags⟩

/-- A no-event managed position frames the current value. Metadata changes
are retained in History and are not presented as a LogicalTrace stutter. -/
theorem Step.cell_read_none {before after : State} (step : Step before none after)
    (identifier : Atomics64.CellId64) (cell : Atomics64.Cell)
    (valid : WellFormed before) (live : before.shared.cells identifier = some cell) :
    loadQWord (toMemory after.shared.legacy.shared.resources.space) cell.address =
      loadQWord (toMemory before.shared.legacy.shared.resources.space) cell.address := by
  generalize labelEq : (none : Option Atomics64.Event) = label at step
  cases step with
  | spawn success => rw [spawn_resources _ _ _ _ _ success]
  | @dispatch thread af result success =>
    have shape : result = (result.1, none) := Prod.ext rfl labelEq.symm
    rw [dispatch_return_shared _ _ _ _ valid (success.trans (congrArg Except.ok shape))]
  | join success => rw [(join_resources _ _ _ _ success).1]
  | mutate success => exact mutate_cell_read _ _ _ _ _ valid live success
  | retire success => rw [retire_resources _ _ _ _ success]
  | idle => rfl

end EDSL.OS.AtomicSetThreads64
