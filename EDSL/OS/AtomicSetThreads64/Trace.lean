/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.AtomicSetThreads64.History
import EDSL.OS.AtomicSetThreads64.Scheduling
import EDSL.OS.Atomics64.OrderedHistory

set_option warningAsError true

namespace EDSL.OS.AtomicSetThreads64
open X86 AddressSpace

/-- Every observation binds its selection and AF choice to an actual checked
instruction. The scheduling relation already retains the no-event RET. -/
abbrev InstructionTrace := DispatchHistory

theorem schedule_instructions (state : State) (selections : List Selection)
    (result : State × List Observation) (success : schedule state selections = .ok result) :
    InstructionTrace state result.2 result.1 := schedule_history _ _ _ success

theorem InstructionTrace.managed {before after : State} {observations : List Observation}
    (trace : InstructionTrace before observations after) :
    History before (observations.map Prod.snd) after := by
  induction trace with
  | refl => exact .refl
  | next selected _ induction => exact .next (.dispatch selected) induction

/-- Current resources, actual decode, complete fetch extent and exact CPU/OS
coupling for a selected RMW. All GPRs and logical flags are exposed by the
explicit successor context; its memory is the entire current updated RAM. -/
theorem dispatch_atomic_origin (state : State) (identifier : Nat) (af : Bool)
    (after : State) (event : Atomics64.Event) (valid : WellFormed state)
    (success : dispatch state identifier af = .ok (after, some event)) :
    ∃ worker op,
      state.workers identifier = some worker ∧ WorkerValid state.shared identifier worker ∧
      worker.phase = .running ∧ worker.operations[worker.cursor]? = some op ∧
      LockedSet64.decodeAt (worker.context.snapshot state.shared.legacy.shared.resources.space) =
        .ok (.logicalRdiRsi op) ∧
      worker.context.rip = worker.entry.rip + BitVec.ofNat 64 (4 * worker.cursor) ∧
      4 * worker.cursor + 4 ≤ worker.bytes.length ∧
      Atomics64.logicalUpdate op state.shared (principal identifier) worker.handle
        (worker.context.registers .rsi) = .ok (after.shared, event) ∧
      LockedSet64.step af (worker.context.snapshot state.shared.legacy.shared.resources.space) =
        .ok ⟨.atomic64 event.logical
          ((applied worker.context event.logical.event.after af).snapshot
            after.shared.legacy.shared.resources.space), [.rmw8 (worker.entry.registers .rdi)]⟩ ∧
      event.logical.op = op ∧ event.actor = principal identifier ∧
      event.handle = worker.handle ∧ event.cell = worker.cell ∧
      event.logical.event.address = worker.entry.registers .rdi ∧
      event.logical.mask = worker.entry.registers .rsi ∧
      after.workers identifier = some { worker with
        context := applied worker.context event.logical.event.after af,
        cursor := worker.cursor + 1, events := worker.events ++ [event] } := by
  obtain ⟨worker, live, effect⟩ := dispatch_effect _ _ _ _ valid success
  cases effect with
  | @logical op updated running selected changed =>
    have workerValid := (valid.2 _ _ live).2
    have decoded := workerValid.running_logical_decode running selected
    obtain ⟨handle, cell, authorized, address, linked⟩ := workerValid.authorized valid.1
    have operand : worker.context.registers .rdi = cell.address := by
      rw [workerValid.running_registers running]
      exact address.symm
    have machine := Atomics64.logicalUpdate_step op _ _ _ _ _ handle cell
      (worker.context.snapshot state.shared.legacy.shared.resources.space) af changed authorized
      rfl operand rfl decoded
    have sound := Atomics64.logicalUpdate_sound _ _ _ _ _ _ changed
    have identity := Atomics64.logicalUpdate_identity _ _ _ _ _ _ _ _ changed authorized
    have continuing := (List.getElem?_eq_some_iff.mp selected).1
    refine ⟨worker, op, live, workerValid, running, selected, decoded,
      workerValid.running_rip running, ?_, changed, ?_, sound.2.1,
      sound.2.2.2.2.1, sound.2.2.2.2.2, identity.1.trans linked,
      identity.2.trans address, ?_, by simp [replace]⟩
    · rw [workerValid.layout, bodyBytes_length]
      omega
    · simpa [address, LockedSet64.afterLogical, applied, Threads.Context.snapshot, replace] using machine
    · exact sound.2.2.1.trans (congrFun (workerValid.running_registers running) .rsi)

/-- RET reads the currently retained original caller slot, covers its own
complete byte, increments RSP once and leaves the entire shared state current. -/
theorem dispatch_return_origin (state : State) (identifier : Nat) (af : Bool)
    (after : State) (valid : WellFormed state)
    (success : dispatch state identifier af = .ok (after, none)) :
    ∃ worker, state.workers identifier = some worker ∧ WorkerValid state.shared identifier worker ∧
      worker.phase = .running ∧ worker.cursor = worker.operations.length ∧
      LockedSet64.decodeAt (worker.context.snapshot state.shared.legacy.shared.resources.space) = .ok .ret ∧
      4 * worker.cursor + 1 ≤ worker.bytes.length ∧
      readWord (toMemory state.shared.legacy.shared.resources.space) (worker.entry.registers .rsp) =
        .ok worker.returnAddress ∧
      LockedSet64.step af (worker.context.snapshot state.shared.legacy.shared.resources.space) =
        .ok ⟨.returned ((returned worker.context worker.returnAddress).snapshot
          state.shared.legacy.shared.resources.space), [.stack8 (worker.entry.registers .rsp)]⟩ ∧
      after.shared = state.shared ∧
      after.workers identifier = some { worker with
        context := returned worker.context worker.returnAddress, phase := .completed } := by
  obtain ⟨worker, live, effect⟩ := dispatch_effect _ _ _ _ valid success
  cases effect with
  | returning running terminal =>
    have workerValid := (valid.2 _ _ live).2
    refine ⟨worker, live, workerValid, running, terminal,
      workerValid.running_ret_decode running terminal, ?_, workerValid.target, ?_, rfl,
      by simp [replace]⟩
    · rw [workerValid.layout, bodyBytes_length, terminal]
      exact Nat.le_refl _
    · simpa only [workerValid.running_registers running] using
        workerValid.running_ret_step running terminal af

theorem InstructionTrace.event_bound {state after : State} {observations : List Observation}
    (trace : InstructionTrace state observations after) (valid : WellFormed state)
    (selection : Selection) (event : Atomics64.Event)
    (member : (selection, some event) ∈ observations) :
    ∃ before next worker op, WellFormed before ∧
      before.workers selection.1 = some worker ∧ WorkerValid before.shared selection.1 worker ∧
      dispatch before selection.1 selection.2 = .ok (next, some event) ∧
      LockedSet64.decodeAt (worker.context.snapshot before.shared.legacy.shared.resources.space) =
        .ok (.logicalRdiRsi op) ∧
      Atomics64.logicalUpdate op before.shared (principal selection.1) worker.handle
        (worker.context.registers .rsi) = .ok (next.shared, event) ∧
      event.logical.op = op ∧ event.actor = principal selection.1 ∧
      event.handle = worker.handle ∧ event.cell = worker.cell ∧
      event.logical.mask = worker.entry.registers .rsi := by
  induction trace with
  | refl => simp at member
  | @next before middle after chosen label rest selected tail induction =>
    rcases List.mem_cons.mp member with head | member
    · have same := Prod.mk.inj head
      have chosenEq : chosen = selection := same.1.symm
      subst chosen
      have hasEvent : dispatch before selection.1 selection.2 = .ok (middle, some event) := by
        simpa only [same.2] using selected
      obtain ⟨worker, op, live, workerValid, _, _, decoded, _, _, changed, _, tag,
        actor, handle, cell, _, mask, _⟩ := dispatch_atomic_origin _ _ _ _ _ valid hasEvent
      exact ⟨before, middle, worker, op, valid, live, workerValid, hasEvent, decoded,
        changed, tag, actor, handle, cell, mask⟩
    · exact induction (dispatch_wellFormed _ _ _ _ valid selected) member

/-- Rich histories retain the same current-resource instruction origins at
events separated by spawn, collection, mutations or explicit idle positions. -/
theorem History.event_bound {state after : State} {labels : List (Option Atomics64.Event)}
    (history : History state labels after) (valid : WellFormed state)
    (event : Atomics64.Event) (member : some event ∈ labels) :
    ∃ before next thread af worker op, WellFormed before ∧
      before.workers thread = some worker ∧ WorkerValid before.shared thread worker ∧
      dispatch before thread af = .ok (next, some event) ∧
      LockedSet64.decodeAt (worker.context.snapshot before.shared.legacy.shared.resources.space) =
        .ok (.logicalRdiRsi op) ∧
      4 * worker.cursor + 4 ≤ worker.bytes.length ∧
      Atomics64.logicalUpdate op before.shared (principal thread) worker.handle
        (worker.context.registers .rsi) = .ok (next.shared, event) ∧
      event.logical.op = op ∧ event.actor = principal thread ∧
      event.handle = worker.handle ∧ event.cell = worker.cell ∧
      event.logical.mask = worker.entry.registers .rsi := by
  induction history with
  | refl => simp at member
  | next first tail induction =>
    rcases List.mem_cons.mp member with head | member
    · cases head
      obtain ⟨thread, af, dispatched⟩ := first.event_dispatch
      obtain ⟨worker, op, live, workerValid, _, _, decoded, _, covered, changed, _, tag,
        actor, handle, cell, _, mask, _⟩ := dispatch_atomic_origin _ _ _ _ _ valid dispatched
      exact ⟨_, _, thread, af, worker, op, valid, live, workerValid, dispatched,
        decoded, covered, changed, tag, actor, handle, cell, mask⟩
    · exact induction (first.wellFormed valid) member

theorem InstructionTrace.worker_events {before after : State} {observations : List Observation}
    (trace : InstructionTrace before observations after) (valid : WellFormed before)
    (identifier : Nat) (previous current : Worker)
    (live : before.workers identifier = some previous) (survives : after.workers identifier = some current) :
    previous.origin = current.origin ∧
      current.events = previous.events ++ workerEvents identifier (observations.map Prod.snd) :=
  ⟨(trace.managed.origin_and_prefix valid identifier previous current live survives).1,
    trace.managed.worker_events valid identifier previous current live survives⟩

/-- An unselected peer retains its entire private worker, including context,
event prefix, cursor and phase. Shared memory remains current and may change. -/
theorem InstructionTrace.peer {before after : State} {observations : List Observation}
    (trace : InstructionTrace before observations after) (valid : WellFormed before)
    (identifier : Nat) (worker : Worker) (live : before.workers identifier = some worker)
    (unselected : ∀ observation ∈ observations, observation.1.1 ≠ identifier) :
    after.workers identifier = some worker := by
  induction trace with
  | refl => exact live
  | @next before middle after selection label rest selected tail induction =>
    have other := unselected (selection, label) (by simp)
    have retained := ((dispatch_frame _ _ _ _ valid selected).2 identifier (Ne.symm other)).trans live
    exact induction (dispatch_wellFormed _ _ _ _ valid selected) retained
      (fun observation member => unselected observation (List.mem_cons_of_mem _ member))

def AllOn (state : State) (cell : Atomics64.CellId64) : Prop :=
  ∀ identifier worker, state.workers identifier = some worker → worker.cell = cell

theorem dispatch_allOn (state : State) (identifier : Nat) (af : Bool)
    (result : State × Option Atomics64.Event) (cell : Atomics64.CellId64)
    (valid : WellFormed state) (allOn : AllOn state cell)
    (success : dispatch state identifier af = .ok result) : AllOn result.1 cell := by
  obtain ⟨selected, live, effect⟩ := dispatch_effect _ _ _ _ valid success
  cases effect <;> intro query worker found
  all_goals
    by_cases own : query = identifier
    · subst query
      simp [replace] at found
      cases found
      exact allOn identifier selected live
    · exact allOn query worker (by simpa [replace, own] using found)

/-- Dispatch-only histories with one persistent cell genuinely have lower
LogicalTrace endpoints. RET is justified by equality of the entire shared
state. This theorem is not applied across administrative metadata changes. -/
theorem InstructionTrace.logicalTrace {before after : State} {observations : List Observation}
    (trace : InstructionTrace before observations after)
    (identifier : Atomics64.CellId64) (cell : Atomics64.Cell) (valid : WellFormed before)
    (live : before.shared.cells identifier = some cell) (allOn : AllOn before identifier) :
    Atomics64.LogicalTrace identifier cell before.shared (events observations) after.shared := by
  induction trace with
  | refl => exact .refl live
  | @next before middle after selection label rest selected tail induction =>
    have keeps := dispatch_keeps _ _ _ _ valid selected
    have nextLive : middle.shared.cells identifier = some cell := by rw [keeps.2.1]; exact live
    have remainder := induction (dispatch_wellFormed _ _ _ _ valid selected) nextLive
      (dispatch_allOn _ _ _ _ _ valid allOn selected)
    cases label with
    | none =>
      have current := dispatch_return_shared _ _ _ _ valid selected
      simpa only [events_none, current] using remainder
    | some event =>
      obtain ⟨worker, op, workerAt, _, _, _, _, _, _, changed, _, _, _, _, identity, _⟩ :=
        dispatch_atomic_origin _ _ _ _ _ valid selected
      exact .next changed (identity.trans (allOn _ _ workerAt)) remainder

theorem schedule_logicalTrace (state : State) (selections : List Selection)
    (result : State × List Observation) (identifier : Atomics64.CellId64) (cell : Atomics64.Cell)
    (valid : WellFormed state) (live : state.shared.cells identifier = some cell)
    (allOn : AllOn state identifier) (success : schedule state selections = .ok result) :
    Atomics64.LogicalTrace identifier cell state.shared (events result.2) result.1.shared :=
  (schedule_instructions _ _ _ success).logicalTrace identifier cell valid live allOn

theorem schedule_orderedMathematicalResult (state : State) (selections : List Selection)
    (result : State × List Observation) (identifier : Atomics64.CellId64) (cell : Atomics64.Cell)
    (initial : Word) (valid : WellFormed state) (live : state.shared.cells identifier = some cell)
    (allOn : AllOn state identifier)
    (read : loadQWord (toMemory state.shared.legacy.shared.resources.space) cell.address = .ok initial)
    (success : schedule state selections = .ok result) :
    ∃ final, loadQWord (toMemory result.1.shared.legacy.shared.resources.space) cell.address = .ok final ∧
      Logical64.OrderedMathematicalResult initial
        ((events result.2).map Atomics64.Event.orderedRequest) final :=
  (schedule_logicalTrace _ _ _ _ _ valid live allOn success).orderedMathematicalResult initial read

/-- Present finite count bounds construct the actual instructions and their
independent ordered result for every AF choice retained in the selections. -/
theorem schedule_enabled_ordered (state : State) (selections : List Selection)
    (identifier : Atomics64.CellId64) (cell : Atomics64.Cell) (initial : Word)
    (valid : WellFormed state) (live : state.shared.cells identifier = some cell)
    (allOn : AllOn state identifier) (legal : Legal state selections)
    (read : loadQWord (toMemory state.shared.legacy.shared.resources.space) cell.address = .ok initial) :
    ∃ after observations final, schedule state selections = .ok (after, observations) ∧
      WellFormed after ∧ InstructionTrace state observations after ∧
      loadQWord (toMemory after.shared.legacy.shared.resources.space) cell.address = .ok final ∧
      Logical64.OrderedMathematicalResult initial
        ((events observations).map Atomics64.Event.orderedRequest) final := by
  obtain ⟨result, success⟩ := schedule_enabled _ _ valid legal
  obtain ⟨final, finalRead, mathematical⟩ :=
    schedule_orderedMathematicalResult _ _ _ _ _ _ valid live allOn read success
  exact ⟨result.1, result.2, final, success, schedule_wellFormed _ _ _ valid success,
    schedule_instructions _ _ _ success, finalRead, mathematical⟩

/-- The same registered cell is live at every state, including both endpoints,
and every emitted event selects it. Spawn, join, mutations and retirement of
other cells remain actual positions, rather than erased endpoint changes. -/
inductive FixedCellEpoch (identifier : Atomics64.CellId64) (cell : Atomics64.Cell) :
    State → List (Option Atomics64.Event) → State → Prop where
  | refl {state} (live : state.shared.cells identifier = some cell) :
      FixedCellEpoch identifier cell state [] state
  | next {before middle after label labels}
      (step : Step before label middle)
      (live : before.shared.cells identifier = some cell)
      (selected : ∀ event, label = some event → event.cell = identifier)
      (tail : FixedCellEpoch identifier cell middle labels after) :
      FixedCellEpoch identifier cell before (label :: labels) after

theorem FixedCellEpoch.history {identifier : Atomics64.CellId64} {cell : Atomics64.Cell}
    {before after : State} {labels : List (Option Atomics64.Event)}
    (epoch : FixedCellEpoch identifier cell before labels after) : History before labels after := by
  induction epoch with
  | refl _ => exact .refl
  | next step _ _ _ induction => exact .next step induction

theorem FixedCellEpoch.initial_cell {identifier : Atomics64.CellId64} {cell : Atomics64.Cell}
    {before after : State} {labels : List (Option Atomics64.Event)}
    (epoch : FixedCellEpoch identifier cell before labels after) :
    before.shared.cells identifier = some cell := by
  cases epoch with
  | refl live => exact live
  | next _ live _ _ => exact live

theorem FixedCellEpoch.final_cell {identifier : Atomics64.CellId64} {cell : Atomics64.Cell}
    {before after : State} {labels : List (Option Atomics64.Event)}
    (epoch : FixedCellEpoch identifier cell before labels after) :
    after.shared.cells identifier = some cell := by
  induction epoch with
  | refl live => exact live
  | next _ _ _ _ induction => exact induction

theorem FixedCellEpoch.trans {identifier : Atomics64.CellId64} {cell : Atomics64.Cell}
    {before middle after : State} {firstLabels lastLabels : List (Option Atomics64.Event)}
    (first : FixedCellEpoch identifier cell before firstLabels middle)
    (last : FixedCellEpoch identifier cell middle lastLabels after) :
    FixedCellEpoch identifier cell before (firstLabels ++ lastLabels) after := by
  induction first with
  | refl _ => exact last
  | next step live selected _ induction => exact .next step live selected (induction last)

theorem FixedCellEpoch.prepend_none {identifier : Atomics64.CellId64} {cell : Atomics64.Cell}
    {before middle after : State} {labels : List (Option Atomics64.Event)}
    (step : Step before none middle) (live : before.shared.cells identifier = some cell)
    (tail : FixedCellEpoch identifier cell middle labels after) :
    FixedCellEpoch identifier cell before (none :: labels) after :=
  .next step live (by intro event impossible; cases impossible) tail

/-- A dispatch trace supplies the per-state epoch directly. It suffices that
its emitted events select the cell; unscheduled workers may use other cells. -/
theorem InstructionTrace.epoch {before after : State} {observations : List Observation}
    (trace : InstructionTrace before observations after)
    (identifier : Atomics64.CellId64) (cell : Atomics64.Cell) (valid : WellFormed before)
    (live : before.shared.cells identifier = some cell)
    (selectedCell : ∀ event ∈ events observations, event.cell = identifier) :
    FixedCellEpoch identifier cell before (observations.map Prod.snd) after := by
  induction trace with
  | refl => exact .refl live
  | @next before middle after selection label rest selected tail induction =>
    have keeps := dispatch_keeps _ _ _ _ valid selected
    have nextLive : middle.shared.cells identifier = some cell := by rw [keeps.2.1]; exact live
    have tailSelected : ∀ event ∈ events rest, event.cell = identifier := by
      intro event member
      apply selectedCell event
      cases label <;> simp [member]
    refine .next (.dispatch selected) live ?_
      (induction (dispatch_wellFormed _ _ _ _ valid selected) nextLive tailSelected)
    intro event emitted
    change label = some event at emitted
    subst label
    exact selectedCell event (by simp)

/-- Administrative steps frame the current read. Every actual RMW reads the
preceding word, even if its output is unchanged or later XORs cancel it. -/
theorem FixedCellEpoch.chain {identifier : Atomics64.CellId64} {cell : Atomics64.Cell}
    {before after : State} {labels : List (Option Atomics64.Event)}
    (epoch : FixedCellEpoch identifier cell before labels after) (valid : WellFormed before)
    (initial : Word)
    (read : loadQWord (toMemory before.shared.legacy.shared.resources.space) cell.address = .ok initial) :
    ∃ final, loadQWord (toMemory after.shared.legacy.shared.resources.space) cell.address = .ok final ∧
      Atomics64.LogicalChain initial (labels.filterMap id) final := by
  induction epoch generalizing initial with
  | refl _ => exact ⟨initial, read, .nil⟩
  | @next before middle after label labels step live selected tail induction =>
    have nextValid := step.wellFormed valid
    cases label with
    | none =>
      have nextRead := (step.cell_read_none identifier cell valid live).trans read
      exact induction nextValid initial nextRead
    | some event =>
      obtain ⟨thread, af, dispatched⟩ := step.event_dispatch
      obtain ⟨worker, op, _, _, _, _, changed⟩ :=
        dispatch_atomic_operation _ _ _ _ _ valid dispatched
      have effect := Atomics64.logicalUpdate_sound _ _ _ _ _ _ changed
      have address := Atomics64.logicalUpdate_registered op _ _ _ _ _ identifier cell changed live
        (selected event rfl)
      have current := effect.1.2.2.1
      rw [address, read] at current
      have same : event.logical.event.before = initial := (Except.ok.inj current).symm
      have readback := effect.1.readback
      rw [address] at readback
      obtain ⟨final, finalRead, chained⟩ := induction nextValid event.logical.event.after readback
      refine ⟨final, finalRead, ?_⟩
      change Atomics64.LogicalChain initial (event :: labels.filterMap id) final
      refine .cons same ?_ chained
      have tag : event.logical.op = op := effect.2.1
      have mask : event.logical.mask = worker.context.registers .rsi := effect.2.2.1
      rw [tag, mask]
      simpa only [same] using effect.2.2.2.1

/-- The independent ordered mathematical contract receives one request per
actual event, with its decoded operation and mask. Metadata positions stay in
the epoch evidence; no same-endpoint lower LogicalTrace is fabricated. -/
theorem FixedCellEpoch.orderedMathematicalResult
    {identifier : Atomics64.CellId64} {cell : Atomics64.Cell}
    {before after : State} {labels : List (Option Atomics64.Event)}
    (epoch : FixedCellEpoch identifier cell before labels after) (valid : WellFormed before)
    (initial : Word)
    (read : loadQWord (toMemory before.shared.legacy.shared.resources.space) cell.address = .ok initial) :
    ∃ final, loadQWord (toMemory after.shared.legacy.shared.resources.space) cell.address = .ok final ∧
      Logical64.OrderedMathematicalResult initial
        ((labels.filterMap id).map Atomics64.Event.orderedRequest) final := by
  obtain ⟨final, finalRead, chain⟩ := epoch.chain valid initial read
  exact ⟨final, finalRead, chain.orderedMathematicalResult⟩

theorem FixedCellEpoch.join_readback
    {identifier : Atomics64.CellId64} {cell : Atomics64.Cell}
    {before after : State} {labels : List (Option Atomics64.Event)}
    (epoch : FixedCellEpoch identifier cell before labels after) (valid : WellFormed before)
    (initial : Word) (parent thread : Nat) (result : State × Context)
    (read : loadQWord (toMemory before.shared.legacy.shared.resources.space) cell.address = .ok initial)
    (joined : join after parent thread = .ok result) :
    ∃ final, loadQWord (toMemory result.1.shared.legacy.shared.resources.space) cell.address = .ok final ∧
      Logical64.OrderedMathematicalResult initial
        ((labels.filterMap id).map Atomics64.Event.orderedRequest) final := by
  obtain ⟨final, finalRead, mathematical⟩ := epoch.orderedMathematicalResult valid initial read
  exact ⟨final, by rw [(join_resources _ _ _ _ joined).1]; exact finalRead, mathematical⟩

end EDSL.OS.AtomicSetThreads64
