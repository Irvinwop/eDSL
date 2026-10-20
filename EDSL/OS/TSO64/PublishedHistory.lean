/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.CellEffects
import EDSL.OS.TSO64.ReadHistory
import EDSL.OS.TSO64.ScheduleTrace

set_option autoImplicit false

namespace EDSL.OS.TSO64.PublishedHistory
open X86

/-- The ghost writer map agrees with actual published whole-word memory for
every registered target. An arbitrary incoming map is an explicit boundary;
its selected value must agree with the actual initial read. -/
theorem schedule_read {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {offset : Nat}
    {writers : Writers} (valid : WellFormed state profile)
    (success : schedule state actions profile = .ok result)
    (target : Atomics64.CellId64) (cell : Atomics64.Cell)
    (live : state.world.cells target = some cell) (boundary : Word)
    (readBefore : loadQWord (published state.world) cell.address =
      .ok (valueOf writers target boundary)) :
    loadQWord (published result.1.world) cell.address =
      .ok (valueOf (after offset result.2 writers) target boundary) := by
  induction actions generalizing state result offset writers with
  | nil =>
    have same : (state, []) = result := Except.ok.inj success
    subst result
    exact readBefore
  | cons action rest ih =>
    obtain ⟨first, tail, stepped, following, same⟩ := schedule_cons_ok success
    have nextLive : first.1.world.cells target = some cell :=
      (congrFun (step_stable stepped).cells target).trans live
    have nextRead : loadQWord (published first.1.world) cell.address =
        .ok (valueOf (update writers offset first.2) target boundary) := by
      rw [valueOf_update]
      exact step_read valid stepped target cell live (valueOf writers target boundary) readBefore
    have finalRead := ih (offset := offset + 1) (writers := update writers offset first.2)
      (step_wellFormed valid stepped) following nextLive nextRead
    simpa only [same, after_cons] using finalRead

/-- An empty writer map names the current run's publications; the initial word
remains a separate boundary when this run has not published to the target. -/
theorem schedule_read_empty {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {offset : Nat}
    (valid : WellFormed state profile)
    (success : schedule state actions profile = .ok result)
    (target : Atomics64.CellId64) (cell : Atomics64.Cell)
    (live : state.world.cells target = some cell) (boundary : Word)
    (readBefore : loadQWord (published state.world) cell.address = .ok boundary) :
    loadQWord (published result.1.world) cell.address =
      .ok (valueOf (after offset result.2 empty) target boundary) :=
  schedule_read valid success target cell live boundary readBefore

/-- A stamped writer is tied to a real prefix and actual successful scheduler
step. Global position includes silent actions; equal-value RMWs cannot acquire
the same identity by having equal event payloads. -/
structure WriteAt (initial : State) (actions : List Action)
    (result : State × List Observation) (profile : Profile) (offset : Nat)
    (stamp : Stamp) where
  index : Nat
  observation : Observation
  before : State
  action : Action
  next : State
  position : stamp.position = offset + index
  observed : result.2[index]? = some observation
  prefixRun : schedule initial (actions.take index) profile =
    .ok (before, result.2.take index)
  actionAt : actions[index]? = some action
  stepped : step before action profile = .ok (next, observation)
  written : writeOf observation = some stamp.cause

/-- A map entry from an empty boundary names the actual newest write to that
cell in this run, with no later write to the cell in the observation suffix. -/
theorem newest_write_at {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {offset : Nat}
    {target : Atomics64.CellId64} {stamp : Stamp}
    (success : schedule state actions profile = .ok result)
    (found : after offset result.2 empty target = some stamp) :
    ∃ witness : WriteAt state actions result profile offset stamp,
      stamp.cause.cell = target ∧ NoWrites (result.2.drop (witness.index + 1)) target := by
  obtain ⟨index, observation, _bound, observed, written, position, cell, noLater⟩ :=
    after_empty_newest found
  obtain ⟨before, action, next, prefixRun, actionAt, stepped⟩ :=
    ScheduleTrace.observation_at success observed
  exact ⟨⟨index, observation, before, action, next, position, observed,
    prefixRun, actionAt, stepped, written⟩, cell, noLater⟩

/-- Actual current RAM is either the boundary word with no published writer,
or the word of the newest stamped write at a real scheduler step. -/
theorem published_read_origin {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {offset : Nat}
    (valid : WellFormed state profile)
    (success : schedule state actions profile = .ok result)
    (target : Atomics64.CellId64) (cell : Atomics64.Cell)
    (live : state.world.cells target = some cell) (boundary value : Word)
    (readBefore : loadQWord (published state.world) cell.address = .ok boundary)
    (readAfter : loadQWord (published result.1.world) cell.address = .ok value) :
    (after offset result.2 empty target = none ∧ value = boundary) ∨
      ∃ stamp, after offset result.2 empty target = some stamp ∧
        stamp.cause.value = value ∧ ∃ witness : WriteAt state actions result profile offset stamp,
          stamp.cause.cell = target ∧ NoWrites (result.2.drop (witness.index + 1)) target := by
  have memory := schedule_read_empty (offset := offset) valid success target cell live boundary readBefore
  have valueEq := Except.ok.inj (readAfter.symm.trans memory)
  cases found : after offset result.2 empty target with
  | none =>
    exact .inl ⟨rfl, by simpa only [valueOf, found] using valueEq⟩
  | some stamp =>
    obtain ⟨witness, selected, noLater⟩ := newest_write_at success found
    exact .inr ⟨stamp, rfl, by simpa only [valueOf, found] using valueEq.symm,
      witness, selected, noLater⟩

/-- Boundary or actual newest published writer for the selected persistent
cell. The initial word is not assigned an invented pre-run write event. -/
def PublishedReadFrom (state : State) (actions : List Action)
    (result : State × List Observation) (profile : Profile) (offset : Nat)
    (target : Atomics64.CellId64) (boundary value : Word) : Prop :=
  (after offset result.2 empty target = none ∧ value = boundary) ∨
    ∃ stamp, after offset result.2 empty target = some stamp ∧
      stamp.cause.value = value ∧ ∃ witness : WriteAt state actions result profile offset stamp,
        stamp.cause.cell = target ∧ NoWrites (result.2.drop (witness.index + 1)) target

/-- A real managed load either forwards the exact own pending occurrence,
reads the explicit RAM boundary, or reads the newest actual publication/RMW.
Forwarded entries keep the separate initial-queue boundary when applicable. -/
inductive ReadFrom (state : State) (actions : List Action)
    (result : State × List Observation) (profile : Profile) (offset tid : Nat)
    (worker : Worker) (reference : Queue.ManagedRef) (target : Atomics64.CellId64)
    (boundary value : Word) : Prop where
  | forwarded (position : StoreBuffer.Mixed.QWordOrigin) (writer : Queue.ManagedRef)
      (occurrence : Nat)
      (newest : StoreBuffer.Mixed.newestQWord (payload worker.pending)
        reference.cell.address = some position)
      (entry : worker.pending[position.index]? = some (.managed writer value occurrence))
      (origin : StoreHistory.Origin state actions result profile tid (.managed writer value occurrence)) :
      ReadFrom state actions result profile offset tid worker reference target boundary value
  | published
      (absent : StoreBuffer.Mixed.newestQWord (payload worker.pending) reference.cell.address = none)
      (origin : PublishedReadFrom state actions result profile offset target boundary value) :
      ReadFrom state actions result profile offset tid worker reference target boundary value

/-- Resource-derived whole-word forwarding and the actual published-writer
history meet at the real local load. The target's original descriptor is
transported through current cell metadata, never through equality of values. -/
theorem managed_read_origin {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {offset tid : Nat}
    {worker : Worker} {reference : Queue.ManagedRef} {target : Atomics64.CellId64}
    {cell : Atomics64.Cell} {boundary value : Word}
    (valid : WellFormed state profile) (sequenced : Sequenced state)
    (success : schedule state actions profile = .ok result)
    (live : state.world.cells target = some cell)
    (readBefore : loadQWord (published state.world) cell.address = .ok boundary)
    (workerLive : result.1.workers[tid]? = some worker)
    (current : Queue.Current result.1.world worker.resources reference)
    (selected : reference.handle.cell = target)
    (loaded : loadQWord (localCPU result.1 worker).memory reference.cell.address = .ok value) :
    ReadFrom state actions result profile offset tid worker reference target boundary value := by
  have finalValid := schedule_wellFormed valid success
  have source := managed_read_source finalValid
    (finalValid.2 worker (List.mem_of_getElem? workerLive))
    (schedule_sequenced sequenced success worker (List.mem_of_getElem? workerLive)) current loaded
  cases source with
  | forwarded position writer occurrence newest entry payload address writerCurrent below =>
    exact .forwarded position writer occurrence newest entry
      (StoreHistory.schedule_pending_origin success
        ⟨worker, workerLive, List.mem_of_getElem? entry⟩)
  | published absent read =>
    have sameLive : result.1.world.cells target = some cell :=
      (congrFun (ScheduleTrace.cells success) target).trans live
    have linked : result.1.world.cells target = some reference.cell := by
      simpa only [selected] using current.cell
    have cellEq : reference.cell = cell := Option.some.inj (linked.symm.trans sameLive)
    have readAfter : loadQWord (published result.1.world) cell.address = .ok value := by
      simpa only [cellEq] using read
    exact .published absent (published_read_origin valid success target cell live boundary value readBefore readAfter)

/-- A decoded managed MOV64 after an actual prefix run exposes its complete
read origin and exact destination installation. Instruction effects may be
extracted directly from step success using `issue_ordinary_effect`. -/
theorem loadMem64_origin {state : State} {actions : List Action}
    {priorRun : State × List Observation} {profile : Profile} {offset tid : Nat}
    {worker : Worker} {reference : Queue.ManagedRef} {target : Atomics64.CellId64}
    {cell : Atomics64.Cell} {boundary : Word}
    {destination : Register} {address : Sequential.Address} {af : Bool}
    {result : State × Observation}
    (valid : WellFormed state profile) (sequenced : Sequenced state)
    (success : schedule state actions profile = .ok priorRun)
    (live : state.world.cells target = some cell)
    (readBefore : loadQWord (published state.world) cell.address = .ok boundary)
    (workerLive : priorRun.1.workers[tid]? = some worker)
    (current : Queue.Current priorRun.1.world worker.resources reference)
    (selected : reference.handle.cell = target)
    (operand : reference.cell.address = address.eval (localCPU priorRun.1 worker))
    (effect : OrdinaryEffect priorRun.1 tid worker (.loadMem64 destination address) af result profile) :
    ∃ value, ReadFrom state actions priorRun profile offset tid worker reference target boundary value ∧
      result = (install priorRun.1 tid priorRun.1.world
        { worker with context := .ofCPU (
          { (localCPU priorRun.1 worker).writeRegister destination value with
            rip := (localCPU priorRun.1 worker).rip +
              BitVec.ofNat 64 (Sequential.Instruction.loadMem64 destination address).length }) },
        .ordinary tid) := by
  obtain ⟨value, loaded, _source, installed⟩ :=
    effect.managed_loadMem64 (schedule_wellFormed valid success) workerLive current operand
  exact ⟨value, managed_read_origin valid sequenced success live readBefore workerLive
    current selected loaded, installed⟩
private theorem buffered_observation {observation : Observation} {tid occurrence : Nat}
    {reference : Queue.ManagedRef} {value : Word}
    (written : writeOf observation = some (.buffered tid reference value occurrence)) :
    observation = .drained tid (.managed reference value occurrence) := by
  cases observation with
  | ordinary => simp [writeOf] at written
  | returned => simp [writeOf] at written
  | blocked => simp [writeOf] at written
  | rmw => simp [writeOf] at written
  | drained actual entry =>
    cases entry with
    | ordinary => simp [writeOf] at written
    | managed other payload number =>
      have same : WriteCause.buffered actual other payload number =
          .buffered tid reference value occurrence := Option.some.inj written
      cases same
      rfl

private theorem drained_action {state next : State} {action : Action} {profile : Profile}
    {tid : Nat} {entry : Pending}
    (success : step state action profile = .ok (next, .drained tid entry)) : action = .drain tid := by
  cases step_origin success with
  | ordinary live running code caller fetched effect =>
    cases effect with
    | intro supported bounds decoded reads queue executed finish => cases finish
  | drained => rfl

/-- A buffered last-writer stamp retains the exact initial-queue or actual
instruction-issue origin of the entry published at its real prefix position.
It does not invent a prior issue for an arbitrary nonempty initial FIFO. -/
theorem WriteAt.buffered_origin {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {offset position tid occurrence : Nat}
    {reference : Queue.ManagedRef} {value : Word}
    (witness : WriteAt state actions result profile offset
      ⟨position, .buffered tid reference value occurrence⟩) :
    StoreHistory.Origin state (actions.take witness.index)
      (witness.before, result.2.take witness.index) profile tid (.managed reference value occurrence) := by
  have observed := buffered_observation witness.written
  have stepped : step witness.before witness.action profile =
      .ok (witness.next, .drained tid (.managed reference value occurrence)) := by
    simpa only [observed] using witness.stepped
  have action := drained_action stepped
  apply StoreHistory.drain_after_schedule_origin witness.prefixRun
  simpa only [action, step] using stepped
end EDSL.OS.TSO64.PublishedHistory
