/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO.CounterHistory
import EDSL.Audit

namespace EDSL.OS.TSO.Counter
open X86

/-- Excludes interference with the counter cell without suppressing unrelated
buffered writes or unrelated RMWs. A retiring locked instruction on the cell
must be the actually decoded fetch-add. A different RMW footprint must be
byte-disjoint; unequal starting addresses alone would not suffice. -/
def IssuePermitted (address : Word) (state : State) (identifier : Nat) : Prop :=
  ∀ worker instruction, state.workers[identifier]? = some worker →
    decodeAt (sharedState state worker) = .ok instruction →
    locked instruction = true → worker.buffer = [] →
    (worker.context.registers .rdi = address ∧ instruction = .fetchAddEaxRdi) ∨
      DWordDisjoint (worker.context.registers .rdi) address 4

/-- Pending publication may not overwrite any byte of the counter cell. -/
def DrainPermitted (address : Word) (state : State) (identifier : Nat) : Prop :=
  ∀ worker head tail, state.workers[identifier]? = some worker →
    worker.buffer = head :: tail → DWordDisjoint head.address address 4

def Permitted (address : Word) (state : State) : Action → Prop
  | .issue identifier => IssuePermitted address state identifier
  | .drain identifier => DrainPermitted address state identifier

/-- State-dependent policy for every successful prefix. This is an explicit
noninterference obligation, not a premise assuming a desired final value. -/
def SchedulePermitted (address : Word) (state : State) : List Action → Prop
  | [] => True
  | action :: actions => Permitted address state action ∧
      ∀ result, TSO.step state action = .ok result → SchedulePermitted address result.1 actions

inductive Effect (address : Word) (before : State) (action : Action)
    (result : State × Observation) : Prop where
  | quiet (unchanged : loadDWord result.1.memory address = loadDWord before.memory address)
      (unobserved : eventsAt address [result.2] = []) : Effect address before action result
  | addition (operation : Operation) (origin : Origin address before action result operation) :
      Effect address before action result

private theorem disjoint_ne {write address : Word} (disjoint : DWordDisjoint write address 4) :
    write ≠ address := by
  intro same
  have outside := disjoint 0 (by decide)
  simp [same] at outside

/-- Inversion of actual scheduler success, not execution of a guessed
instruction: the policy discharges just the interfering cases. -/
theorem step_effect {address : Word} {before : State} {action : Action}
    {result : State × Observation} (permitted : Permitted address before action)
    (success : TSO.step before action = .ok result) : Effect address before action result := by
  cases action with
  | issue identifier =>
    obtain ⟨worker, instruction, live, returned, decoded, issued, effect⟩ :=
      issue_effect _ _ _ success
    cases effect with
    | queued pending aligned data executed writable exactOutput =>
      exact .quiet rfl rfl
    | ordinary pending unlocked loads executed memory => exact .quiet rfl rfl
    | returned pending unlocked instructionEq executed memory => exact .quiet rfl rfl
    | blocked pending classified nonempty => exact .quiet rfl rfl
    | @atomic event output pending classified empty data architectural transition eventAddress accumulator =>
      rcases permitted worker instruction live decoded classified empty with target | disjoint
      · rcases target with ⟨target, rfl⟩
        exact .addition ⟨identifier, (worker.context.registers .rax).setWidth 32, event.before⟩
          ⟨worker, event, output, rfl, live, returned, decoded, empty, architectural,
            rfl, rfl, eventAddress.trans target, rfl, rfl⟩
      · have outside : DWordDisjoint event.address address 4 := by
          rw [eventAddress]
          exact disjoint
        refine .quiet ?_ ?_
        · change loadDWord output.memory address = _
          rw [transition.2.2.2]
          exact loadDWord_congr _ _ _ (writeDWord_agrees _ _ _ _ _ outside)
        · simp [eventsAt, disjoint_ne outside]
  | drain identifier =>
    obtain ⟨worker, head, tail, live, buffer, allowed, written, observed⟩ := drain_memory _ _ _ success
    have outside := permitted worker head tail live buffer
    refine .quiet ?_ ?_
    · rw [written]
      exact loadDWord_congr _ _ _ (writeDWord_agrees _ _ _ _ _ outside)
    · rw [observed]
      rfl

/-- A chronological history plus independent sequential semantics for every
successful finite schedule satisfying the explicit footprint policy. Ordinary
TSO buffering remains active. No fairness or whole-call atomicity is assumed. -/
theorem schedule_linearization {address : Word} {before : State} {actions : List Action}
    {result : State × List Observation} {initialValue : BitVec 32}
    (read : loadDWord before.memory address = .ok initialValue)
    (permitted : SchedulePermitted address before actions)
    (success : TSO.schedule before actions = .ok result) :
    ∃ finalValue operations,
      loadDWord result.1.memory address = .ok finalValue ∧
      Sequential initialValue operations finalValue ∧
      MachineHistory address before actions result.2 result.1 operations ∧
      operations.map (Operation.event address) = eventsAt address result.2 ∧
      finalValue = initialValue + totalDelta operations := by
  induction actions generalizing before result initialValue with
  | nil =>
    simp only [TSO.schedule, Except.ok.injEq] at success
    cases success
    exact ⟨initialValue, [], read, .nil _, .nil, rfl, by simp [totalDelta]⟩
  | cons action actions ih =>
    obtain ⟨head, tail, first, following, same⟩ := schedule_cons_ok _ _ _ _ success
    have allowedTail := permitted.2 head first
    cases step_effect permitted.1 first with
    | quiet unchanged unobserved =>
      obtain ⟨finalValue, operations, finalRead, sequential, history, observed, total⟩ :=
        ih (unchanged.trans read) allowedTail following
      rw [same]
      have whole : MachineHistory address before (action :: actions) (head.2 :: tail.2)
          tail.1 operations := .quiet first unchanged unobserved history
      exact ⟨finalValue, operations, finalRead, sequential, whole, whole.events, total⟩
    | addition operation origin =>
      have effects := origin.effects
      have returned : operation.result = initialValue := by
        rw [read] at effects
        exact Except.ok.inj effects.1.symm
      have nextRead : loadDWord head.1.memory address = .ok (initialValue + operation.delta) := by
        rw [← returned]
        exact effects.2.1
      obtain ⟨finalValue, operations, finalRead, sequential, history, observed, total⟩ :=
        ih nextRead allowedTail following
      rw [same]
      have whole : MachineHistory address before (action :: actions) (head.2 :: tail.2)
          tail.1 (operation :: operations) := .addition first origin history
      have seq : Sequential initialValue (operation :: operations) finalValue :=
        .cons returned rfl sequential
      exact ⟨finalValue, operation :: operations, finalRead, seq, whole, whole.events, seq.total⟩

end EDSL.OS.TSO.Counter

#audit_edsl
