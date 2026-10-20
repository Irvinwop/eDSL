/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO.Counter
import EDSL.Audit

namespace EDSL.OS.TSO.Counter
open X86

/-- Finite byte-footprint check, including partial overlap and modular
addresses. Checking only inequality of starting addresses would be unsound. -/
def checkDisjoint (write address : Word) : Bool :=
  decide (4 ≤ (address - write).toNat ∧
    4 ≤ ((address + 1) - write).toNat ∧
    4 ≤ ((address + 2) - write).toNat ∧
    4 ≤ ((address + 3) - write).toNat)

theorem checkDisjoint_sound {write address : Word}
    (checked : checkDisjoint write address = true) : DWordDisjoint write address 4 := by
  have bounds := of_decide_eq_true checked
  intro offset bound
  have cases : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · simpa using bounds.1
  · exact bounds.2.1
  · exact bounds.2.2.1
  · exact bounds.2.2.2

/-- Fail-closed executable discharge of one step's explicit interference
policy. Actual scheduling still performs all ordinary architectural checks. -/
def checkPermitted (address : Word) (state : State) : Action → Bool
  | .issue identifier =>
    match state.workers[identifier]? with
    | none => false
    | some worker =>
      match decodeAt (sharedState state worker) with
      | .error _ => false
      | .ok instruction =>
        if locked instruction && worker.buffer.isEmpty then
          decide (worker.context.registers .rdi = address ∧ instruction = .fetchAddEaxRdi) ||
            checkDisjoint (worker.context.registers .rdi) address
        else true
  | .drain identifier =>
    match state.workers[identifier]? with
    | none => false
    | some worker =>
      match worker.buffer with
      | [] => false
      | head :: _ => checkDisjoint head.address address

theorem checkPermitted_sound {address : Word} {state : State} {action : Action}
    (checked : checkPermitted address state action = true) : Permitted address state action := by
  cases action with
  | issue identifier =>
    intro worker instruction live decoded classified empty
    simp only [checkPermitted, live, decoded, classified, empty, List.isEmpty_nil,
      Bool.and_self, ↓reduceIte] at checked
    rcases Bool.or_eq_true_iff.mp checked with target | disjoint
    · exact .inl (of_decide_eq_true target)
    · exact .inr (checkDisjoint_sound disjoint)
  | drain identifier =>
    intro worker head tail live buffer
    simp only [checkPermitted, live, buffer] at checked
    exact checkDisjoint_sound checked

/-- Executes the real scheduler once per selected action while checking the
counter policy against each current state. This checker does not replace the
TSO semantics with a separate counter runner. -/
def checkSchedule (address : Word) (state : State) : List Action → Bool
  | [] => true
  | action :: actions => checkPermitted address state action &&
      match TSO.step state action with
      | .error _ => false
      | .ok result => checkSchedule address result.1 actions

theorem checkSchedule_sound {address : Word} {state : State} {actions : List Action}
    (checked : checkSchedule address state actions = true) :
    ∃ result, TSO.schedule state actions = .ok result ∧ SchedulePermitted address state actions := by
  induction actions generalizing state with
  | nil => exact ⟨(state, []), rfl, trivial⟩
  | cons action actions ih =>
    have both := Bool.and_eq_true_iff.mp checked
    cases first : TSO.step state action with
    | error fault => simp [checkSchedule, first] at checked
    | ok head =>
      have tailChecked : checkSchedule address head.1 actions = true := by
        simpa [first] using both.2
      obtain ⟨tail, following, permitted⟩ := ih tailChecked
      refine ⟨(tail.1, head.2 :: tail.2), ?_, checkPermitted_sound both.1, ?_⟩
      · simp [TSO.schedule, first, following]
      · intro result transition
        have same : result = head := Except.ok.inj (transition.symm.trans first)
        cases same
        exact permitted

/-- Kernel checking one Boolean supplies both actual successful scheduling and
its independent sequential fetch-add certificate. The result is only for this
operational model and the explicit noninterference profile. -/
theorem checked_linearization {address : Word} {before : State} {actions : List Action}
    {initialValue : BitVec 32} (read : loadDWord before.memory address = .ok initialValue)
    (checked : checkSchedule address before actions = true) :
    ∃ result finalValue operations,
      TSO.schedule before actions = .ok result ∧
      loadDWord result.1.memory address = .ok finalValue ∧
      Sequential initialValue operations finalValue ∧
      MachineHistory address before actions result.2 result.1 operations ∧
      operations.map (Operation.event address) = eventsAt address result.2 ∧
      finalValue = initialValue + totalDelta operations := by
  obtain ⟨result, success, permitted⟩ := checkSchedule_sound checked
  obtain ⟨finalValue, operations, finalRead, sequential, history, observed, total⟩ :=
    schedule_linearization read permitted success
  exact ⟨result, finalValue, operations, success, finalRead, sequential, history, observed, total⟩

end EDSL.OS.TSO.Counter

#audit_edsl
