/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Machine
import EDSL.X86.Sequential.Multiply
import EDSL.X86.Sequential.ShiftRight32

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.X86.Sequential

/-- A register-only vector operation supplies its complete choice dependence
and memory frame once. Shared execution, read provenance and policy consumers
use these laws without enumerating the registered instruction families. -/
structure RegisterChoiceEffect (instruction : Instruction) where
  active : State → List StatusFlag
  apply : State → FlagChoices → State
  noReads : ∀ state, instruction.operandReads state = []
  memory : ∀ state choices, (apply state choices).memory = state.memory
  agreement : ∀ state left right,
    FlagChoices.Agreement (active state) left right → apply state left = apply state right

/-- Production registration for vector-only, register-local operations. A new
family must prove the shared effect and inactive-choice laws at this boundary. -/
def Instruction.registerChoiceEffect :
    (instruction : Instruction) → Option (RegisterChoiceEffect instruction)
  | .imulReg64 destination source => some {
      active := fun _ => [.pf, .af, .zf, .sf]
      apply := fun state choices => imulReg64State state destination source choices
      noReads := fun _ => rfl
      memory := fun state choices => imulReg64State_memory state destination source choices
      agreement := fun state left right agree =>
        imulReg64State_eq_of_agreement state destination source left right agree }
  | .shiftRightImm32 operation destination immediate prefixed => some {
      active := fun _ => shiftRightUndefinedFlags32 immediate
      apply := fun state choices =>
        shiftRightImm32State state operation destination immediate prefixed choices
      noReads := fun _ => rfl
      memory := fun state choices =>
        shiftRightImm32State_memory state operation destination immediate prefixed choices
      agreement := fun state left right agree =>
        shiftRightImm32State_eq_of_agreement state operation destination immediate prefixed
          left right agree }
  | _ => none

/-- The Bool profile excludes every registered vector-only operation. -/
def Instruction.boolChoiceProfile (instruction : Instruction) : Bool :=
  match instruction.registerChoiceEffect with
  | none => true
  | some _ => false

/-- This predicate inspects actual decoding, not a caller's proposed opcode.
Failed decoding satisfies the predicate because both interfaces retain the error. -/
def BoolChoiceProfile (state : State) : Prop :=
  ∀ instruction, decodeAt state = .ok instruction → instruction.boolChoiceProfile = true

/-- Vector-only effects declare all active bits. Other instructions retain
the original state-dependent single-bit metadata. -/
def Instruction.undefinedFlags (instruction : Instruction) (state : State) : List StatusFlag :=
  match instruction.registerChoiceEffect with
  | some effect => effect.active state
  | none => match instruction.choiceFlag state with
    | none => []
    | some .af => [.af]
    | some .of => [.of]

theorem Instruction.undefinedFlags_of_boolChoiceProfile (instruction : Instruction) (state : State)
    (single : instruction.boolChoiceProfile = true) :
    instruction.undefinedFlags state = match instruction.choiceFlag state with
      | none => [] | some .af => [.af] | some .of => [.of] := by
  cases registered : instruction.registerChoiceEffect with
  | none => simp only [Instruction.undefinedFlags, registered]
  | some effect => simp [Instruction.boolChoiceProfile, registered] at single

/-- Projection used only by the single-bit instruction branches. Defined
instructions ignore the false placeholder; vector-only operations bypass it. -/
def Instruction.selectedChoice (instruction : Instruction) (state : State)
    (choices : FlagChoices) : Bool :=
  match instruction.choiceFlag state with
  | none => false
  | some .af => choices.get .af
  | some .of => choices.get .of

/-- Full vector execution uses the registered complete transformer, including
independently undefined bits. Other instructions keep their prior effects. -/
def executeWith (state : State) (instruction : Instruction) (choices : FlagChoices) :
    Except Error Observation :=
  match instruction.registerChoiceEffect with
  | some effect => .ok ⟨.next (effect.apply state choices), []⟩
  | none => execute state instruction (instruction.selectedChoice state choices)

def stepWith (choices : FlagChoices) (state : State) : Except Error Observation := do
  let instruction ← decodeAt state
  executeWith state instruction choices

theorem executeWith_eq_execute (state : State) (instruction : Instruction) (choices : FlagChoices)
    (single : instruction.boolChoiceProfile = true) :
    executeWith state instruction choices =
      execute state instruction (instruction.selectedChoice state choices) := by
  cases registered : instruction.registerChoiceEffect with
  | none => simp only [executeWith, registered]
  | some effect => simp [Instruction.boolChoiceProfile, registered] at single

theorem stepWith_eq_executeWith {state : State} {instruction : Instruction}
    (choices : FlagChoices) (decoded : decodeAt state = .ok instruction) :
    stepWith choices state = executeWith state instruction choices := by
  simp only [stepWith, decoded, ok_bind]

theorem Instruction.selectedChoice_eq_of_agreement (instruction : Instruction) (state : State)
    (left right : FlagChoices) (single : instruction.boolChoiceProfile = true)
    (agree : FlagChoices.Agreement (instruction.undefinedFlags state) left right) :
    instruction.selectedChoice state left = instruction.selectedChoice state right := by
  cases selected : instruction.choiceFlag state with
  | none => simp only [Instruction.selectedChoice, selected]
  | some flag =>
    cases flag with
    | af =>
      have same := agree .af (by simp [instruction.undefinedFlags_of_boolChoiceProfile state single, selected])
      simpa only [Instruction.selectedChoice, selected] using same
    | of =>
      have same := agree .of (by simp [instruction.undefinedFlags_of_boolChoiceProfile state single, selected])
      simpa only [Instruction.selectedChoice, selected] using same

/-- Inactive-bit independence covers the entire success/error observation,
including all successor flags, register values and memory effects. -/
theorem executeWith_congr (state : State) (instruction : Instruction) (left right : FlagChoices)
    (agree : FlagChoices.Agreement (instruction.undefinedFlags state) left right) :
    executeWith state instruction left = executeWith state instruction right := by
  cases registered : instruction.registerChoiceEffect with
  | none =>
    have single : instruction.boolChoiceProfile = true := by
      simp only [Instruction.boolChoiceProfile, registered]
    rw [executeWith_eq_execute state instruction left single,
      executeWith_eq_execute state instruction right single,
      instruction.selectedChoice_eq_of_agreement state left right single agree]
  | some effect =>
    simp only [Instruction.undefinedFlags, registered] at agree
    simp only [executeWith, registered, effect.agreement state left right agree]

theorem stepWith_congr {state : State} {instruction : Instruction} (left right : FlagChoices)
    (decoded : decodeAt state = .ok instruction)
    (agree : FlagChoices.Agreement (instruction.undefinedFlags state) left right) :
    stepWith left state = stepWith right state := by
  rw [stepWith_eq_executeWith left decoded, stepWith_eq_executeWith right decoded]
  exact executeWith_congr state instruction left right agree

theorem executeWith_invariant (state : State) (instruction : Instruction)
    (predicate : Except Error Observation → Prop) :
    FlagChoices.Invariant (instruction.undefinedFlags state)
      (fun choices => predicate (executeWith state instruction choices)) := by
  intro left right agree
  change predicate (executeWith state instruction left) ↔ predicate (executeWith state instruction right)
  rw [executeWith_congr state instruction left right agree]

/-- Uniform vectors recover Bool semantics only in the recorded Bool profile.
They do not cover independently undefined bits in vector-only operations. -/
theorem executeWith_uniform (state : State) (instruction : Instruction) (value : Bool)
    (single : instruction.boolChoiceProfile = true) :
    executeWith state instruction (FlagChoices.uniform value) = execute state instruction value := by
  rw [executeWith_eq_execute state instruction (FlagChoices.uniform value) single]
  cases selected : instruction.choiceFlag state with
  | none =>
    simp only [Instruction.selectedChoice, selected]
    exact execute_choice_independent state instruction false value selected
  | some flag =>
    cases flag <;> simp only [Instruction.selectedChoice, selected, FlagChoices.get_uniform]

theorem stepWith_uniform (state : State) (value : Bool) (single : BoolChoiceProfile state) :
    stepWith (FlagChoices.uniform value) state = step value state := by
  cases decoded : decodeAt state with
  | error fault => simp only [stepWith, step, decoded, error_bind]
  | ok instruction =>
    simp only [stepWith, step, decoded, ok_bind]
    exact executeWith_uniform state instruction value (single instruction decoded)

theorem executeWith_exists_bool (state : State) (instruction : Instruction) (choices : FlagChoices)
    (single : instruction.boolChoiceProfile = true) :
    ∃ value : Bool, executeWith state instruction choices = execute state instruction value :=
  ⟨instruction.selectedChoice state choices, executeWith_eq_execute state instruction choices single⟩

theorem execute_existsWith (state : State) (instruction : Instruction) (value : Bool)
    (single : instruction.boolChoiceProfile = true) :
    ∃ choices : FlagChoices, executeWith state instruction choices = execute state instruction value :=
  ⟨FlagChoices.uniform value, executeWith_uniform state instruction value single⟩

theorem stepWith_exists_bool (state : State) (choices : FlagChoices) (single : BoolChoiceProfile state) :
    ∃ value : Bool, stepWith choices state = step value state := by
  cases decoded : decodeAt state with
  | error fault => exact ⟨false, by simp only [stepWith, step, decoded, error_bind]⟩
  | ok instruction =>
    refine ⟨instruction.selectedChoice state choices, ?_⟩
    simp only [stepWith, step, decoded, ok_bind]
    exact executeWith_eq_execute state instruction choices (single instruction decoded)

theorem step_existsWith (state : State) (value : Bool) (single : BoolChoiceProfile state) :
    ∃ choices : FlagChoices, stepWith choices state = step value state :=
  ⟨FlagChoices.uniform value, stepWith_uniform state value single⟩

/-- Successful Bool execution rules out the rejected multi-flag opcode. -/
theorem execute_boolChoiceProfile_of_success {state : State} {instruction : Instruction}
    {value : Bool} {observation : Observation}
    (success : execute state instruction value = .ok observation) :
    instruction.boolChoiceProfile = true := by
  cases instruction <;> first | rfl | simp [execute] at success

theorem boolChoiceProfile_of_step_success {state : State} {value : Bool} {observation : Observation}
    (success : step value state = .ok observation) : BoolChoiceProfile state := by
  intro instruction decoded
  rw [step_eq_execute value decoded] at success
  exact execute_boolChoiceProfile_of_success success

/-- A single shared effect split is sufficient for memory-policy consumers.
The vector branch carries full memory equality and the exact empty read trace. -/
theorem executeWith_effect (state : State) (instruction : Instruction) (choices : FlagChoices) :
    instruction.boolChoiceProfile = true ∨
      ∃ after, executeWith state instruction choices = .ok ⟨.next after, []⟩ ∧
        instruction.operandReads state = [] ∧ after.memory = state.memory := by
  cases registered : instruction.registerChoiceEffect with
  | none => exact Or.inl (by simp only [Instruction.boolChoiceProfile, registered])
  | some effect =>
    exact Or.inr ⟨effect.apply state choices, by simp only [executeWith, registered],
      effect.noReads state, effect.memory state choices⟩

theorem executeWith_reads {state : State} {instruction : Instruction} {choices : FlagChoices}
    {observation : Observation} (success : executeWith state instruction choices = .ok observation) :
    observation.reads = instruction.operandReads state := by
  rcases executeWith_effect state instruction choices with single | ⟨after, actual, reads, _⟩
  · rw [executeWith_eq_execute state instruction choices single] at success
    exact execute_reads success
  · rw [actual] at success
    cases success
    exact reads.symm

theorem executeWith_reads_succeed {state : State} {instruction : Instruction} {choices : FlagChoices}
    {observation : Observation} (success : executeWith state instruction choices = .ok observation) :
    ∀ read ∈ observation.reads, OperandReadSucceeds state read := by
  rcases executeWith_effect state instruction choices with single | ⟨after, actual, _, _⟩
  · rw [executeWith_eq_execute state instruction choices single] at success
    exact execute_reads_succeed success
  · rw [actual] at success
    cases success
    intro read member
    cases member

theorem stepWith_reads_succeed {state : State} {choices : FlagChoices}
    {observation : Observation} (success : stepWith choices state = .ok observation) :
    ∀ read ∈ observation.reads, OperandReadSucceeds state read := by
  cases decoded : decodeAt state with
  | error fault => simp only [stepWith, decoded, error_bind, reduceCtorEq] at success
  | ok instruction =>
    have actual : executeWith state instruction choices = .ok observation := by
      simpa only [stepWith, decoded, ok_bind] using success
    exact executeWith_reads_succeed actual

end EDSL.X86.Sequential
