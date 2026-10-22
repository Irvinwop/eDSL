/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Machine
import EDSL.X86.Sequential.Multiply

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.X86.Sequential

/-- The Bool executor rejects instructions needing several undefined bits. -/
def Instruction.boolChoiceProfile : Instruction → Bool
  | .imulReg64 _ _ => false
  | _ => true

theorem Instruction.boolChoiceProfile_or_imul (instruction : Instruction) :
    instruction.boolChoiceProfile = true ∨
      ∃ destination source, instruction = .imulReg64 destination source := by
  cases instruction <;> first
    | exact Or.inl rfl
    | exact Or.inr ⟨_, _, rfl⟩

/-- This predicate inspects actual decoding, not a caller's proposed opcode.
Failed decoding satisfies the predicate because both interfaces retain the error. -/
def BoolChoiceProfile (state : State) : Prop :=
  ∀ instruction, decodeAt state = .ok instruction → instruction.boolChoiceProfile = true

/-- IMUL has four independent undefined bits. All other supported instructions
retain the original state-dependent AF/OF metadata. -/
def Instruction.undefinedFlags (instruction : Instruction) (state : State) : List StatusFlag :=
  match instruction with
  | .imulReg64 _ _ => [.pf, .af, .zf, .sf]
  | _ => match instruction.choiceFlag state with
    | none => []
    | some .af => [.af]
    | some .of => [.of]

theorem Instruction.undefinedFlags_of_boolChoiceProfile (instruction : Instruction) (state : State)
    (single : instruction.boolChoiceProfile = true) :
    instruction.undefinedFlags state = match instruction.choiceFlag state with
      | none => [] | some .af => [.af] | some .of => [.of] := by
  cases instruction <;> first | rfl | cases single

/-- Projection used only by the single-bit instruction branches. Defined
instructions ignore the false placeholder; IMUL never uses this projection. -/
def Instruction.selectedChoice (instruction : Instruction) (state : State)
    (choices : FlagChoices) : Bool :=
  match instruction.choiceFlag state with
  | none => false
  | some .af => choices.get .af
  | some .of => choices.get .of

/-- Full vector semantics. IMUL captures both old operands, writes the low64
product, computes CF/OF from signed overflow, and independently chooses the four
undefined flags. Existing instructions retain their complete prior effects. -/
def executeWith (state : State) (instruction : Instruction) (choices : FlagChoices) :
    Except Error Observation :=
  match instruction with
  | .imulReg64 destination source => .ok ⟨.next (imulReg64State state destination source choices), []⟩
  | _ => execute state instruction (instruction.selectedChoice state choices)

def stepWith (choices : FlagChoices) (state : State) : Except Error Observation := do
  let instruction ← decodeAt state
  executeWith state instruction choices

theorem executeWith_eq_execute (state : State) (instruction : Instruction) (choices : FlagChoices)
    (single : instruction.boolChoiceProfile = true) :
    executeWith state instruction choices =
      execute state instruction (instruction.selectedChoice state choices) := by
  cases instruction <;> first | rfl | cases single

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
  rcases instruction.boolChoiceProfile_or_imul with single | ⟨destination, source, rfl⟩
  · rw [executeWith_eq_execute state instruction left single,
      executeWith_eq_execute state instruction right single,
      instruction.selectedChoice_eq_of_agreement state left right single agree]
  · exact congrArg (fun after => (Except.ok ⟨.next after, []⟩ : Except Error Observation))
      (imulReg64State_eq_of_agreement state destination source left right agree)

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
They are not a complete model of IMUL's independently undefined flags. -/
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

theorem executeWith_reads {state : State} {instruction : Instruction} {choices : FlagChoices}
    {observation : Observation} (success : executeWith state instruction choices = .ok observation) :
    observation.reads = instruction.operandReads state := by
  rcases instruction.boolChoiceProfile_or_imul with single | ⟨destination, source, rfl⟩
  · rw [executeWith_eq_execute state instruction choices single] at success
    exact execute_reads success
  · cases success
    rfl

theorem executeWith_reads_succeed {state : State} {instruction : Instruction} {choices : FlagChoices}
    {observation : Observation} (success : executeWith state instruction choices = .ok observation) :
    ∀ read ∈ observation.reads, OperandReadSucceeds state read := by
  rcases instruction.boolChoiceProfile_or_imul with single | ⟨destination, source, rfl⟩
  · rw [executeWith_eq_execute state instruction choices single] at success
    exact execute_reads_succeed success
  · cases success
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
