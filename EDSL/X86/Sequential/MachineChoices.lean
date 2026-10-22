/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Machine
import EDSL.X86.Sequential.FlagChoices

set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.X86.Sequential

/-- Undefined-bit metadata for the existing single-choice instruction profile.
This adapter does not add opcodes or claim support for multi-flag instructions.
ROL's metadata depends on its actual pre-instruction masked count. -/
def Instruction.undefinedFlags (instruction : Instruction) (state : State) : List StatusFlag :=
  match instruction.choiceFlag state with
  | none => []
  | some .af => [.af]
  | some .of => [.of]

/-- Select the bit named by the existing production semantics. A defined
instruction uses an arbitrary false placeholder; its observation is independent
of that placeholder by `execute_choice_independent`. -/
def Instruction.selectedChoice (instruction : Instruction) (state : State)
    (choices : FlagChoices) : Bool :=
  match instruction.choiceFlag state with
  | none => false
  | some .af => choices.get .af
  | some .of => choices.get .of

/-- Additive vector interface to the current production instruction semantics.
Every existing register, memory, permission, flag and error effect is retained. -/
def executeWith (state : State) (instruction : Instruction) (choices : FlagChoices) :
    Except Error Observation :=
  execute state instruction (instruction.selectedChoice state choices)

/-- Decode the actual current executable bytes before selecting their choice.
A caller-supplied instruction cannot override the current instruction stream. -/
def stepWith (choices : FlagChoices) (state : State) : Except Error Observation := do
  let instruction ← decodeAt state
  executeWith state instruction choices

theorem stepWith_eq_executeWith {state : State} {instruction : Instruction}
    (choices : FlagChoices) (decoded : decodeAt state = .ok instruction) :
    stepWith choices state = executeWith state instruction choices := by
  simp only [stepWith, decoded, ok_bind]

/-- Agreement on active bits is sufficient to select the same Bool in the
existing profile. No relation between inactive status-bit choices is needed. -/
theorem Instruction.selectedChoice_eq_of_agreement (instruction : Instruction) (state : State)
    (left right : FlagChoices)
    (agree : FlagChoices.Agreement (instruction.undefinedFlags state) left right) :
    instruction.selectedChoice state left = instruction.selectedChoice state right := by
  cases selected : instruction.choiceFlag state with
  | none => simp only [Instruction.selectedChoice, selected]
  | some flag =>
    cases flag with
    | af =>
      have same := agree .af (by simp [Instruction.undefinedFlags, selected])
      simpa only [Instruction.selectedChoice, selected] using same
    | of =>
      have same := agree .of (by simp [Instruction.undefinedFlags, selected])
      simpa only [Instruction.selectedChoice, selected] using same

/-- The entire success or failure observation depends only on active choices.
This includes exact read footprints and the complete successor state. -/
theorem executeWith_congr (state : State) (instruction : Instruction) (left right : FlagChoices)
    (agree : FlagChoices.Agreement (instruction.undefinedFlags state) left right) :
    executeWith state instruction left = executeWith state instruction right := by
  unfold executeWith
  rw [instruction.selectedChoice_eq_of_agreement state left right agree]

/-- Actual decoded steps inherit complete-observation independence. -/
theorem stepWith_congr {state : State} {instruction : Instruction} (left right : FlagChoices)
    (decoded : decodeAt state = .ok instruction)
    (agree : FlagChoices.Agreement (instruction.undefinedFlags state) left right) :
    stepWith left state = stepWith right state := by
  rw [stepWith_eq_executeWith left decoded, stepWith_eq_executeWith right decoded]
  exact executeWith_congr state instruction left right agree

/-- Any predicate of the complete production observation has the inactive-bit
independence required by finite representative checking. -/
theorem executeWith_invariant (state : State) (instruction : Instruction)
    (predicate : Except Error Observation → Prop) :
    FlagChoices.Invariant (instruction.undefinedFlags state)
      (fun choices => predicate (executeWith state instruction choices)) := by
  intro left right agree
  change predicate (executeWith state instruction left) ↔ predicate (executeWith state instruction right)
  rw [executeWith_congr state instruction left right agree]

/-- A uniform vector produces exactly the old Bool observation, including
instructions whose semantics ignore the Bool entirely. -/
theorem executeWith_uniform (state : State) (instruction : Instruction) (value : Bool) :
    executeWith state instruction (FlagChoices.uniform value) = execute state instruction value := by
  cases selected : instruction.choiceFlag state with
  | none =>
    simp only [executeWith, Instruction.selectedChoice, selected]
    exact execute_choice_independent state instruction false value selected
  | some flag =>
    cases flag <;>
      simp only [executeWith, Instruction.selectedChoice, selected, FlagChoices.get_uniform]

theorem stepWith_uniform (state : State) (value : Bool) :
    stepWith (FlagChoices.uniform value) state = step value state := by
  cases decoded : decodeAt state with
  | error fault => simp only [stepWith, step, decoded, error_bind]
  | ok instruction =>
    simp only [stepWith, step, decoded, ok_bind, executeWith_uniform]

/-- Every vector instruction outcome is an actual Bool-profile outcome.
The witness is selected from the actual prestate's declared active flag. -/
theorem executeWith_exists_bool (state : State) (instruction : Instruction) (choices : FlagChoices) :
    ∃ value : Bool, executeWith state instruction choices = execute state instruction value :=
  ⟨instruction.selectedChoice state choices, rfl⟩

/-- Every Bool instruction outcome has a vector representative. Together with
`executeWith_exists_bool`, this establishes equality of possible observations
for the current profile, rather than just an inclusion of selected results. -/
theorem execute_existsWith (state : State) (instruction : Instruction) (value : Bool) :
    ∃ choices : FlagChoices, executeWith state instruction choices = execute state instruction value :=
  ⟨FlagChoices.uniform value, executeWith_uniform state instruction value⟩

/-- The pointwise compatibility witness follows actual decoding; decode errors
also have the same complete outcome under either choice API. -/
theorem stepWith_exists_bool (state : State) (choices : FlagChoices) :
    ∃ value : Bool, stepWith choices state = step value state := by
  cases decoded : decodeAt state with
  | error fault =>
    exact ⟨false, by simp only [stepWith, step, decoded, error_bind]⟩
  | ok instruction =>
    refine ⟨instruction.selectedChoice state choices, ?_⟩
    simp only [stepWith, step, decoded, ok_bind, executeWith]

theorem step_existsWith (state : State) (value : Bool) :
    ∃ choices : FlagChoices, stepWith choices state = step value state :=
  ⟨FlagChoices.uniform value, stepWith_uniform state value⟩

/-- Vector adaptation cannot manufacture a different operand-read footprint. -/
theorem executeWith_reads {state : State} {instruction : Instruction} {choices : FlagChoices}
    {observation : Observation} (success : executeWith state instruction choices = .ok observation) :
    observation.reads = instruction.operandReads state :=
  execute_reads (af := instruction.selectedChoice state choices) success

/-- Every successful operand read retains the actual memory primitive's
canonicality, span and per-byte access checks. -/
theorem executeWith_reads_succeed {state : State} {instruction : Instruction} {choices : FlagChoices}
    {observation : Observation} (success : executeWith state instruction choices = .ok observation) :
    ∀ read ∈ observation.reads, OperandReadSucceeds state read :=
  execute_reads_succeed (af := instruction.selectedChoice state choices) success

/-- Read success follows from the actual decoded vector step, including RET's
stack read. No read authority is introduced by the compatibility adapter. -/
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
