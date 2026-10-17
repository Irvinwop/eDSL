/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Policy
set_option warningAsError true

namespace EDSL.Grading.Trace
open EDSL EDSL.X86 EDSL.X86.Sequential

abbrev SeqInstruction := EDSL.X86.Sequential.Instruction

/-- Registration, not submission, supplies these relations. An existential
invariant in `Policy` is proof evidence and never an admission premise. -/
structure Rules (Ghost : Type) where
  Current : Ghost → State → Prop
  ReadAllowed : Ghost → State → Read → Prop
  Effect : Ghost → State → SeqInstruction → Observation → Ghost → Prop

/-- Every local obligation is about current RAM and a real decoded instruction.
Returning steps also produce a current evolved OS state. Termination remains
the separate `AllExecutions` obligation of `SemanticClaim`. -/
def Policy (rules : Rules Ghost) (seed : Ghost) (initial : State) : Prop :=
  ∃ Inv : Ghost → State → Prop, Inv seed initial ∧
    ∀ shared before, Inv shared before →
      rules.Current shared before ∧
      ∃ instruction, Sequential.decodeAt before = .ok instruction ∧
        ∀ af, ∃ observation evolved,
          step af before = .ok observation ∧
          (∀ read ∈ observation.reads,
            rules.ReadAllowed shared before read ∧ OperandReadSucceeds before read) ∧
          rules.Effect shared before instruction observation evolved ∧
          match observation.result with
          | .next after => Inv evolved after
          | .returned after => rules.Current evolved after
          | .atomic _ _ | .syscall _ => False

/-- Broader registration rules retain the same invariant, actual steps and
evolved worlds. This changes no admission or execution premise. -/
theorem Policy.mono {Ghost : Type} {rules broader : Rules Ghost} {seed initial}
    (policy : Policy rules seed initial)
    (current : ∀ ghost before, rules.Current ghost before → broader.Current ghost before)
    (permission : ∀ ghost before read,
      rules.ReadAllowed ghost before read → broader.ReadAllowed ghost before read)
    (effect : ∀ ghost before instruction observation evolved,
      rules.Effect ghost before instruction observation evolved →
        broader.Effect ghost before instruction observation evolved) :
    Policy broader seed initial := by
  obtain ⟨Inv, start, advance⟩ := policy
  refine ⟨Inv, start, ?_⟩
  intro ghost before inside
  obtain ⟨present, instruction, decoded, enabled⟩ := advance ghost before inside
  refine ⟨current ghost before present, instruction, decoded, ?_⟩
  intro af
  obtain ⟨observation, evolved, actual, reads, changed, progress⟩ := enabled af
  refine ⟨observation, evolved, actual,
    fun read member => ⟨permission ghost before read (reads read member).1, (reads read member).2⟩,
    effect ghost before instruction observation evolved changed, ?_⟩
  cases outcome : observation.result with
  | next after => simpa only [outcome] using progress
  | returned after =>
    exact current evolved after (by simpa only [outcome] using progress)
  | atomic event after => simp only [outcome] at progress
  | syscall after => simp only [outcome] at progress

/-- A ghost path indexed by the actual machine path, with no OS-only steps. -/
inductive LiftedBlock (rules : Rules Ghost) :
    Choices → State → Ghost → State → Ghost → Nat → List Read → Prop where
  | nil {choices before shared} : LiftedBlock rules choices before shared before shared 0 []
  | next {choices before shared middle evolved after final count reads rest instruction}
      (decoded : Sequential.decodeAt before = .ok instruction)
      (actual : step (choices 0) before = .ok ⟨.next middle, reads⟩)
      (permission : ∀ read ∈ reads,
        rules.ReadAllowed shared before read ∧ OperandReadSucceeds before read)
      (effect : rules.Effect shared before instruction ⟨.next middle, reads⟩ evolved)
      (tail : LiftedBlock rules (choices.drop 1) middle evolved after final count rest) :
      LiftedBlock rules choices before shared after final (count + 1) (reads ++ rest)

/-- One coherent evolved witness per actual prefix, derived by induction on
the REAL block; no future successful execution is a premise. -/
theorem policy_prefix {rules : Rules Ghost} {seed : Ghost} {initial : State}
    (policy : Policy rules seed initial) {choices : Choices} {before : State}
    {count : Nat} {reads : List Read} (block : Block choices initial before count reads) :
    ∃ shared, LiftedBlock rules choices initial seed before shared count reads ∧
      rules.Current shared before := by
  obtain ⟨Inv, start, advance⟩ := policy
  have lift : ∀ {choices initial before count reads},
      Block choices initial before count reads → ∀ shared, Inv shared initial →
        ∃ evolved, LiftedBlock rules choices initial shared before evolved count reads ∧
          Inv evolved before := by
    intro choices initial before count reads block
    induction block with
    | nil =>
      intro shared present
      exact ⟨shared, .nil, present⟩
    | @next choices initial middle before count reads rest actual tail ih =>
      intro shared present
      obtain ⟨_, instruction, decoded, enabled⟩ := advance shared initial present
      obtain ⟨observation, evolved, chosen, permission, effect, progress⟩ := enabled (choices 0)
      have same := Except.ok.inj (chosen.symm.trans actual)
      cases same
      obtain ⟨final, lifted, current⟩ := ih evolved progress
      exact ⟨final, .next decoded actual permission effect lifted, current⟩
    | @atomic choices initial middle before count reads rest event actual tail ih =>
      intro shared present
      obtain ⟨_, _, _, enabled⟩ := advance shared initial present
      obtain ⟨observation, _, chosen, _, _, progress⟩ := enabled (choices 0)
      have same := Except.ok.inj (chosen.symm.trans actual)
      cases same
      exact False.elim progress
  obtain ⟨shared, lifted, present⟩ := lift block seed start
  exact ⟨shared, lifted, (advance shared before present).1⟩

inductive LiftedExecutes (rules : Rules Ghost) :
    Choices → State → Ghost → Result → Ghost → Prop where
  | ret {choices before shared after evolved reads instruction}
      (decoded : Sequential.decodeAt before = .ok instruction)
      (actual : step (choices 0) before = .ok ⟨.returned after, reads⟩)
      (permission : ∀ read ∈ reads,
        rules.ReadAllowed shared before read ∧ OperandReadSucceeds before read)
      (effect : rules.Effect shared before instruction ⟨.returned after, reads⟩ evolved) :
      LiftedExecutes rules choices before shared ⟨after, 1, reads⟩ evolved
  | next {choices before shared middle evolved result final reads instruction}
      (decoded : Sequential.decodeAt before = .ok instruction)
      (actual : step (choices 0) before = .ok ⟨.next middle, reads⟩)
      (permission : ∀ read ∈ reads,
        rules.ReadAllowed shared before read ∧ OperandReadSucceeds before read)
      (effect : rules.Effect shared before instruction ⟨.next middle, reads⟩ evolved)
      (tail : LiftedExecutes rules (choices.drop 1) middle evolved result final) :
      LiftedExecutes rules choices before shared (result.prepend 1 reads) final

/-- The terminal OS state belongs to the SAME actual step chain, including
the returning instruction and its actual operand permissions. -/
theorem policy_return {rules : Rules Ghost} {seed : Ghost} {initial : State}
    (policy : Policy rules seed initial) {choices : Choices} {result : Result}
    (execution : Sequential.Executes choices initial result) :
    ∃ final, LiftedExecutes rules choices initial seed result final ∧
      rules.Current final result.state := by
  obtain ⟨Inv, start, advance⟩ := policy
  have lift : ∀ {choices initial result}, Sequential.Executes choices initial result →
      ∀ shared, Inv shared initial →
        ∃ final, LiftedExecutes rules choices initial shared result final ∧
          rules.Current final result.state := by
    intro choices initial result execution
    induction execution with
    | @ret choices initial after reads actual =>
      intro shared present
      obtain ⟨_, instruction, decoded, enabled⟩ := advance shared initial present
      obtain ⟨observation, evolved, chosen, permission, effect, progress⟩ := enabled (choices 0)
      have same := Except.ok.inj (chosen.symm.trans actual)
      cases same
      exact ⟨evolved, .ret decoded actual permission effect, progress⟩
    | @next choices initial middle result reads actual tail ih =>
      intro shared present
      obtain ⟨_, instruction, decoded, enabled⟩ := advance shared initial present
      obtain ⟨observation, evolved, chosen, permission, effect, progress⟩ := enabled (choices 0)
      have same := Except.ok.inj (chosen.symm.trans actual)
      cases same
      obtain ⟨final, lifted, current⟩ := ih evolved progress
      exact ⟨final, .next decoded actual permission effect lifted, current⟩
    | @atomic choices initial middle result reads event actual tail ih =>
      intro shared present
      obtain ⟨_, _, _, enabled⟩ := advance shared initial present
      obtain ⟨observation, _, chosen, _, _, progress⟩ := enabled (choices 0)
      have same := Except.ok.inj (chosen.symm.trans actual)
      cases same
      exact False.elim progress
  exact lift execution seed start


/-- Erasure certifies that the ghost path has exactly the actual machine
prefix, including its AF stream, instruction count and observed reads. -/
theorem LiftedBlock.erase {Ghost : Type} {rules : Rules Ghost}
    {choices initial seed before current count reads}
    (lifted : LiftedBlock rules choices initial seed before current count reads) :
    Block choices initial before count reads := by
  induction lifted with
  | nil => exact .nil
  | next _ actual _ _ _ ih => exact .next actual ih

/-- Erasure of the returning path includes the actual RET step. -/
theorem LiftedExecutes.erase {Ghost : Type} {rules : Rules Ghost}
    {choices initial seed result current}
    (lifted : LiftedExecutes rules choices initial seed result current) :
    Sequential.Executes choices initial result := by
  induction lifted with
  | ret _ actual _ _ => exact .ret actual
  | next _ actual _ _ _ ih => exact .next actual ih

/-- Every effect can be accumulated along the same actual prefix. This is
used for checked Borrowing histories and for exact no-change frames. -/
theorem LiftedBlock.fold {Ghost : Type} {rules : Rules Ghost}
    {Relation : Ghost → Ghost → Prop}
    (refl : ∀ ghost, Relation ghost ghost)
    (trans : ∀ a b c, Relation a b → Relation b c → Relation a c)
    (onEffect : ∀ ghost before instruction observation evolved,
      rules.Effect ghost before instruction observation evolved → Relation ghost evolved)
    {choices initial seed before current count reads}
    (lifted : LiftedBlock rules choices initial seed before current count reads) :
    Relation seed current := by
  induction lifted with
  | nil => exact refl _
  | next _ _ _ effect _ ih => exact trans _ _ _ (onEffect _ _ _ _ _ effect) ih

theorem LiftedExecutes.fold {Ghost : Type} {rules : Rules Ghost}
    {Relation : Ghost → Ghost → Prop}
    (_refl : ∀ ghost, Relation ghost ghost)
    (trans : ∀ a b c, Relation a b → Relation b c → Relation a c)
    (onEffect : ∀ ghost before instruction observation evolved,
      rules.Effect ghost before instruction observation evolved → Relation ghost evolved)
    {choices initial seed result current}
    (lifted : LiftedExecutes rules choices initial seed result current) :
    Relation seed current := by
  induction lifted with
  | ret _ _ _ effect => exact onEffect _ _ _ _ _ effect
  | next _ _ _ effect _ ih => exact trans _ _ _ (onEffect _ _ _ _ _ effect) ih

/-- Strengthened prefix extraction keeps the invariant used by the policy.
This supplies local reads/effects at the end of an arbitrary real prefix. -/
theorem policy_prefix_invariant {Ghost : Type} {rules : Rules Ghost} {Inv : Ghost → State → Prop}
    (advance : ∀ ghost before, Inv ghost before →
      rules.Current ghost before ∧
      ∃ instruction, Sequential.decodeAt before = .ok instruction ∧
        ∀ af, ∃ observation evolved,
          step af before = .ok observation ∧
          (∀ read ∈ observation.reads,
            rules.ReadAllowed ghost before read ∧ OperandReadSucceeds before read) ∧
          rules.Effect ghost before instruction observation evolved ∧
          match observation.result with
          | .next after => Inv evolved after
          | .returned after => rules.Current evolved after
          | .atomic _ _ | .syscall _ => False)
    {choices initial before count reads}
    (block : Block choices initial before count reads) {seed : Ghost}
    (start : Inv seed initial) :
    ∃ ghost, LiftedBlock rules choices initial seed before ghost count reads ∧ Inv ghost before := by
  induction block generalizing seed with
  | nil => exact ⟨seed, .nil, start⟩
  | @next choices initial middle before count reads rest actual tail ih =>
    obtain ⟨_, instruction, decoded, enabled⟩ := advance seed initial start
    obtain ⟨observation, evolved, chosen, permission, effect, progress⟩ := enabled (choices 0)
    have same := Except.ok.inj (chosen.symm.trans actual)
    cases same
    obtain ⟨final, lifted, current⟩ := ih progress
    exact ⟨final, .next decoded actual permission effect lifted, current⟩
  | @atomic choices initial middle before count reads rest event actual tail ih =>
    obtain ⟨_, _, _, enabled⟩ := advance seed initial start
    obtain ⟨observation, _, chosen, _, _, progress⟩ := enabled (choices 0)
    have same := Except.ok.inj (chosen.symm.trans actual)
    cases same
    exact False.elim progress

/-- Extract a permitted read at its real prefix, with a lifted path starting
at the registered seed. The current world is not selected independently. -/
theorem Policy.read_origin {Ghost : Type} {rules : Rules Ghost} {seed initial}
    (policy : Policy rules seed initial) {choices result}
    (execution : Sequential.Executes choices initial result) {read : Read}
    (member : read ∈ result.reads) :
    ∃ count before priorReads observation ghost,
      count < result.instructions ∧
      LiftedBlock rules choices initial seed before ghost count priorReads ∧
      rules.Current ghost before ∧
      step (choices count) before = .ok observation ∧ read ∈ observation.reads ∧
      rules.ReadAllowed ghost before read ∧ OperandReadSucceeds before read := by
  obtain ⟨count, before, priorReads, observation, bound, block, actual, present⟩ :=
    execution.read_origin member
  obtain ⟨Inv, start, advance⟩ := policy
  obtain ⟨ghost, lifted, inside⟩ := policy_prefix_invariant advance block start
  obtain ⟨current, _, _, enabled⟩ := advance ghost before inside
  obtain ⟨expected, _, chosen, permission, _, _⟩ := enabled (choices count)
  have same := Except.ok.inj (chosen.symm.trans actual)
  cases same
  exact ⟨count, before, priorReads, observation, ghost, bound, lifted, current,
    actual, present, (permission read present).1, (permission read present).2⟩

end EDSL.Grading.Trace
