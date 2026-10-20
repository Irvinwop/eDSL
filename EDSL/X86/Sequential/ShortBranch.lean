/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Machine

set_option warningAsError true

namespace EDSL.X86.Sequential

/-- The selected rel8 destination is measured from the end of the two-byte
instruction. The displacement is sign-extended before full-width addition. -/
def shortBranchTarget (before : State) (condition : Condition) (displacement : Byte) : Word :=
  if condition.holds before.flags then before.rip + 2 + displacement.signExtend 64
  else before.rip + 2

/-- Taken destinations must be canonical. An untaken branch does not inspect
the unused target; the next instruction fetch checks the fallthrough address. -/
def ShortBranchSafe (before : State) (condition : Condition) (displacement : Byte) : Prop :=
  condition.holds before.flags = true →
    canonical (before.rip + 2 + displacement.signExtend 64) = true

/-- The existing JE and legacy JNZ spellings describe the same status
conditions as generic Jcc. This relation leaves their decoder identities intact. -/
inductive ShortBranchForm : Instruction → Condition → Byte → Prop where
  | generic (condition : Condition) (displacement : Byte) :
      ShortBranchForm (.jcc condition displacement) condition displacement
  | equal (displacement : Byte) : ShortBranchForm (.je displacement) .equal displacement
  | notEqual (displacement : Byte) :
      ShortBranchForm (.legacy (.jnz displacement)) .notEqual displacement

theorem execute_shortBranch_form (before : State) {instruction : Instruction}
    {condition : Condition} {displacement : Byte}
    (form : ShortBranchForm instruction condition displacement) (af : Bool) :
    execute before instruction af = do
      return ⟨.next (← executeShortBranch before (condition.holds before.flags) displacement), []⟩ := by
  cases form with
  | generic => rfl
  | equal => rfl
  | notEqual displacement =>
    simp [execute,X86.executeInstruction,executeJnz,Condition.holds,Instruction.operandReads]

/-- Successful execution derives the complete post-state from the actual
condition, with no register, flag, data read or RAM effect. -/
theorem execute_shortBranch_context (before : State) {instruction : Instruction}
    {condition : Condition} {displacement : Byte}
    (form : ShortBranchForm instruction condition displacement)
    (safe : ShortBranchSafe before condition displacement) (af : Bool) :
    execute before instruction af =
      .ok ⟨.next { before with rip := shortBranchTarget before condition displacement }, []⟩ := by
  rw [execute_shortBranch_form before form af]
  cases taken : condition.holds before.flags with
  | false => simp only [executeShortBranch,shortBranchTarget,taken,Bool.false_eq_true,
      ite_false,ok_bind,pure_ok]
  | true => simp only [executeShortBranch,shortBranchTarget,taken,safe taken,
      ite_true,ok_bind,pure_ok]

/-- Noncanonical taken targets fault before producing a continuation. This
claim does not grant fetch permission at either possible destination. -/
theorem execute_shortBranch_noncanonical (before : State) {instruction : Instruction}
    {condition : Condition} {displacement : Byte}
    (form : ShortBranchForm instruction condition displacement)
    (taken : condition.holds before.flags = true)
    (bad : canonical (before.rip + 2 + displacement.signExtend 64) = false) (af : Bool) :
    execute before instruction af =
      .error (.noncanonicalBranch (before.rip + 2 + displacement.signExtend 64)) := by
  rw [execute_shortBranch_form before form af]
  simp only [executeShortBranch,taken,ite_true,bad,Bool.false_eq_true,
    ite_false,error_bind]

/-- The unused target may be noncanonical. No target accessibility check is
silently substituted for actual execution of a false condition. -/
theorem execute_shortBranch_untaken (before : State) {instruction : Instruction}
    {condition : Condition} {displacement : Byte}
    (form : ShortBranchForm instruction condition displacement)
    (untaken : condition.holds before.flags = false) (af : Bool) :
    execute before instruction af = .ok ⟨.next { before with rip := before.rip + 2 }, []⟩ := by
  rw [execute_shortBranch_form before form af]
  simp [executeShortBranch,untaken]

end EDSL.X86.Sequential
