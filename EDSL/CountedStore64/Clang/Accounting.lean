/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CountedStore64.Clang.Proof
import EDSL.X86.Sequential.CutpointsAccounting

set_option warningAsError true

/-! Optional accounting follows the actual Clang instruction path, including
its final RET and ordered operand reads. It changes no admission or result
contract, and counts no physical time, micro-ops or alternative programs. -/

namespace EDSL.CountedStore64.Clang
open EDSL X86 X86.Sequential

/-- Residual retired model instructions. STORE precedes DEC, so decrement's
full count still includes that iteration; back's count already excludes it. -/
def remainingCost (node : Node) (state : State) : Nat :=
  let count := (state.registers .rdx).toNat
  match node with
  | .entry => 4 * count + 4
  | .test => 4 * count + 3
  | .guard => 4 * count + 2
  | .increment => 4 * count + 1
  | .store => 4 * count
  | .decrement => 4 * count - 1
  | .back => 4 * count + 2
  | .ret => 1

private theorem machine_inside {input initial source budget node state}
    (pre : Pre bytes input initial) (inside : Interior input initial source budget node state) :
    (certificate pre (rawSupport input initial)).machine.Interior source budget node state :=
  ⟨(), True.intro, inside⟩

/-- Every actual local step consumes one instruction; only RET reads an
operand, using the original caller's complete eight-byte return slot. -/
noncomputable def accounting {input initial} (pre : Pre bytes input initial) :
    Cutpoints.Accounting (certificate pre (rawSupport input initial)).machine where
  cost := remainingCost
  reads _ _ := [⟨.stack, initial.registers .rsp, 8⟩]
  localStep source budget node state valid af observation actual := by
    obtain ⟨_, _, inside⟩ := valid
    have frame := interior_frame pre inside
    have pc := interior_pc inside
    have decoded := decode frame.code node pc
    cases inside with
    | entry =>
      have chosen := (step_eq_execute af decoded).trans (execute_move initial af)
      have same := Except.ok.inj (actual.symm.trans chosen)
      cases same
      refine ⟨.test, ⟨.entry, input.count.toNat + 1,
        machine_inside pre Interior.test⟩, ?_, rfl⟩
      simp only [remainingCost, GCC.move, State.writeRegister, reduceCtorEq, ite_false]
      omega
    | test =>
      have chosen := (step_eq_execute af decoded).trans (execute_test _ af)
      have same := Except.ok.inj (actual.symm.trans chosen)
      cases same
      refine ⟨.guard, ⟨.entry, input.count.toNat + 1,
        machine_inside pre (Interior.guard af)⟩, ?_, rfl⟩
      simp only [remainingCost, GCC.test]
      omega
    | guard prior =>
      by_cases zero : initial.registers .rdx = 0
      · have zf : (test (move initial) prior).flags.getLsbD 6 = true := by
          rw [tested_zero]
          simp only [GCC.move, State.writeRegister, reduceCtorEq, ite_false]
          rw [zero]; decide
        have chosen := (step_eq_execute af decoded).trans (guard_exit frame.code pc zf af)
        have same := Except.ok.inj (actual.symm.trans chosen)
        cases same
        refine ⟨.ret, ⟨.entry, input.count.toNat + 1,
          machine_inside pre (Interior.ret (initialExit pre zero prior))⟩, ?_, rfl⟩
        simp [remainingCost, GCC.test, GCC.move, State.writeRegister, zero]
      · have zf : (test (move initial) prior).flags.getLsbD 6 = false := by
          rw [tested_zero]
          simp only [GCC.move, State.writeRegister, reduceCtorEq, ite_false,
            Bool.beq_eq_decide_eq, zero, decide_false]
        have chosen := (step_eq_execute af decoded).trans (guard_body pc zf af)
        have same := Except.ok.inj (actual.symm.trans chosen)
        cases same
        refine ⟨.increment, ⟨.increment, _,
          machine_inside pre (Interior.increment (initialHeader pre zero prior))⟩, ?_, rfl⟩
        simp only [remainingCost, GCC.atPC, GCC.test]
        omega
    | increment h =>
      have chosen := (step_eq_execute af decoded).trans (execute_increment _ af)
      have same := Except.ok.inj (actual.symm.trans chosen)
      cases same
      refine ⟨.store, ⟨.increment, _,
        machine_inside pre (Interior.store h)⟩, ?_, rfl⟩
      simp only [remainingCost, GCC.increment, State.writeRegister,
        reduceCtorEq, ite_false]
      omega
    | @store before h =>
      have pointer := frame.pointer pre
      have writable : canStoreQWord (incState before).memory
          ((incState before).registers .rdi) = true := by
        rw [pointer]; exact frame.writable
      have chosen := (step_eq_execute af decoded).trans (execute_store _ af writable)
      have same := Except.ok.inj (actual.symm.trans chosen)
      cases same
      refine ⟨.decrement, ⟨.increment, (before.registers .rdx).toNat,
        machine_inside pre (Interior.decrement h)⟩, ?_, rfl⟩
      have positive := BitVec.toNat_pos_of_ne_zero h.nonzero
      simp only [remainingCost, incState, GCC.store, GCC.increment,
        State.writeRegister, reduceCtorEq, ite_false]
      omega
    | @decrement before h =>
      have chosen := (step_eq_execute af decoded).trans (execute_decrement _ af)
      have same := Except.ok.inj (actual.symm.trans chosen)
      cases same
      refine ⟨.back, ⟨.increment, (before.registers .rdx).toNat,
        machine_inside pre (Interior.back h)⟩, ?_, rfl⟩
      have decreased := decrement_count (before.registers .rdx) h.nonzero
      simp only [remainingCost, storedState, incState, GCC.decrement,
        GCC.store, GCC.increment, State.writeRegister, reduceCtorEq, ite_true, ite_false]
      omega
    | @back before h =>
      by_cases zero : (decState before).registers .rdx = 0
      · have zf : (decState before).flags.getLsbD 6 = true := by
          rw [decState, decremented_zero]
          change ((decState before).registers .rdx == 0) = true
          rw [zero]; decide
        have chosen := (step_eq_execute af decoded).trans (back_exit pc zf af)
        have same := Except.ok.inj (actual.symm.trans chosen)
        cases same
        refine ⟨.ret, ⟨.increment, (before.registers .rdx).toNat,
          machine_inside pre (Interior.ret (nextExit pre h zero))⟩, ?_, rfl⟩
        simp [remainingCost, zero]
      · have zf : (decState before).flags.getLsbD 6 = false := by
          rw [decState, decremented_zero]
          change ((decState before).registers .rdx == 0) = false
          simp only [Bool.beq_eq_decide_eq, zero, decide_false]
        have chosen := (step_eq_execute af decoded).trans (back_taken frame.code pc zf af)
        have same := Except.ok.inj (actual.symm.trans chosen)
        cases same
        refine ⟨.increment, ⟨.increment, ((continued initial.rip before).registers .rdx).toNat,
          machine_inside pre (Interior.increment (nextHeader pre h zero))⟩, ?_, rfl⟩
        simp only [remainingCost, GCC.atPC]
        omega
    | ret exit =>
      have stack : state.registers .rsp = initial.registers .rsp :=
        frame.registers .rsp (by decide) (by decide)
      have loaded : readWord state.memory (state.registers .rsp) = .ok input.returnAddress := by
        rw [stack]; exact frame.stackRead
      have chosen := (step_eq_execute af decoded).trans (execute_ret loaded pre.memory.returnCanonical af)
      have same := Except.ok.inj (actual.symm.trans chosen)
      cases same
      exact ⟨rfl, by rw [stack]⟩

/-- Every actual returning execution for every full64 count and AF stream
has this exact cost and trace, using unchanged present-state admission. -/
theorem execution_exact {input initial choices result} (pre : Pre bytes input initial)
    (actual : Sequential.Executes choices initial result) :
    result.instructions = 4 * input.count.toNat + 4 ∧
      result.reads = [⟨.stack, initial.registers .rsp, 8⟩] := by
  have inside := machine_inside pre (Interior.entry (input := input) (initial := initial))
  have exactCost := (accounting pre).execution_exact actual ⟨.entry, input.count.toNat + 1, inside⟩
  simpa only [accounting, remainingCost, pre.count] using exactCost

/-- Totality and the independent functional result retain exact accounting
for that same execution and the complete existing raw policy. -/
theorem raw_exact {input initial} (pre : Pre bytes input initial) (choices : Choices) :
    ∃ result : Result, Sequential.Executes choices initial result ∧
      Post input initial result.state ∧ result.instructions = 4 * input.count.toNat + 4 ∧
      result.reads = [⟨.stack, initial.registers .rsp, 8⟩] ∧ RawPolicy bytes input initial := by
  obtain ⟨result, actual, post, _⟩ := raw_semantics pre choices
  obtain ⟨cost, reads⟩ := execution_exact pre actual
  exact ⟨result, actual, post, cost, reads, raw_policy pre⟩

/-- Exact cost preserves the same checked world evolution and returned
authority, including the ability to perform another arbitrary checked store. -/
theorem resource_exact {resource initial} (pre : ResourcePre bytes resource initial)
    (choices : Choices) :
    ∃ result : Result, Sequential.Executes choices initial result ∧
      Post (resourceInput resource) initial result.state ∧ ResourceReturn resource initial result ∧
      result.instructions = 4 * resource.count.toNat + 4 ∧
      result.reads = [⟨.stack, initial.registers .rsp, 8⟩] ∧ ResourcePolicy resource initial := by
  obtain ⟨result, actual, post, returned, _⟩ := (resource_semantics pre).1 choices
  obtain ⟨cost, reads⟩ := execution_exact pre.machine actual
  exact ⟨result, actual, post, returned, cost, reads, (resource_semantics pre).2⟩

end EDSL.CountedStore64.Clang
