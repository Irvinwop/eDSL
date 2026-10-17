/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.CountedStoreFinal64.Proof
import EDSL.X86.Sequential.CutpointsAccounting

set_option warningAsError true

namespace EDSL.CountedStoreFinal64
open EDSL X86 X86.Sequential CountedStore64

/-- Model instructions including RET. This is separate from task acceptance. -/
def cost (count : Nat) : Nat := if count = 0 then 4 else 3 * count + 5

def remainingCost (node : Node) (state : State) : Nat :=
  let count := (state.registers .rdx).toNat
  match node with
  | .entry => cost count
  | .test => if count = 0 then 3 else 3 * count + 4
  | .guard => if count = 0 then 2 else 3 * count + 3
  | .increment => 3 * count + 2
  | .decrement => 3 * count + 1
  | .back => 3 * count + 3
  | .store => 2
  | .ret => 1

private theorem machine_inside {input initial source budget node state}
    (pre : Pre bytes input initial) (inside : Interior input initial source budget node state) :
    (certificate pre (rawSupport input initial)).machine.Interior source budget node state :=
  ⟨(), True.intro, inside⟩

/-- Each actual step consumes one instruction; RET alone reads an operand. -/
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
      simp only [remainingCost, cost, GCC.move, State.writeRegister, reduceCtorEq, ite_false]
      split <;> omega
    | test =>
      have chosen := (step_eq_execute af decoded).trans (execute_test _ af)
      have same := Except.ok.inj (actual.symm.trans chosen)
      cases same
      refine ⟨.guard, ⟨.entry, input.count.toNat + 1,
        machine_inside pre (Interior.guard af)⟩, ?_, rfl⟩
      simp only [remainingCost, GCC.test]
      split <;> omega
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
        have positive := BitVec.toNat_pos_of_ne_zero zero
        simp only [remainingCost, GCC.atPC, GCC.test, GCC.move, State.writeRegister,
          reduceCtorEq, ite_false]
        split <;> omega
    | increment h =>
      have chosen := (step_eq_execute af decoded).trans (execute_increment _ af)
      have same := Except.ok.inj (actual.symm.trans chosen)
      cases same
      refine ⟨.decrement, ⟨.increment, _,
        machine_inside pre (Interior.decrement h)⟩, ?_, rfl⟩
      simp only [remainingCost, GCC.increment, State.writeRegister, reduceCtorEq, ite_false]
      omega
    | @decrement before h =>
      have chosen := (step_eq_execute af decoded).trans (execute_decrement _ af)
      have same := Except.ok.inj (actual.symm.trans chosen)
      cases same
      refine ⟨.back, ⟨.increment, (before.registers .rdx).toNat,
        machine_inside pre (Interior.back h)⟩, ?_, rfl⟩
      have decreased := decrement_count (before.registers .rdx) h.nonzero
      simp only [remainingCost, incState, GCC.decrement, GCC.increment,
        State.writeRegister, reduceCtorEq, ite_true, ite_false]
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
        refine ⟨.store, ⟨.increment, (before.registers .rdx).toNat,
          machine_inside pre (Interior.store (nextReady pre h zero))⟩, ?_, rfl⟩
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
    | store ready =>
      have pointer := frame.pointer pre
      have writable : canStoreQWord state.memory (state.registers .rdi) = true := by
        rw [pointer]; exact frame.writable
      have chosen := (step_eq_execute af decoded).trans (execute_store _ af writable)
      have same := Except.ok.inj (actual.symm.trans chosen)
      cases same
      exact ⟨.ret, ⟨source, budget, machine_inside pre (Interior.ret (storedExit pre ready))⟩, rfl, rfl⟩
    | ret exit =>
      have stack : state.registers .rsp = initial.registers .rsp :=
        frame.registers .rsp (by decide) (by decide)
      have loaded : readWord state.memory (state.registers .rsp) = .ok input.returnAddress := by
        rw [stack]; exact frame.stackRead
      have chosen := (step_eq_execute af decoded).trans (execute_ret loaded pre.memory.returnCanonical af)
      have same := Except.ok.inj (actual.symm.trans chosen)
      cases same
      exact ⟨rfl, by rw [stack]⟩

/-- Any actual execution has the exact model cost and original STACK8 read. -/
theorem execution_exact {input initial choices result} (pre : Pre bytes input initial)
    (actual : Sequential.Executes choices initial result) :
    result.instructions = cost input.count.toNat ∧
      result.reads = [⟨.stack, initial.registers .rsp, 8⟩] := by
  have inside := machine_inside pre (Interior.entry (input := input) (initial := initial))
  have exactCost := (accounting pre).execution_exact actual ⟨.entry, input.count.toNat + 1, inside⟩
  simpa only [accounting, remainingCost, pre.count] using exactCost

theorem resource_exact {resource initial} (pre : ResourcePre bytes resource initial)
    (choices : Choices) :
    ∃ result : Result, Sequential.Executes choices initial result ∧
      Post (resourceInput resource) initial result.state ∧ ResourceReturn resource initial result ∧
      result.instructions = cost resource.count.toNat ∧
      result.reads = [⟨.stack, initial.registers .rsp, 8⟩] ∧ ResourcePolicy resource initial := by
  obtain ⟨result, actual, post, returned, _⟩ := (resource_semantics pre).1 choices
  obtain ⟨exactCost, reads⟩ := execution_exact pre.machine actual
  exact ⟨result, actual, post, returned, exactCost, reads, (resource_semantics pre).2⟩

/-- A comparison of these three concrete loop costs, without a claim about
other programs, source-level effects, micro-ops, cycles or global optimality. -/
theorem cost_comparison (count : Nat) :
    cost count ≤ 4 * count + 4 ∧ cost count ≤ 6 * count + 4 ∧
      (1 < count → cost count < 4 * count + 4) := by
  unfold cost
  split <;> omega

end EDSL.CountedStoreFinal64
