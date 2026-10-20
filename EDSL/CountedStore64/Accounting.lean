/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CountedStore64.Proof
import EDSL.X86.Sequential.CutpointsAccounting

set_option warningAsError true

/-! Optional accounting for the exact GCC byte window. Costs count modeled
decoded instructions, including RET; reads record operand reads in execution
order. Neither quantity changes functional admission or the registered result
contract. These theorems do not count CPU cycles, micro-ops, source operations
or intermediate stores, and do not establish an optimality bound. -/

namespace EDSL.CountedStore64.GCC
open EDSL X86 X86.Sequential

/-- Residual instruction count at each checked machine location. After DEC,
RDX already excludes the pending store, so the store/back phases include its
remaining instructions before the next count test. -/
def remainingCost (node : Node) (state : State) : Nat :=
  let count := (state.registers .rdx).toNat
  match node with
  | .entry => 6 * count + 4
  | .header => 6 * count + 3
  | .guard => 6 * count + 2
  | .increment => 6 * count + 1
  | .decrement => 6 * count
  | .store => 6 * count + 5
  | .back => 6 * count + 4
  | .ret => 1

private theorem machine_inside {input initial source budget node state}
    (pre : Pre bytes input initial) (inside : Interior input initial source budget node state) :
    (certificate pre (rawSupport input initial)).machine.Interior source budget node state :=
  ⟨(), True.intro, inside⟩

/-- Each actual local step consumes exactly one modeled instruction. The
only operand read on the admitted execution is the caller's full RET slot. -/
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
      refine ⟨.header, ⟨.header, ((move initial).registers .rdx).toNat,
        machine_inside pre (Interior.header (initialized pre))⟩, ?_, rfl⟩
      simp only [remainingCost, move, State.writeRegister, reduceCtorEq, ite_false]
      omega
    | header h =>
      have chosen := (step_eq_execute af decoded).trans (execute_test _ af)
      have same := Except.ok.inj (actual.symm.trans chosen)
      cases same
      refine ⟨.guard, ⟨.header, _,
        machine_inside pre (Interior.guard h af)⟩, ?_, rfl⟩
      simp only [remainingCost, test]
      omega
    | @guard before h prior =>
      by_cases zero : before.registers .rdx = 0
      · have zf : (test before prior).flags.getLsbD 6 = true := by rw [tested_zero, zero]; decide
        have chosen := (step_eq_execute af decoded).trans (guard_exit frame.code pc zf af)
        have same := Except.ok.inj (actual.symm.trans chosen)
        cases same
        refine ⟨.ret, ⟨.header, (before.registers .rdx).toNat,
          machine_inside pre (Interior.ret h zero prior)⟩, ?_, rfl⟩
        simp [remainingCost, test, zero]
      · have zf : (test before prior).flags.getLsbD 6 = false := by
          rw [tested_zero]
          simp only [Bool.beq_eq_decide_eq, zero, decide_false]
        have chosen := (step_eq_execute af decoded).trans (guard_body pc zf af)
        have same := Except.ok.inj (actual.symm.trans chosen)
        cases same
        refine ⟨.increment, ⟨.header, (before.registers .rdx).toNat,
          machine_inside pre (Interior.increment h zero prior)⟩, ?_, rfl⟩
        simp only [remainingCost, atPC, test]
        omega
    | @increment before h nonzero prior =>
      have chosen := (step_eq_execute af decoded).trans (execute_increment _ af)
      have same := Except.ok.inj (actual.symm.trans chosen)
      cases same
      refine ⟨.decrement, ⟨.header, (before.registers .rdx).toNat,
        machine_inside pre (Interior.decrement h nonzero prior)⟩, ?_, rfl⟩
      simp only [remainingCost, increment, body, atPC, test, State.writeRegister,
        reduceCtorEq, ite_false]
      omega
    | @decrement before h nonzero prior =>
      have chosen := (step_eq_execute af decoded).trans (execute_decrement _ af)
      have same := Except.ok.inj (actual.symm.trans chosen)
      cases same
      refine ⟨.store, ⟨.header, (before.registers .rdx).toNat,
        machine_inside pre (Interior.store h nonzero prior)⟩, ?_, rfl⟩
      have decreased := decrement_count (before.registers .rdx) nonzero
      simp only [remainingCost, decrement, increment, body, atPC, test,
        State.writeRegister, reduceCtorEq, ite_true, ite_false]
      omega
    | @store before h nonzero prior =>
      have pointer := frame.pointer pre
      have writable : canStoreQWord (pending initial.rip before prior).memory
          ((pending initial.rip before prior).registers .rdi) = true := by
        rw [pointer]; exact frame.writable
      have chosen := (step_eq_execute af decoded).trans (execute_store _ af writable)
      have same := Except.ok.inj (actual.symm.trans chosen)
      cases same
      refine ⟨.back, ⟨.header, (before.registers .rdx).toNat,
        machine_inside pre (Interior.back h nonzero prior)⟩, ?_, rfl⟩
      simp only [remainingCost, store]
      omega
    | @back before h nonzero prior =>
      have chosen := (step_eq_execute af decoded).trans (back_edge frame.code pc af)
      have same := Except.ok.inj (actual.symm.trans chosen)
      cases same
      refine ⟨.header, ⟨.header, ((cycle initial.rip before prior).registers .rdx).toNat,
        machine_inside pre (Interior.header (nextHeader pre h nonzero prior))⟩, ?_, rfl⟩
      simp only [remainingCost, atPC]
      omega
    | @ret before h zero prior =>
      have stack : (exitState initial.rip before prior).registers .rsp = initial.registers .rsp :=
        frame.registers .rsp (by decide) (by decide)
      have loaded : readWord (exitState initial.rip before prior).memory
          ((exitState initial.rip before prior).registers .rsp) = .ok input.returnAddress := by
        rw [stack]; exact frame.stackRead
      have chosen := (step_eq_execute af decoded).trans (execute_ret loaded pre.memory.returnCanonical af)
      have same := Except.ok.inj (actual.symm.trans chosen)
      cases same
      exact ⟨rfl, by rw [stack]⟩

/-- Every actual returning execution, for any modeled AF stream and every
full64 count, has this cost and ordered operand-read trace. This accounting
uses the unchanged present-state Pre; it assumes no successful evaluator run. -/
theorem execution_exact {input initial choices result} (pre : Pre bytes input initial)
    (actual : Sequential.Executes choices initial result) :
    result.instructions = 6 * input.count.toNat + 4 ∧
      result.reads = [⟨.stack, initial.registers .rsp, 8⟩] := by
  have inside := machine_inside pre (Interior.entry (input := input) (initial := initial))
  have exactCost := (accounting pre).execution_exact actual ⟨.entry, input.count.toNat + 1, inside⟩
  simpa only [accounting, remainingCost, pre.count] using exactCost

/-- All-choice totality and the independent functional result together with
exact accounting for that same actual execution and the existing raw policy. -/
theorem raw_exact {input initial} (pre : Pre bytes input initial) (choices : Choices) :
    ∃ result : Result, Sequential.Executes choices initial result ∧
      Post input initial result.state ∧ result.instructions = 6 * input.count.toNat + 4 ∧
      result.reads = [⟨.stack, initial.registers .rsp, 8⟩] ∧ RawPolicy bytes input initial := by
  obtain ⟨result, actual, post, _⟩ := raw_semantics pre choices
  obtain ⟨cost, reads⟩ := execution_exact pre actual
  exact ⟨result, actual, post, cost, reads, raw_policy pre⟩

/-- The exact-cost result also retains the original ResourceReturn for its
same actual path: checked world evolution, current RAM, all resource frames,
live loans and authority for another checked64 store. Resource admission and
the returned-world predicate are unchanged. -/
theorem resource_exact {resource initial} (pre : ResourcePre bytes resource initial)
    (choices : Choices) :
    ∃ result : Result, Sequential.Executes choices initial result ∧
      Post (resourceInput resource) initial result.state ∧ ResourceReturn resource initial result ∧
      result.instructions = 6 * resource.count.toNat + 4 ∧
      result.reads = [⟨.stack, initial.registers .rsp, 8⟩] ∧ ResourcePolicy resource initial := by
  obtain ⟨result, actual, post, returned, _⟩ := (resource_semantics pre).1 choices
  obtain ⟨cost, reads⟩ := execution_exact pre.machine actual
  exact ⟨result, actual, post, returned, cost, reads, (resource_semantics pre).2⟩

end EDSL.CountedStore64.GCC
