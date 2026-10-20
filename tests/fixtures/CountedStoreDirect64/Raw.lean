/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.CountedStoreDirect64.Machine

set_option warningAsError true

namespace EDSL.CountedStoreDirect64
open EDSL X86 X86.Sequential CountedStore64

theorem ready_frame {variant input initial} (pre : Pre (bytes variant) input initial) :
    Common.Frame (bytes variant) input initial (ready variant initial) := by
  have frame := Common.Frame.initial pre
  cases variant with
  | gcc =>
    exact frame.sameMemory rfl (by intros; simp_all [ready,lea,State.writeRegister]) rfl
  | clang =>
    exact frame.move.sameMemory rfl (by intros; simp_all [ready,add,State.writeRegister])
      (addFlags64_preserves ..)

theorem ready_value {variant input initial} (pre : Pre (bytes variant) input initial) :
    (ready variant initial).registers .rax = input.argument + input.count := by
  cases variant <;> simp [ready,lea,add,CountedStore64.GCC.move,State.writeRegister,
    pre.memory.source,pre.count]

theorem guard_frame {variant input initial} (pre : Pre (bytes variant) input initial) (af : Bool) :
    Common.Frame (bytes variant) input initial (guard variant initial af) :=
  (ready_frame pre).test af

theorem atStore_frame {variant input initial} (pre : Pre (bytes variant) input initial) (af : Bool) :
    Common.Frame (bytes variant) input initial (atStore variant initial af) :=
  (guard_frame pre af).atPC _

theorem atRet_frame {variant input initial} (pre : Pre (bytes variant) input initial) (af : Bool) :
    Common.Frame (bytes variant) input initial (atRet variant initial af) :=
  (guard_frame pre af).atPC _

theorem stored_frame {variant input initial} (pre : Pre (bytes variant) input initial) (af : Bool) :
    Common.Frame (bytes variant) input initial (store (atStore variant initial af)) :=
  (atStore_frame pre af).store pre

theorem guard_value {variant input initial} (pre : Pre (bytes variant) input initial) (af : Bool) :
    (guard variant initial af).registers .rax = input.argument + input.count :=
  ready_value pre

theorem guard_count {variant input initial} (pre : Pre (bytes variant) input initial) (af : Bool) :
    (guard variant initial af).registers .rdx = input.count :=
  (ready_count variant initial).trans pre.count

theorem prefix_block {variant input initial} (pre : Pre (bytes variant) input initial) (choices : Choices) :
    Sequential.Block choices initial (ready variant initial) (prefixCost variant) [] := by
  cases variant with
  | gcc =>
    have first := (step_eq_execute (choices 0) (decode_entry pre.memory.code rfl)).trans
      (execute_lea initial (choices 0))
    simpa [ready,prefixCost] using Sequential.Block.next first Sequential.Block.nil
  | clang =>
    have first := (step_eq_execute (choices 0) (decode_entry pre.memory.code rfl)).trans
      (execute_move initial (choices 0))
    have code : CodeAt (move initial).memory initial.rip (bytes .clang) := pre.memory.code
    have second := (step_eq_execute ((choices.drop 1) 0) (decode_add code rfl)).trans
      (execute_add (move initial) ((choices.drop 1) 0))
    simpa [ready,prefixCost] using
      Sequential.Block.next first (Sequential.Block.next second Sequential.Block.nil)

theorem test_step {variant input initial} (pre : Pre (bytes variant) input initial) (af : Bool) :
    Sequential.step af (ready variant initial) = .ok ⟨.next (guard variant initial af),[]⟩ :=
  (step_eq_execute af (decode (ready_frame pre).code .test (ready_pc variant initial))).trans
    (execute_test (ready variant initial) af)

theorem guard_zero_step {variant input initial} (pre : Pre (bytes variant) input initial)
    (zero : input.count = 0) (prior af : Bool) :
    Sequential.step af (guard variant initial prior) = .ok ⟨.next (atRet variant initial prior),[]⟩ := by
  have zf : (guard variant initial prior).flags.getLsbD 6 = true := by
    change (test (ready variant initial) prior).flags.getLsbD 6 = true
    rw [tested_zero,ready_count,pre.count,zero]
    decide
  exact (step_eq_execute af (decode (guard_frame pre prior).code .guard
    (guard_pc variant initial prior))).trans
      (guard_exit (guard_frame pre prior).code (guard_pc variant initial prior) zf af)

theorem guard_positive_step {variant input initial} (pre : Pre (bytes variant) input initial)
    (nonzero : input.count ≠ 0) (prior af : Bool) :
    Sequential.step af (guard variant initial prior) = .ok ⟨.next (atStore variant initial prior),[]⟩ := by
  have zf : (guard variant initial prior).flags.getLsbD 6 = false := by
    change (test (ready variant initial) prior).flags.getLsbD 6 = false
    rw [tested_zero,ready_count,pre.count]
    simp only [Bool.beq_eq_decide_eq,nonzero,decide_false]
  exact (step_eq_execute af (decode (guard_frame pre prior).code .guard
    (guard_pc variant initial prior))).trans (guard_body (guard_pc variant initial prior) zf af)

theorem store_step {variant input initial} (pre : Pre (bytes variant) input initial) (prior af : Bool) :
    Sequential.step af (atStore variant initial prior) =
      .ok ⟨.next (store (atStore variant initial prior)),[]⟩ := by
  have frame := atStore_frame pre prior
  have writable : canStoreQWord (atStore variant initial prior).memory
      ((atStore variant initial prior).registers .rdi) = true := by
    rw [frame.pointer pre]
    exact frame.writable
  exact (step_eq_execute af (decode frame.code .store rfl)).trans
    (execute_store _ af writable)

theorem ret_step {variant input initial before} (pre : Pre (bytes variant) input initial)
    (frame : Common.Frame (bytes variant) input initial before)
    (pc : before.rip = initial.rip + BitVec.ofNat 64 (offset variant .ret)) (af : Bool) :
    Sequential.step af before = .ok ⟨.returned (finish before input.returnAddress),
      [⟨.stack,initial.registers .rsp,8⟩]⟩ := by
  have stack : before.registers .rsp = initial.registers .rsp :=
    frame.registers .rsp (by decide) (by decide)
  have loaded : readWord before.memory (before.registers .rsp) = .ok input.returnAddress := by
    rw [stack]
    exact frame.stackRead
  have actual := (step_eq_execute af (decode frame.code .ret pc)).trans
    (execute_ret loaded pre.memory.returnCanonical af)
  simpa only [stack] using actual

private theorem finish_post {variant input initial before} (_pre : Pre (bytes variant) input initial)
    (frame : Common.Frame (bytes variant) input initial before)
    (value : before.registers .rax = input.argument + input.count)
    (stored : loadQWord before.memory input.address = .ok (expectedValue input)) :
    Post input initial (finish before input.returnAddress) := by
  refine ⟨?_,stored,frame.outside,frame.writableMap,frame.executableMap,rfl,?_,?_,frame.flags⟩
  · simpa only [CountedStore64.GCC.finish,State.writeRegister,reduceCtorEq,ite_false] using value
  · simp only [CountedStore64.GCC.finish,State.writeRegister,ite_true]
    exact congrArg (· + 8) (frame.registers .rsp (by decide) (by decide))
  · intro register member
    have a : register ≠ .rax := by intro same; subst register; simp [StoreLoad64.calleeSaved] at member
    have d : register ≠ .rdx := by intro same; subst register; simp [StoreLoad64.calleeSaved] at member
    have s : register ≠ .rsp := by intro same; subst register; simp [StoreLoad64.calleeSaved] at member
    simpa only [CountedStore64.GCC.finish,State.writeRegister,s,ite_false] using frame.registers register a d

/-- The final mathematical result is shared by both windows. Zero retains
old target bytes; positive counts write the complete modular sum once. -/
theorem final_post {variant input initial} (pre : Pre (bytes variant) input initial) (af : Bool) :
    Post input initial (finalState variant initial input.returnAddress af) := by
  by_cases zero : input.count = 0
  · have stored : loadQWord (atRet variant initial af).memory input.address = .ok (expectedValue input) := by
      simpa only [atRet,guard,CountedStore64.GCC.atPC,CountedStore64.GCC.test,
        ready_memory,expectedValue,zero,ite_true] using pre.memory.oldValue
    simpa only [finalState,beforeReturn,pre.count,zero,ite_true] using
      finish_post pre (atRet_frame pre af) (guard_value pre af) stored
  · have frame := atStore_frame pre af
    have value : (atStore variant initial af).registers .rax = input.argument + input.count := guard_value pre af
    have stored : loadQWord (store (atStore variant initial af)).memory input.address =
        .ok (expectedValue input) := by
      change loadQWord (writeQWordUnchecked (atStore variant initial af).memory
        ((atStore variant initial af).registers .rdi) ((atStore variant initial af).registers .rax))
        input.address = .ok _
      rw [frame.pointer pre,value]
      simpa only [expectedValue,zero,ite_false] using
        qword_load_after_write (atStore variant initial af).memory input.address
          (input.argument + input.count) pre.memory.target_addressable
    simpa only [finalState,beforeReturn,pre.count,zero,ite_false] using
      finish_post pre (stored_frame pre af) value stored

theorem suffix_execution {variant input initial} (pre : Pre (bytes variant) input initial) (choices : Choices) :
    Sequential.Executes choices (ready variant initial)
      ⟨finalState variant initial input.returnAddress (choices 0),
        if input.count = 0 then 3 else 4,[⟨.stack,initial.registers .rsp,8⟩]⟩ := by
  by_cases zero : input.count = 0
  · have actual := Sequential.Executes.next (test_step pre (choices 0))
      (Sequential.Executes.next (guard_zero_step pre zero (choices 0) ((choices.drop 1) 0))
        (Sequential.Executes.ret (ret_step pre (atRet_frame pre (choices 0)) rfl
          (((choices.drop 1).drop 1) 0))))
    simpa only [Result.prepend,List.nil_append,finalState,beforeReturn,pre.count,zero,ite_true] using actual
  · have actual := Sequential.Executes.next (test_step pre (choices 0))
      (Sequential.Executes.next (guard_positive_step pre zero (choices 0) ((choices.drop 1) 0))
        (Sequential.Executes.next (store_step pre (choices 0) (((choices.drop 1).drop 1) 0))
          (Sequential.Executes.ret (ret_step pre (stored_frame pre (choices 0))
            (stored_pc variant initial (choices 0)) ((((choices.drop 1).drop 1).drop 1) 0)))))
    simpa only [Result.prepend,List.nil_append,finalState,beforeReturn,pre.count,zero,ite_false] using actual

/-- Actual complete executions, for every full64 input and AF stream. Costs
count decoded instructions including RET, and reads exclude instruction fetch. -/
theorem executions {variant input initial} (pre : Pre (bytes variant) input initial) (choices : Choices) :
    Sequential.Executes choices initial
      ⟨finalState variant initial input.returnAddress ((choices.drop (prefixCost variant)) 0),
        cost variant input.count,[⟨.stack,initial.registers .rsp,8⟩]⟩ := by
  have actual := (prefix_block pre choices).then_executes
    (suffix_execution pre (choices.drop (prefixCost variant)))
  simpa only [Result.prepend,List.nil_append,cost] using actual

theorem execution_exact {variant input initial choices result} (pre : Pre (bytes variant) input initial)
    (actual : Sequential.Executes choices initial result) :
    result.instructions = cost variant input.count ∧ result.reads = [⟨.stack,initial.registers .rsp,8⟩] := by
  have same := Sequential.Executes.fixed_choices_unique (executions pre choices) actual
  cases same
  exact ⟨rfl,rfl⟩

/-- Unchanged present-state admission implies totality and the independent
Post. Exact accounting is exposed separately from the acceptance contract. -/
theorem raw_semantics {variant input initial} (pre : Pre (bytes variant) input initial) :
    AllExecutions initial (fun result => Post input initial result.state ∧
      result.instructions = cost variant input.count ∧
      result.reads = [⟨.stack,initial.registers .rsp,8⟩]) := by
  intro choices
  exact ⟨_,executions pre choices,final_post pre _,rfl,rfl⟩

end EDSL.CountedStoreDirect64
