/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.Comparison64.Machine

set_option warningAsError true

namespace EDSL.Comparison64.Client
open X86 X86.Sequential

/-- The arithmetic assertion uses mathematical signed/unsigned order; no
instruction, flags, selection expression or cost appears in its specification. -/
theorem selected_result {variant operation input initial}
    (pre : Pre (bytes variant operation) input initial) :
    MathematicalResult operation input.left input.right
      ((thirdState variant operation initial).registers .rax) := by
  cases variant <;> cases operation <;>
    simp only [thirdState,select,secondState,firstState,compare,copy,selectSource,copySource,
      compareLeft,compareRight,reversed,condition,State.writeRegister,reduceCtorEq,
      ite_false,ite_true,pre.left,pre.right,
      Condition.cmp_aboveEqual,Condition.cmp_belowEqual,Condition.cmp_greaterEqual,
      Condition.cmp_above,Condition.cmp_below,Condition.cmp_greater] <;>
    split <;> rename_i order <;>
    simp_all [MathematicalResult,Nat.max_def,Nat.min_def,Int.max_def] <;> omega

theorem final_post {variant operation input initial}
    (pre : Pre (bytes variant operation) input initial) :
    Post operation input initial (finalState variant operation initial input.returnAddress) := by
  have frame := stage_frame variant operation .ret initial
  change Frame initial (thirdState variant operation initial) at frame
  refine ⟨?_,frame.memory,rfl,?_,?_,frame.flags⟩
  · simpa only [finalState,finish,State.writeRegister,reduceCtorEq,ite_false] using selected_result pre
  · simp only [finalState,finish,State.writeRegister,ite_true]
    exact congrArg (· + 8) (frame.registers .rsp (by decide))
  · intro register member
    have notStack : register ≠ .rsp := by
      intro same; subst register; simp [calleeSaved] at member
    have notResult : register ≠ .rax := by
      intro same; subst register; simp [calleeSaved] at member
    simpa only [finalState,finish,State.writeRegister,notStack,ite_false] using
      frame.registers register notResult

/-- Every full64 input and every AF stream executes the four actual decoded
instructions, ending at the supplied caller address with one original STACK8. -/
theorem executions {variant operation input initial}
    (pre : Pre (bytes variant operation) input initial) (choices : Choices) :
    Sequential.Executes choices initial
      ⟨finalState variant operation initial input.returnAddress,4,
        [⟨.stack,initial.registers .rsp,8⟩]⟩ := by
  have execution := Sequential.Executes.next (step_stage pre .first (choices 0))
    (Sequential.Executes.next (step_stage pre .second ((choices.drop 1) 0))
      (Sequential.Executes.next (step_stage pre .select (((choices.drop 1).drop 1) 0))
        (Sequential.Executes.ret (step_stage pre .ret ((((choices.drop 1).drop 1).drop 1) 0)))))
  simpa only [stageState,observation,Result.prepend,List.nil_append] using execution

theorem raw_semantics {variant operation input initial}
    (pre : Pre (bytes variant operation) input initial) :
    AllExecutions initial (fun result =>
      Post operation input initial result.state ∧ result.instructions = 4 ∧
        result.reads = [⟨.stack,initial.registers .rsp,8⟩]) := by
  intro choices
  exact ⟨_,executions pre choices,final_post pre,rfl,rfl⟩

theorem execution_exact {variant operation input initial choices result}
    (pre : Pre (bytes variant operation) input initial)
    (execution : Sequential.Executes choices initial result) :
    result = ⟨finalState variant operation initial input.returnAddress,4,
      [⟨.stack,initial.registers .rsp,8⟩]⟩ :=
  execution.fixed_choices_unique (executions pre choices)

/-- Ghost locations describe all actual continuing pre-states; they do not
assume that a later execution succeeds or that an instruction is read-only. -/
def Prefix (variant : Variant) (operation : Operation) (initial before : State) : Prop :=
  ∃ stage, before = stageState variant operation stage initial

theorem prefix_continues {variant operation input initial before after af outcome reads}
    (pre : Pre (bytes variant operation) input initial)
    (inside : Prefix variant operation initial before)
    (actual : Sequential.step af before = .ok ⟨outcome,reads⟩)
    (next : nextState outcome = some after) : Prefix variant operation initial after := by
  obtain ⟨stage,rfl⟩ := inside
  have same := Except.ok.inj ((step_stage pre stage af).symm.trans actual)
  cases stage with
  | first =>
    cases same
    cases next
    exact ⟨.second,rfl⟩
  | second =>
    cases same
    cases next
    exact ⟨.select,rfl⟩
  | select =>
    cases same
    cases next
    exact ⟨.ret,rfl⟩
  | ret =>
    cases same
    cases next

theorem prefix_block {variant operation input initial before final choices count reads}
    (pre : Pre (bytes variant operation) input initial)
    (inside : Prefix variant operation initial before)
    (block : Sequential.Block choices before final count reads) :
    Prefix variant operation initial final := by
  induction block with
  | nil => exact inside
  | next step tail induction | atomic step tail induction =>
    exact induction (prefix_continues pre inside step rfl)

theorem prefix_reachable {variant operation input initial before}
    (pre : Pre (bytes variant operation) input initial)
    (reachable : Sequential.Reachable initial before) :
    Prefix variant operation initial before := by
  obtain ⟨_,_,_,block⟩ := reachable
  exact prefix_block pre ⟨.first,rfl⟩ block

/-- Prefix-sensitive read-only evidence retains complete original RAM and
authorizes only the actual, successful original caller-slot read. -/
theorem raw_policy {variant operation input initial}
    (pre : Pre (bytes variant operation) input initial) : RawPolicy initial := by
  intro before reachable
  obtain ⟨stage,rfl⟩ := prefix_reachable pre reachable
  have frame := stage_frame variant operation stage initial
  refine ⟨frame.memory,⟨instruction variant operation stage,stage_decoded pre stage,?_⟩,?_⟩
  · cases variant <;> cases stage <;> rfl
  · intro af
    refine ⟨observation variant operation stage initial input.returnAddress,step_stage pre stage af,?_,?_⟩
    · intro read member
      cases stage with
      | first | second | select => cases member
      | ret =>
        simp only [observation,List.mem_singleton] at member
        subst read
        refine ⟨⟨rfl,rfl,rfl⟩,rfl,input.returnAddress,?_⟩
        rw [frame.memory]
        exact pre.stack
    · cases stage with
      | first => exact (stage_frame variant operation .second initial).memory.trans frame.memory.symm
      | second => exact (stage_frame variant operation .select initial).memory.trans frame.memory.symm
      | select => exact (stage_frame variant operation .ret initial).memory.trans frame.memory.symm
      | ret => rfl

end EDSL.Comparison64.Client
