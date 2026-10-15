/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Machine

namespace EDSL.X86

/-- Unbounded finite execution semantics. The fuelled evaluator is an
implementation of this independently stated transition closure. -/
inductive Executes : State → State → Nat → Prop where
  | ret {initial final}
      (transition : step initial = .ok (.returned final)) : Executes initial final 1
  | next {initial middle final count}
      (transition : step initial = .ok (.next middle))
      (tail : Executes middle final count) : Executes initial final (count + 1)

def Diverges (initial : State) : Prop :=
  ∃ trace : Nat → State, trace 0 = initial ∧
    ∀ index, step (trace index) = .ok (.next (trace (index + 1)))

theorem run_sound {fuel : Nat} {initial : State} {result : Execution}
    (success : run fuel initial = .ok result) :
    Executes initial result.state result.instructions := by
  induction fuel generalizing initial result with
  | zero => simp [run] at success
  | succ fuel induction =>
    cases transition : step initial with
    | error error => simp [run, transition] at success
    | ok outcome =>
      cases outcome with
      | syscall request => simp [run, transition] at success
      | returned final =>
        simp [run, transition] at success
        cases success
        exact .ret transition
      | next middle =>
        cases tail : run fuel middle with
        | error error => simp [run, transition, tail] at success
        | ok rest =>
          simp [run, transition, tail] at success
          cases success
          exact .next transition (induction tail)

theorem run_complete {initial final : State} {count fuel : Nat}
    (execution : Executes initial final count) (enough : count ≤ fuel) :
    run fuel initial = .ok ⟨final, count⟩ := by
  induction execution generalizing fuel with
  | ret transition =>
    cases fuel with
    | zero => omega
    | succ fuel => simp [run, transition]
  | @next initial middle final count transition tail induction =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have bound : count ≤ fuel := by omega
      simp [run, transition, induction bound]

theorem Executes.deterministic {initial left right : State} {leftCount rightCount : Nat}
    (first : Executes initial left leftCount)
    (second : Executes initial right rightCount) : left = right ∧ leftCount = rightCount := by
  have firstRun := run_complete first (fuel := leftCount + rightCount) (by omega)
  have secondRun := run_complete second (fuel := leftCount + rightCount) (by omega)
  have equal : (⟨left, leftCount⟩ : Execution) = ⟨right, rightCount⟩ :=
    Except.ok.inj (firstRun.symm.trans secondRun)
  exact ⟨congrArg Execution.state equal, congrArg Execution.instructions equal⟩

theorem Executes.positive {initial final : State} {count : Nat}
    (execution : Executes initial final count) : 1 ≤ count := by
  induction execution with
  | ret _ => omega
  | next _ _ induction => omega

theorem Executes.no_divergence {initial final : State} {count : Nat}
    (execution : Executes initial final count) : ¬ Diverges initial := by
  induction execution with
  | ret transition =>
    rintro ⟨trace, start, steps⟩
    have first := steps 0
    rw [start, transition] at first
    cases first
  | @next initial middle final count transition tail induction =>
    rintro ⟨trace, start, steps⟩
    have first := steps 0
    rw [start, transition] at first
    have middleState : trace 1 = middle := (StepResult.next.inj (Except.ok.inj first)).symm
    apply induction
    refine ⟨fun index => trace (index + 1), middleState, ?_⟩
    intro index
    exact steps (index + 1)

theorem returned_preserves_rax {initial final : State}
    (transition : step initial = .ok (.returned final)) :
    final.registers .rax = initial.registers .rax := by
  cases decoded : decodeAt initial with
  | error error => simp [step, decoded] at transition
  | ok instruction =>
    cases instruction with
    | leaEaxRdiDisp8 displacement => simp [step, decoded] at transition
    | leaEaxRaxDisp8 displacement => simp [step, decoded] at transition
    | movEaxEdi => simp [step, decoded] at transition
    | jrcxz displacement =>
      cases jumped : executeJrcxz initial displacement <;> simp [step, decoded, jumped] at transition
    | loopRcx displacement =>
      cases jumped : executeLoop initial displacement <;> simp [step, decoded, jumped] at transition
    | loadEaxRdi =>
      cases loaded : executeLoad initial <;> simp [step, decoded, loaded] at transition
    | storeEsiRdi =>
      cases stored : executeStore initial <;> simp [step, decoded, stored] at transition
    | mov32 destination value => simp [step, decoded] at transition
    | syscall => simp [step, decoded] at transition
    | ret =>
      cases returned : executeRet initial with
      | error error => simp [step, decoded, returned] at transition
      | ok result =>
        simp [step, decoded, returned] at transition
        cases transition
        cases stack : readWord initial.memory (initial.registers .rsp) with
        | error error => simp [executeRet, stack] at returned
        | ok target =>
          cases valid : canonical target <;> simp [executeRet, stack, valid] at returned
          cases returned
          simp [State.writeRegister]

/-- A lower bound over every successful execution in the supported ISA subset,
not just the fixture: changing RAX requires a non-return step before RET. -/
theorem Executes.changing_rax_costs_two {initial final : State} {count : Nat}
    (execution : Executes initial final count)
    (changed : final.registers .rax ≠ initial.registers .rax) : 2 ≤ count := by
  cases execution with
  | ret transition => exact False.elim (changed (returned_preserves_rax transition))
  | next _ tail => have positive := tail.positive; omega

end EDSL.X86
