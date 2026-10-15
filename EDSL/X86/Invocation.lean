/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Execution

namespace EDSL.X86

structure Invocation where
  request : SyscallRequest
  instructions : Nat

/-- Evaluate to the first syscall request, not through the kernel or SYSRET. -/
def runToSyscall : Nat → State → Except Error Invocation
  | 0, _ => .error .exhaustedFuel
  | fuel + 1, state => do
    match ← step state with
    | .syscall request => return ⟨request, 1⟩
    | .returned _ => throw .unexpectedReturn
    | .next next =>
      let result ← runToSyscall fuel next
      return { result with instructions := result.instructions + 1 }

/-- Unbounded finite execution to an external request boundary. -/
inductive Invokes : State → SyscallRequest → Nat → Prop where
  | syscall {initial request}
      (transition : step initial = .ok (.syscall request)) : Invokes initial request 1
  | next {initial middle request count}
      (transition : step initial = .ok (.next middle))
      (tail : Invokes middle request count) : Invokes initial request (count + 1)

theorem runToSyscall_sound {fuel : Nat} {initial : State} {result : Invocation}
    (success : runToSyscall fuel initial = .ok result) :
    Invokes initial result.request result.instructions := by
  induction fuel generalizing initial result with
  | zero => simp [runToSyscall] at success
  | succ fuel induction =>
    cases transition : step initial with
    | error error => simp [runToSyscall, transition] at success
    | ok outcome =>
      cases outcome with
      | returned final => simp [runToSyscall, transition] at success
      | syscall request =>
        simp [runToSyscall, transition] at success
        cases success
        exact .syscall transition
      | next middle =>
        cases tail : runToSyscall fuel middle with
        | error error => simp [runToSyscall, transition, tail] at success
        | ok rest =>
          simp [runToSyscall, transition, tail] at success
          cases success
          exact .next transition (induction tail)

theorem runToSyscall_complete {initial : State} {request : SyscallRequest} {count fuel : Nat}
    (execution : Invokes initial request count) (enough : count ≤ fuel) :
    runToSyscall fuel initial = .ok ⟨request, count⟩ := by
  induction execution generalizing fuel with
  | syscall transition =>
    cases fuel with
    | zero => omega
    | succ fuel => simp [runToSyscall, transition]
  | @next initial middle request count transition tail induction =>
    cases fuel with
    | zero => omega
    | succ fuel => simp [runToSyscall, transition, induction (by omega : count ≤ fuel)]

theorem Invokes.deterministic {initial : State} {left right : SyscallRequest}
    {leftCount rightCount : Nat} (first : Invokes initial left leftCount)
    (second : Invokes initial right rightCount) : left = right ∧ leftCount = rightCount := by
  have firstRun := runToSyscall_complete first (fuel := leftCount + rightCount) (by omega)
  have secondRun := runToSyscall_complete second (fuel := leftCount + rightCount) (by omega)
  have equal : (⟨left, leftCount⟩ : Invocation) = ⟨right, rightCount⟩ :=
    Except.ok.inj (firstRun.symm.trans secondRun)
  exact ⟨congrArg Invocation.request equal, congrArg Invocation.instructions equal⟩

theorem Invokes.no_user_divergence {initial : State} {request : SyscallRequest} {count : Nat}
    (execution : Invokes initial request count) : ¬ Diverges initial := by
  induction execution with
  | syscall transition =>
    rintro ⟨trace, start, steps⟩
    have first := steps 0
    rw [start, transition] at first
    cases first
  | @next initial middle request count transition tail induction =>
    rintro ⟨trace, start, steps⟩
    have first := steps 0
    rw [start, transition] at first
    have middleState : trace 1 = middle := (StepResult.next.inj (Except.ok.inj first)).symm
    apply induction
    exact ⟨fun index => trace (index + 1), middleState, fun index => steps (index + 1)⟩

theorem Invokes.positive {initial : State} {request : SyscallRequest} {count : Nat}
    (execution : Invokes initial request count) : 1 ≤ count := by
  induction execution with
  | syscall _ => omega
  | next _ _ induction => omega

theorem syscall_uses_user_state {initial : State} {request : SyscallRequest}
    (transition : step initial = .ok (.syscall request)) : request.user = initial := by
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
    | mov32 destination value => simp [step, decoded] at transition
    | loadEaxRdi => cases loaded : executeLoad initial <;> simp [step, decoded, loaded] at transition
    | storeEsiRdi => cases stored : executeStore initial <;> simp [step, decoded, stored] at transition
    | ret => cases returned : executeRet initial <;> simp [step, decoded, returned] at transition
    | syscall =>
      simp [step, decoded] at transition
      cases transition
      rfl

/-- No supported ordinary step changes both syscall number and first argument
registers. The statement covers all successful steps, not just a fixture. -/
theorem next_preserves_rax_or_rdi {initial middle : State}
    (transition : step initial = .ok (.next middle)) :
    middle.registers .rax = initial.registers .rax ∨
      middle.registers .rdi = initial.registers .rdi := by
  cases decoded : decodeAt initial with
  | error error => simp [step, decoded] at transition
  | ok instruction =>
    cases instruction with
    | leaEaxRdiDisp8 displacement =>
      simp [step, decoded] at transition
      cases transition
      exact Or.inr (by simp [executeLea, State.writeRegister])
    | leaEaxRaxDisp8 displacement =>
      simp [step, decoded] at transition
      cases transition
      exact Or.inr (by simp [executeLeaRax, State.writeRegister])
    | movEaxEdi =>
      simp [step, decoded] at transition
      cases transition
      exact Or.inr (by simp [executeMovEaxEdi, State.writeRegister])
    | jrcxz displacement =>
      cases jumped : executeJrcxz initial displacement with
      | error error => simp [step, decoded, jumped] at transition
      | ok result =>
        simp [step, decoded, jumped] at transition
        cases transition
        exact Or.inl (congrFun (executeShortBranch_registers jumped) .rax)
    | loopRcx displacement =>
      cases jumped : executeLoop initial displacement with
      | error error => simp [step, decoded, jumped] at transition
      | ok result =>
        simp [step, decoded, jumped] at transition
        cases transition
        have registers := congrFun (executeShortBranch_registers jumped) .rax
        exact Or.inl (by simpa [State.writeRegister] using registers)
    | mov32 destination value =>
      simp [step, decoded] at transition
      cases transition
      by_cases same : destination = .rax
      · subst destination
        exact Or.inr (by simp [executeMov32, State.writeRegister])
      · exact Or.inl (by simp [executeMov32, State.writeRegister, Ne.symm same])
    | loadEaxRdi =>
      cases loaded : loadDWord initial.memory (initial.registers .rdi) with
      | error error => simp [step, decoded, executeLoad, loaded] at transition
      | ok value =>
        simp [step, decoded, executeLoad, loaded] at transition
        cases transition
        exact Or.inr (by simp [State.writeRegister])
    | storeEsiRdi =>
      cases stored : storeDWord initial.memory (initial.registers .rdi)
          ((initial.registers .rsi).setWidth 32) with
      | error error => simp [step, decoded, executeStore, stored] at transition
      | ok memory =>
        simp [step, decoded, executeStore, stored] at transition
        cases transition
        exact Or.inl rfl
    | ret => cases returned : executeRet initial <;> simp [step, decoded, returned] at transition
    | syscall => simp [step, decoded] at transition

theorem Invokes.changing_two_registers_costs_three {initial : State}
    {request : SyscallRequest} {count : Nat} (execution : Invokes initial request count)
    (changedNumber : request.user.registers .rax ≠ initial.registers .rax)
    (changedArgument : request.user.registers .rdi ≠ initial.registers .rdi) : 3 ≤ count := by
  cases execution with
  | syscall transition =>
    exact False.elim (changedNumber (by rw [syscall_uses_user_state transition]))
  | @next initial middle request count transition tail =>
    cases tail with
    | syscall called =>
      have stateEq := syscall_uses_user_state called
      rcases next_preserves_rax_or_rdi transition with sameNumber | sameArgument
      · exact False.elim (changedNumber (by rw [stateEq]; exact sameNumber))
      · exact False.elim (changedArgument (by rw [stateEq]; exact sameArgument))
    | next _ tail => have positive := tail.positive; omega

end EDSL.X86
