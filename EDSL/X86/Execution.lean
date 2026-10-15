/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Machine

namespace EDSL.X86

/-- Unbounded finite execution. Atomic RMW events remain distinguished from
ordinary next instructions in the transition closure. -/
inductive Executes : State → State → Nat → Prop where
  | ret {initial final}
      (transition : step initial = .ok (.returned final)) : Executes initial final 1
  | next {initial middle final count}
      (transition : step initial = .ok (.next middle))
      (tail : Executes middle final count) : Executes initial final (count + 1)
  | atomic {initial middle final count event}
      (transition : step initial = .ok (.atomic event middle))
      (tail : Executes middle final count) : Executes initial final (count + 1)

def StepResult.continuation : StepResult → Option State
  | .next state | .atomic _ state => some state
  | .returned _ | .syscall _ => none

def Continues (before after : State) : Prop :=
  ∃ result, step before = .ok result ∧ result.continuation = some after

def Diverges (initial : State) : Prop :=
  ∃ trace : Nat → State, trace 0 = initial ∧ ∀ index, Continues (trace index) (trace (index + 1))

theorem continuation_of_step {before after : State} {result : StepResult}
    (transition : step before = .ok result) (continued : Continues before after) :
    result.continuation = some after := by
  obtain ⟨other, observed, next⟩ := continued
  have same := Except.ok.inj (transition.symm.trans observed)
  rwa [← same] at next

theorem run_sound {fuel : Nat} {initial : State} {result : Execution}
    (success : run fuel initial = .ok result) : Executes initial result.state result.instructions := by
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
      | atomic event middle =>
        cases tail : run fuel middle with
        | error error => simp [run, transition, tail] at success
        | ok rest =>
          simp [run, transition, tail] at success
          cases success
          exact .atomic transition (induction tail)

theorem run_complete {initial final : State} {count fuel : Nat}
    (execution : Executes initial final count) (enough : count ≤ fuel) :
    run fuel initial = .ok ⟨final, count⟩ := by
  induction execution generalizing fuel with
  | ret transition =>
    cases fuel with
    | zero => omega
    | succ fuel => simp [run, transition]
  | @next initial middle final count transition tail induction
  | @atomic initial middle final count event transition tail induction =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have bound : count ≤ fuel := by omega
      simp [run, transition, induction bound]

theorem Executes.deterministic {initial left right : State} {leftCount rightCount : Nat}
    (first : Executes initial left leftCount) (second : Executes initial right rightCount) :
    left = right ∧ leftCount = rightCount := by
  have firstRun := run_complete first (fuel := leftCount + rightCount) (by omega)
  have secondRun := run_complete second (fuel := leftCount + rightCount) (by omega)
  have equal : (⟨left, leftCount⟩ : Execution) = ⟨right, rightCount⟩ :=
    Except.ok.inj (firstRun.symm.trans secondRun)
  exact ⟨congrArg Execution.state equal, congrArg Execution.instructions equal⟩

theorem Executes.positive {initial final : State} {count : Nat}
    (execution : Executes initial final count) : 1 ≤ count := by
  induction execution with
  | ret _ => omega
  | next _ _ induction | atomic _ _ induction => omega

theorem Executes.no_divergence {initial final : State} {count : Nat}
    (execution : Executes initial final count) : ¬ Diverges initial := by
  induction execution with
  | ret transition =>
    rintro ⟨trace, start, steps⟩
    have impossible := continuation_of_step transition (by simpa [start] using steps 0)
    cases impossible
  | @next initial middle final count transition _ induction =>
    rintro ⟨trace, start, steps⟩
    have same := continuation_of_step transition (by simpa [start] using steps 0)
    have middleState : trace 1 = middle := (Option.some.inj same).symm
    exact induction ⟨fun index => trace (index + 1), middleState, fun index => steps (index + 1)⟩
  | @atomic initial middle final count event transition _ induction =>
    rintro ⟨trace, start, steps⟩
    have same := continuation_of_step transition (by simpa [start] using steps 0)
    have middleState : trace 1 = middle := (Option.some.inj same).symm
    exact induction ⟨fun index => trace (index + 1), middleState, fun index => steps (index + 1)⟩

theorem returned_preserves_rax {initial final : State}
    (transition : step initial = .ok (.returned final)) : final.registers .rax = initial.registers .rax := by
  cases decoded : decodeAt initial with
  | error error => simp [step, decoded] at transition
  | ok instruction =>
    cases instruction with
    | leaEaxRdiDisp8 displacement => simp [step, decoded] at transition
    | leaEaxRaxDisp8 displacement => simp [step, decoded] at transition
    | movEaxEdi => simp [step, decoded] at transition
    | movEaxEsi => simp [step, decoded] at transition
    | exchangeEaxRdi => cases exchanged : executeExchange initial <;> simp [step, decoded, exchanged] at transition
    | fetchAddEaxRdi => cases added : executeFetchAdd initial <;> simp [step, decoded, added] at transition
    | jrcxz displacement => cases jumped : executeJrcxz initial displacement <;> simp [step, decoded, jumped] at transition
    | loopRcx displacement => cases jumped : executeLoop initial displacement <;> simp [step, decoded, jumped] at transition
    | loadEaxRdi => cases loaded : executeLoad initial <;> simp [step, decoded, loaded] at transition
    | storeEsiRdi => cases stored : executeStore initial <;> simp [step, decoded, stored] at transition
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

/-- A bound over the supported ISA subset, including atomic instructions. -/
theorem Executes.changing_rax_costs_two {initial final : State} {count : Nat}
    (execution : Executes initial final count) (changed : final.registers .rax ≠ initial.registers .rax) : 2 ≤ count := by
  cases execution with
  | ret transition => exact False.elim (changed (returned_preserves_rax transition))
  | next _ tail | atomic _ tail => have positive := tail.positive; omega

/-- Execution with exact atomic-event trace retained. Ordinary instruction
steps do not invent atomic events. -/
inductive AtomicExecutes : State → State → Nat → List AtomicEvent → Prop where
  | ret {initial final} (transition : step initial = .ok (.returned final)) : AtomicExecutes initial final 1 []
  | next {initial middle final count events} (transition : step initial = .ok (.next middle))
      (tail : AtomicExecutes middle final count events) : AtomicExecutes initial final (count + 1) events
  | atomic {initial middle final count events event} (transition : step initial = .ok (.atomic event middle))
      (tail : AtomicExecutes middle final count events) : AtomicExecutes initial final (count + 1) (event :: events)

theorem AtomicExecutes.executes {initial final : State} {count : Nat} {events : List AtomicEvent}
    (execution : AtomicExecutes initial final count events) : Executes initial final count := by
  induction execution with
  | ret step => exact .ret step
  | next step _ induction => exact .next step induction
  | atomic step _ induction => exact .atomic step induction

theorem AtomicExecutes.deterministic {initial left right : State} {leftCount rightCount : Nat}
    {leftEvents rightEvents : List AtomicEvent}
    (first : AtomicExecutes initial left leftCount leftEvents)
    (second : AtomicExecutes initial right rightCount rightEvents) :
    left = right ∧ leftCount = rightCount ∧ leftEvents = rightEvents := by
  induction first generalizing right rightCount rightEvents with
  | ret transition =>
    cases second <;> rename_i other
    all_goals simp_all
  | next transition tail induction =>
    cases second with
    | ret other => simp_all
    | next other rest =>
      have same := Except.ok.inj (transition.symm.trans other)
      cases same
      obtain ⟨state, count, events⟩ := induction rest
      exact ⟨state, by omega, events⟩
    | atomic other rest => simp_all
  | atomic transition tail induction =>
    cases second with
    | ret other => simp_all
    | next other rest => simp_all
    | atomic other rest =>
      have same := Except.ok.inj (transition.symm.trans other)
      cases same
      obtain ⟨state, count, events⟩ := induction rest
      exact ⟨state, by omega, by simp [events]⟩

end EDSL.X86
