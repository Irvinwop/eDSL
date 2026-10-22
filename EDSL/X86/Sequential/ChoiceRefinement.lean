/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.ExecutionTrace

namespace EDSL.X86.Sequential

/-- Supply the choice at the current instruction before the remaining stream. -/
def ChoiceStream.cons {Choice : Type} (head : Choice) (tail : ChoiceStream Choice) :
    ChoiceStream Choice
  | 0 => head
  | index + 1 => tail index

@[simp] theorem ChoiceStream.cons_zero {Choice : Type} (head : Choice)
    (tail : ChoiceStream Choice) : ChoiceStream.cons head tail 0 = head := rfl

@[simp] theorem ChoiceStream.cons_succ {Choice : Type} (head : Choice)
    (tail : ChoiceStream Choice) (index : Nat) :
    ChoiceStream.cons head tail (index + 1) = tail index := rfl

@[simp] theorem ChoiceStream.cons_drop_one {Choice : Type} (head : Choice)
    (tail : ChoiceStream Choice) : (ChoiceStream.cons head tail).drop 1 = tail := by
  funext index
  change ChoiceStream.cons head tail (1 + index) = tail index
  rw [Nat.one_add]
  rfl

namespace Engine

variable {Choice Other : Type}
variable {left : Choice → State → Except Error Observation}
variable {right : Other → State → Except Error Observation}

/-- Every source choice has a target choice with the identical full observation
or error at the same state. The target choice may depend on both inputs. -/
def Simulates (left : Choice → State → Except Error Observation)
    (right : Other → State → Except Error Observation) : Prop :=
  ∀ choice state, ∃ other, right other state = left choice state

/-- Transfer a finite returning execution without changing its final state,
retired instruction count, or successful operand-read trace. -/
theorem Simulates.executes (simulation : Simulates left right)
    {choices : ChoiceStream Choice} {initial : State} {result : Result}
    (execution : Executes left choices initial result) :
    ∃ other : ChoiceStream Other, Executes right other initial result := by
  induction execution with
  | @ret choices initial final reads step =>
    obtain ⟨head, same⟩ := simulation (choices 0) initial
    exact ⟨fun _ => head, .ret (same.trans step)⟩
  | @next choices initial middle result reads step tail induction =>
    obtain ⟨head, same⟩ := simulation (choices 0) initial
    obtain ⟨rest, execution⟩ := induction
    refine ⟨ChoiceStream.cons head rest, .next (middle := middle) ?_ ?_⟩
    · simpa only [ChoiceStream.cons_zero] using same.trans step
    · simpa only [ChoiceStream.cons_drop_one] using execution
  | @atomic choices initial middle result reads event step tail induction =>
    obtain ⟨head, same⟩ := simulation (choices 0) initial
    obtain ⟨rest, execution⟩ := induction
    refine ⟨ChoiceStream.cons head rest, .atomic (middle := middle) (event := event) ?_ ?_⟩
    · simpa only [ChoiceStream.cons_zero] using same.trans step
    · simpa only [ChoiceStream.cons_drop_one] using execution

/-- Transfer a finite continuing block, including its exact cost and reads. -/
theorem Simulates.block (simulation : Simulates left right)
    {choices : ChoiceStream Choice} {initial final : State} {count : Nat} {reads : List Read}
    (block : Block left choices initial final count reads) :
    ∃ other : ChoiceStream Other, Block right other initial final count reads := by
  induction block with
  | @nil choices state =>
    obtain ⟨head, _⟩ := simulation (choices 0) state
    exact ⟨fun _ => head, .nil⟩
  | @next choices initial middle final count reads rest step tail induction =>
    obtain ⟨head, same⟩ := simulation (choices 0) initial
    obtain ⟨remaining, block⟩ := induction
    refine ⟨ChoiceStream.cons head remaining, .next (middle := middle) ?_ ?_⟩
    · simpa only [ChoiceStream.cons_zero] using same.trans step
    · simpa only [ChoiceStream.cons_drop_one] using block
  | @atomic choices initial middle final count reads rest event step tail induction =>
    obtain ⟨head, same⟩ := simulation (choices 0) initial
    obtain ⟨remaining, block⟩ := induction
    refine ⟨ChoiceStream.cons head remaining, .atomic (middle := middle) (event := event) ?_ ?_⟩
    · simpa only [ChoiceStream.cons_zero] using same.trans step
    · simpa only [ChoiceStream.cons_drop_one] using block

/-- At any fixed fuel, a target stream reproduces the entire source outcome.
This includes exhaustion, transition errors, and rejected syscall boundaries as
well as successful final states, costs, and reads. -/
theorem Simulates.run (simulation : Simulates left right) (fuel : Nat)
    (choices : ChoiceStream Choice) (initial : State) :
    ∃ other : ChoiceStream Other, Engine.run right other fuel initial = Engine.run left choices fuel initial := by
  induction fuel generalizing choices initial with
  | zero =>
    obtain ⟨head, _⟩ := simulation (choices 0) initial
    exact ⟨fun _ => head, rfl⟩
  | succ fuel induction =>
    obtain ⟨head, same⟩ := simulation (choices 0) initial
    cases step : left (choices 0) initial with
    | error fault =>
      refine ⟨fun _ => head, ?_⟩
      simp [Engine.run, same, step]
    | ok observation =>
      rcases observation with ⟨outcome, reads⟩
      cases outcome with
      | returned final =>
        refine ⟨fun _ => head, ?_⟩
        simp [Engine.run, same, step]
      | syscall request =>
        refine ⟨fun _ => head, ?_⟩
        simp [Engine.run, same, step]
      | next middle | atomic event middle =>
        obtain ⟨rest, reproduced⟩ := induction (choices.drop 1) middle
        refine ⟨ChoiceStream.cons head rest, ?_⟩
        simp [Engine.run, same, step, reproduced]

/-- Existential finite returning behavior is preserved by simulation. -/
theorem Simulates.nondet_executes (simulation : Simulates left right)
    {initial : State} {result : Result} (execution : NondetExecutes left initial result) :
    NondetExecutes right initial result := by
  obtain ⟨choices, actual⟩ := execution
  exact simulation.executes actual

/-- Simulations in both directions give equality of finite returning behavior. -/
theorem Simulates.nondet_executes_iff (forward : Simulates left right)
    (backward : Simulates right left) (initial : State) (result : Result) :
    NondetExecutes left initial result ↔ NondetExecutes right initial result :=
  ⟨forward.nondet_executes, backward.nondet_executes⟩

/-- Simulations in both directions give equality of finite continuing behavior,
including the complete read trace and exact retired instruction count. -/
theorem Simulates.blocks_iff (forward : Simulates left right)
    (backward : Simulates right left) (initial final : State) (count : Nat) (reads : List Read) :
    (∃ choices, Block left choices initial final count reads) ↔
      ∃ other, Block right other initial final count reads := by
  constructor
  · rintro ⟨choices, block⟩
    exact forward.block block
  · rintro ⟨other, block⟩
    exact backward.block block

/-- Simulations in both directions give the same set of complete outcomes for
any fixed fuel. This finite statement does not assert transfer of universal
termination or choose a stream that works simultaneously for every fuel. -/
theorem Simulates.run_outcome_iff (forward : Simulates left right)
    (backward : Simulates right left) (fuel : Nat) (initial : State)
    (outcome : Except Error Result) :
    (∃ choices, Engine.run left choices fuel initial = outcome) ↔
      ∃ other, Engine.run right other fuel initial = outcome := by
  constructor
  · rintro ⟨choices, actual⟩
    obtain ⟨other, reproduced⟩ := forward.run fuel choices initial
    exact ⟨other, reproduced.trans actual⟩
  · rintro ⟨other, actual⟩
    obtain ⟨choices, reproduced⟩ := backward.run fuel other initial
    exact ⟨choices, reproduced.trans actual⟩

end Engine
end EDSL.X86.Sequential
