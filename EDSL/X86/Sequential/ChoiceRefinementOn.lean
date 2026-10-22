/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.ChoiceRefinement

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.X86.Sequential.Engine

variable {Choice Other : Type}
variable {Inv : State → Prop}
variable {left : Choice → State → Except Error Observation}
variable {right : Other → State → Except Error Observation}

/-- At an admitted state, each source choice has a target choice with the
identical full observation or error. No agreement is required outside `Inv`. -/
def SimulatesOn (Inv : State → Prop) (left : Choice → State → Except Error Observation)
    (right : Other → State → Except Error Observation) : Prop :=
  ∀ choice state, Inv state → ∃ other, right other state = left choice state

/-- Actual successful continuing steps preserve the invariant. Return and
syscall boundaries have no continuation and impose no closure obligation. -/
def ContinuesClosed (Inv : State → Prop) (right : Other → State → Except Error Observation) : Prop :=
  ∀ choice state observation, Inv state → right choice state = .ok observation →
    ∀ middle, nextState observation.result = some middle → Inv middle

/-- For any fixed fuel and admitted initial state, a target stream reproduces
the entire source outcome: errors, fuel exhaustion, syscall rejection, or a
successful final state with its exact cost and reads. Closure is required of
the target transition. This does not assert unbounded termination or provide
one stream that works simultaneously for every fuel. -/
theorem SimulatesOn.run (simulation : SimulatesOn Inv left right)
    (closed : ContinuesClosed Inv right) (fuel : Nat)
    (choices : ChoiceStream Choice) (initial : State) (valid : Inv initial) :
    ∃ other : ChoiceStream Other,
      Engine.run right other fuel initial = Engine.run left choices fuel initial := by
  induction fuel generalizing choices initial with
  | zero =>
    obtain ⟨head, _⟩ := simulation (choices 0) initial valid
    exact ⟨fun _ => head, rfl⟩
  | succ fuel induction =>
    obtain ⟨head, same⟩ := simulation (choices 0) initial valid
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
        have nextValid : Inv middle :=
          closed head initial _ valid (same.trans step) middle rfl
        obtain ⟨rest, reproduced⟩ := induction (choices.drop 1) middle nextValid
        refine ⟨ChoiceStream.cons head rest, ?_⟩
        simp [Engine.run, same, step, reproduced]

variable (transition : Choice → State → Except Error Observation)

/-- A supplied choice makes the empty prefix available without requiring an
`Inhabited` instance for the choice domain. -/
theorem Reachable.refl (choice : Choice) (initial : State) :
    Reachable transition initial initial :=
  ⟨fun _ => choice, 0, [], .nil⟩

/-- Extend a reachable prefix by an actual successful continuing observation.
The prefix choices are retained; its next position receives the supplied choice.
Both ordinary and atomic continuations are included. -/
theorem Reachable.continues {initial before middle : State}
    (reachable : Reachable transition initial before) {choice : Choice} {observation : Observation}
    (step : transition choice before = .ok observation)
    (continued : nextState observation.result = some middle) :
    Reachable transition initial middle := by
  obtain ⟨choices, count, reads, block⟩ := reachable
  let extension : ChoiceStream Choice := fun index => if index < count then choices index else choice
  have agree : choices.Agree extension count := by
    intro index bound
    simp [extension, bound]
  have retained : Block transition extension initial before count reads :=
    block.restrict_choices transition agree
  have actual : transition ((extension.drop count) 0) before = .ok observation := by
    simpa [ChoiceStream.drop, extension] using step
  have suffix : Block transition (extension.drop count) before middle 1 observation.reads := by
    rcases observation with ⟨outcome, accesses⟩
    cases outcome with
    | returned final | syscall request => cases continued
    | next after =>
      simp only [nextState, Option.some.injEq] at continued
      subst middle
      simpa only [List.append_nil] using
        (Block.next actual
          (Block.nil : Block transition ((extension.drop count).drop 1) after after 0 []))
    | atomic event after =>
      simp only [nextState, Option.some.injEq] at continued
      subst middle
      simpa only [List.append_nil] using
        (Block.atomic actual
          (Block.nil : Block transition ((extension.drop count).drop 1) after after 0 []))
  exact ⟨extension, count + 1, reads ++ observation.reads, retained.append transition suffix⟩

/-- Reachability from a fixed initial state is closed under the same
transition's actual continuing observations. -/
theorem Reachable.continuesClosed (initial : State) :
    ContinuesClosed (Reachable transition initial) transition := by
  intro choice state observation reachable step middle continued
  exact Reachable.continues transition reachable step continued

end EDSL.X86.Sequential.Engine
