/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Trace
import EDSL.X86.Sequential.Cutpoints

set_option warningAsError true

namespace EDSL.Grading.Trace.ResourceCutpoints
open EDSL EDSL.X86 EDSL.X86.Sequential

/-- Local cutpoint obligations retain the current ghost world and actual
registered effects. The decreasing rank depends on the machine state; a
resource-dependent ranking function is outside this interface. -/
structure Certificate {Location : Type u} {Ghost : Type}
    (flow : X86.Sequential.Cutpoints.Layout Location)
    (rules : Rules Ghost) (Post : State → Prop) where
  Inv : Location → Ghost → State → Prop
  rank : Location → State → Nat
  Interior : Location → Nat → Location → Ghost → State → Prop
  start : ∀ cut shared state, flow.cutpoint cut = true → Inv cut shared state →
    Interior cut (rank cut state) cut shared state
  localVC : ∀ source budget node shared state,
    Interior source budget node shared state →
    rules.Current shared state ∧
      ∃ instruction, Sequential.decodeAt state = .ok instruction ∧
        ∀ af, ∃ observation evolved,
          step af state = .ok observation ∧
          (∀ read ∈ observation.reads,
            rules.ReadAllowed shared state read ∧ OperandReadSucceeds state read) ∧
          rules.Effect shared state instruction observation evolved ∧
          match observation.result with
          | .returned final => rules.Current evolved final ∧ Post final
          | .next middle => ∃ dest, flow.Edge node dest ∧
              ((flow.cutpoint dest = true ∧ Inv dest evolved middle ∧ rank dest middle < budget) ∨
               (flow.cutpoint dest = false ∧ Interior source budget dest evolved middle))
          | .atomic _ _ | .syscall _ => False

variable {Location : Type u} {Ghost : Type}
  {flow : X86.Sequential.Cutpoints.Layout Location} {rules : Rules Ghost}
  {Post : State → Prop}

/-- Erasure is used only for the machine termination argument. A separate
policy proof below keeps every current world and actual registered effect. -/
def Certificate.machine (cert : Certificate flow rules Post) :
    X86.Sequential.Cutpoints.Certificate flow Post (fun _ _ => True) where
  Inv node state := ∃ shared, cert.Inv node shared state
  rank := cert.rank
  Interior source budget node state := ∃ shared, cert.Interior source budget node shared state
  start cut state isCut valid := by
    obtain ⟨shared, valid⟩ := valid
    exact ⟨shared, cert.start cut shared state isCut valid⟩
  localVC source budget node state valid af := by
    obtain ⟨shared, valid⟩ := valid
    obtain ⟨_, _, _, enabled⟩ := cert.localVC source budget node shared state valid
    obtain ⟨observation, evolved, actual, _, _, progress⟩ := enabled af
    refine ⟨observation, actual, fun _ _ => True.intro, ?_⟩
    cases outcome : observation.result with
    | returned final =>
      simp only [outcome] at progress ⊢
      exact progress.2
    | next middle =>
      simp only [outcome] at progress ⊢
      obtain ⟨dest, edge, atCut | interior⟩ := progress
      · exact ⟨dest, edge, Or.inl ⟨atCut.1, ⟨evolved, atCut.2.1⟩, atCut.2.2⟩⟩
      · exact ⟨dest, edge, Or.inr ⟨interior.1, ⟨evolved, interior.2⟩⟩⟩
    | atomic event middle => simp only [outcome] at progress
    | syscall request => simp only [outcome] at progress

/-- Every actual continuation carries the same evolved world into its next
interior or cutpoint. Initial invariant evidence and the local obligations
derive the policy; a future execution is not a separate premise. -/
theorem Certificate.policy (cert : Certificate flow rules Post)
    {entry : Location} {seed : Ghost} {initial : State}
    (isCut : flow.cutpoint entry = true) (valid : cert.Inv entry seed initial) :
    Policy rules seed initial := by
  refine ⟨(fun shared state => ∃ source budget node,
    cert.Interior source budget node shared state),
    ⟨entry, cert.rank entry initial, entry, cert.start entry seed initial isCut valid⟩, ?_⟩
  intro shared before inside
  obtain ⟨source, budget, node, inside⟩ := inside
  obtain ⟨current, instruction, decoded, enabled⟩ := cert.localVC source budget node shared before inside
  refine ⟨current, instruction, decoded, ?_⟩
  intro af
  obtain ⟨observation, evolved, actual, permission, effect, progress⟩ := enabled af
  refine ⟨observation, evolved, actual, permission, effect, ?_⟩
  cases outcome : observation.result with
  | returned final =>
    simp only [outcome] at progress ⊢
    exact progress.1
  | next middle =>
    simp only [outcome] at progress ⊢
    obtain ⟨dest, _, atCut | interior⟩ := progress
    · exact ⟨dest, cert.rank dest middle, dest,
        cert.start dest evolved middle atCut.1 atCut.2.1⟩
    · exact ⟨source, budget, dest, interior.2⟩
  | atomic event middle => simp only [outcome] at progress
  | syscall request => simp only [outcome] at progress

/-- Actual all-choice termination, independent Post, and the coherent lifted
OS path follow together. Retired instruction cost includes RET; kernel work,
physical time and concurrent interference are outside this sequential result. -/
theorem Certificate.execution (cert : Certificate flow rules Post)
    {entry : Location} {seed : Ghost} {initial : State}
    (isCut : flow.cutpoint entry = true) (valid : cert.Inv entry seed initial)
    (choices : Choices) :
    ∃ result evolved, Sequential.Executes choices initial result ∧ Post result.state ∧
      LiftedExecutes rules choices initial seed result evolved ∧
      rules.Current evolved result.state ∧
      result.instructions ≤ (flow.maxDepth + 1) * (cert.rank entry initial + 1) := by
  obtain ⟨result, actual, post, bound⟩ := cert.machine.execution isCut ⟨seed, valid⟩ choices
  obtain ⟨evolved, lifted, current⟩ := policy_return (cert.policy isCut valid) actual
  exact ⟨result, evolved, actual, post, lifted, current, bound⟩

end EDSL.Grading.Trace.ResourceCutpoints
