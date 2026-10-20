/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Execution

namespace EDSL.X86.Sequential.Cutpoints

universe u

/-- Static control-flow information. Every edge to an ordinary node decreases
its finite depth; only an edge into a cutpoint can reset that depth. -/
structure Layout (Location : Type u) where
  cutpoint : Location → Bool
  depth : Location → Nat
  maxDepth : Nat
  Edge : Location → Location → Prop
  depth_bound : ∀ node, depth node ≤ maxDepth
  depth_decrease : ∀ {node dest}, Edge node dest → cutpoint dest = false → depth dest < depth node

/-- Local obligations for the actual sequential machine. `Post` and
`AllowedRead` are supplied independently of the certificate. The interior ghost
retains the source cutpoint and its original dynamic budget across a segment.
Atomic and syscall boundaries are deliberately outside this profile. -/
structure Certificate {Location : Type u} (flow : Layout Location)
    (Post : State → Prop) (AllowedRead : State → Read → Prop) where
  Inv : Location → State → Prop
  rank : Location → State → Nat
  Interior : Location → Nat → Location → State → Prop
  start : ∀ cut state, flow.cutpoint cut = true → Inv cut state →
    Interior cut (rank cut state) cut state
  localVC : ∀ source budget node state, Interior source budget node state → ∀ af,
    ∃ observation, Sequential.step af state = .ok observation ∧
      (∀ read ∈ observation.reads, AllowedRead state read) ∧
      match observation.result with
      | .returned final => Post final
      | .next middle => ∃ dest, flow.Edge node dest ∧
          ((flow.cutpoint dest = true ∧ Inv dest middle ∧ rank dest middle < budget) ∨
           (flow.cutpoint dest = false ∧ Interior source budget dest middle))
      | .atomic _ _ | .syscall _ => False

variable {Location : Type u} {flow : Layout Location} {Post : State → Prop}
  {AllowedRead : State → Read → Prop}

/-- One actual nonempty segment ends at RET or its next cutpoint. Its bound is
static depth, independent of dynamic rank and the number of input elements. -/
def Segment (cert : Certificate flow Post AllowedRead) (_source : Location) (budget : Nat)
    (node : Location) (choices : Choices) (initial : State) : Prop :=
  (∃ result, Executes choices initial result ∧ Post result.state ∧
      result.instructions ≤ flow.depth node + 1) ∨
  (∃ dest middle count reads, Block choices initial middle count reads ∧
      0 < count ∧ count ≤ flow.depth node + 1 ∧ flow.cutpoint dest = true ∧
        cert.Inv dest middle ∧ cert.rank dest middle < budget)

/-- The first induction composes only local machine steps. In particular, this
premise contains neither a future successful evaluator run nor a custom graph
evaluator whose relation to the real machine must be trusted. -/
theorem Certificate.segment (cert : Certificate flow Post AllowedRead)
    {source : Location} {budget : Nat} {node : Location} {initial : State}
    (valid : cert.Interior source budget node initial) (choices : Choices) :
    Segment cert source budget node choices initial := by
  have compose : ∀ depth, ∀ node, flow.depth node = depth → ∀ initial,
      cert.Interior source budget node initial → ∀ choices,
        Segment cert source budget node choices initial := by
    intro depth
    induction depth using Nat.strongRecOn with
    | ind depth induction =>
      intro node value initial valid choices
      obtain ⟨⟨outcome, reads⟩, actual, _, after⟩ :=
        cert.localVC source budget node initial valid (choices 0)
      cases outcome with
      | returned final =>
        exact .inl ⟨⟨final, 1, reads⟩, .ret actual, after, by simp⟩
      | atomic event middle => exact False.elim after
      | syscall request => exact False.elim after
      | next middle =>
        obtain ⟨dest, edge, cut | interior⟩ := after
        · obtain ⟨isCut, invariant, decreased⟩ := cut
          exact .inr ⟨dest, middle, 1, reads, by simpa using Block.next actual Block.nil,
            by omega, by omega, isCut, invariant, decreased⟩
        · obtain ⟨notCut, nextValid⟩ := interior
          have smaller := flow.depth_decrease edge notCut
          have next := induction (flow.depth dest) (by omega) dest rfl middle nextValid (choices.drop 1)
          rcases next with ⟨result, execution, post, bound⟩ |
            ⟨last, final, count, rest, block, positive, bound, isCut, invariant, decreased⟩
          · exact .inl ⟨result.prepend 1 reads, .next actual execution, post,
              by simp only [Result.prepend]; omega⟩
          · exact .inr ⟨last, final, count + 1, reads ++ rest, .next actual block,
              by omega, by omega, isCut, invariant, decreased⟩
  exact compose (flow.depth node) node rfl initial valid choices

/-- Dynamic rank decreases only at cutpoints. The second induction combines the
actual bounded segments, dropping the choice stream by each actual block cost. -/
theorem Certificate.execution (cert : Certificate flow Post AllowedRead)
    {entry : Location} {initial : State} (isCut : flow.cutpoint entry = true)
    (valid : cert.Inv entry initial) (choices : Choices) :
    ∃ result, Executes choices initial result ∧ Post result.state ∧
      result.instructions ≤ (flow.maxDepth + 1) * (cert.rank entry initial + 1) := by
  have compose : ∀ budget, ∀ entry initial, cert.rank entry initial = budget →
      flow.cutpoint entry = true → cert.Inv entry initial → ∀ choices,
      ∃ result, Executes choices initial result ∧ Post result.state ∧
        result.instructions ≤ (flow.maxDepth + 1) * (budget + 1) := by
    intro budget
    induction budget using Nat.strongRecOn with
    | ind budget induction =>
      intro entry initial value isCut valid choices
      have start := cert.start entry initial isCut valid
      rcases cert.segment start choices with ⟨result, execution, post, bound⟩ |
        ⟨dest, middle, count, reads, block, _, bound, destCut, invariant, decreased⟩
      · refine ⟨result, execution, post, ?_⟩
        have staticBound := flow.depth_bound entry
        have positive : 1 ≤ budget + 1 := by omega
        have multiply := Nat.mul_le_mul_left (flow.maxDepth + 1) positive
        omega
      · obtain ⟨result, execution, post, cost⟩ := induction (cert.rank dest middle)
          (by omega) dest middle rfl destCut invariant (choices.drop count)
        refine ⟨result.prepend count reads, block.then_executes execution, post, ?_⟩
        have staticBound := flow.depth_bound entry
        have rankBound : cert.rank dest middle + 1 ≤ budget := by omega
        have multiply := Nat.mul_le_mul_left (flow.maxDepth + 1) rankBound
        simp only [Result.prepend]
        rw [Nat.mul_add, Nat.mul_one]
        omega
  exact compose (cert.rank entry initial) entry initial rfl isCut valid choices

/-- Run with the proved global bound; execution may return before all fuel is
spent. The bound is on retired model instructions, not time or micro-operations. -/
theorem Certificate.total (cert : Certificate flow Post AllowedRead)
    {entry : Location} {initial : State} (isCut : flow.cutpoint entry = true)
    (valid : cert.Inv entry initial) (choices : Choices) :
    ∃ result, run choices ((flow.maxDepth + 1) * (cert.rank entry initial + 1)) initial = .ok result ∧
      Post result.state ∧ result.instructions ≤ (flow.maxDepth + 1) * (cert.rank entry initial + 1) := by
  obtain ⟨result, execution, post, bound⟩ := cert.execution isCut valid choices
  exact ⟨result, run_complete execution bound, post, bound⟩

theorem Certificate.all_executions (cert : Certificate flow Post AllowedRead)
    {entry : Location} {initial : State} (isCut : flow.cutpoint entry = true)
    (valid : cert.Inv entry initial) :
    AllExecutions initial (fun result => Post result.state ∧
      result.instructions ≤ (flow.maxDepth + 1) * (cert.rank entry initial + 1)) :=
  fun choices => cert.execution isCut valid choices

theorem Certificate.no_divergence (cert : Certificate flow Post AllowedRead)
    {entry : Location} {initial : State} (isCut : flow.cutpoint entry = true)
    (valid : cert.Inv entry initial) : ¬ Diverges initial :=
  (cert.all_executions isCut valid).no_divergence

theorem Certificate.no_fault_prefix (cert : Certificate flow Post AllowedRead)
    {entry : Location} {initial : State} (isCut : flow.cutpoint entry = true)
    (valid : cert.Inv entry initial) (choices : Choices) {fuel : Nat} {error : Error}
    (fault : run choices fuel initial = .error error) : error = .exhaustedFuel :=
  (cert.all_executions isCut valid).no_fault_prefix choices fault

end EDSL.X86.Sequential.Cutpoints
