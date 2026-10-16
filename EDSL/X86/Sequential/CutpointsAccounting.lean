/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.CutpointsSafety

namespace EDSL.X86.Sequential.Cutpoints

/-- Optional exact accounting. Totality is supplied separately by the checked
cutpoint/depth obligations. These local equalities account for each actual
retired instruction and operand-read prefix, including RET. -/
structure Accounting {Location : Type u} {flow : Layout Location} {Post : State → Prop}
    {AllowedRead : State → Read → Prop} (certificate : Certificate flow Post AllowedRead) where
  cost : Location → State → Nat
  reads : Location → State → List Read
  localStep : ∀ source budget node initial, certificate.Interior source budget node initial →
    ∀ af observation, Sequential.step af initial = .ok observation →
      match observation.result with
      | .returned _ => cost node initial = 1 ∧ reads node initial = observation.reads
      | .next middle => ∃ dest,
          (∃ source budget, certificate.Interior source budget dest middle) ∧
          cost node initial = 1 + cost dest middle ∧
          reads node initial = observation.reads ++ reads dest middle
      | .atomic _ _ | .syscall _ => False

variable {Location : Type u} {flow : Layout Location} {Post : State → Prop}
  {AllowedRead : State → Read → Prop} {certificate : Certificate flow Post AllowedRead}

/-- Accounting follows a given actual execution; it assumes no fuel success.
The next annotated node is justified by the supplied local accounting proof. -/
theorem Accounting.execution_exact (account : Accounting certificate)
    {choices : Choices} {initial : State} {result : Result}
    (execution : Executes choices initial result) {node : Location}
    (inside : ∃ source budget, certificate.Interior source budget node initial) :
    result.instructions = account.cost node initial ∧ result.reads = account.reads node initial := by
  induction execution generalizing node with
  | @ret choices initial final reads step =>
    obtain ⟨source, budget, interior⟩ := inside
    have after := account.localStep source budget node initial interior (choices 0) _ step
    exact ⟨after.1.symm, after.2.symm⟩
  | @next choices initial middle result reads step tail induction =>
    obtain ⟨source, budget, interior⟩ := inside
    obtain ⟨dest, nextInside, cost, accesses⟩ :=
      account.localStep source budget node initial interior (choices 0) _ step
    obtain ⟨restCost, restReads⟩ := induction nextInside
    exact ⟨by simpa only [Result.prepend, restCost] using cost.symm,
      by simpa only [Result.prepend, restReads] using accesses.symm⟩
  | @atomic choices initial middle result reads event step tail induction =>
    obtain ⟨source, budget, interior⟩ := inside
    exact False.elim (account.localStep source budget node initial interior (choices 0) _ step)

/-- Exact cost and ordered reads compose with constructive all-choice totality.
The exact cost can consequently serve as evaluator fuel. -/
theorem Accounting.sound (account : Accounting certificate)
    {entry : Location} {initial : State} (isCut : flow.cutpoint entry = true)
    (admitted : certificate.Inv entry initial) (choices : Choices) :
    ∃ result, run choices (account.cost entry initial) initial = .ok result ∧
      Post result.state ∧ result.instructions = account.cost entry initial ∧
      result.reads = account.reads entry initial := by
  obtain ⟨result, execution, post, _⟩ := certificate.execution isCut admitted choices
  have inside := certificate.start entry initial isCut admitted
  obtain ⟨cost, accesses⟩ := account.execution_exact execution ⟨entry, certificate.rank entry initial, inside⟩
  exact ⟨result, run_complete execution (Nat.le_of_eq cost), post, cost, accesses⟩

end EDSL.X86.Sequential.Cutpoints
