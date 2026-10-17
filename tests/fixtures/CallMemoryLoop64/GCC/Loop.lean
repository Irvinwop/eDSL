/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.CallMemoryLoop64.GCC.Body
import tests.fixtures.CallMemoryLoop64.GCC.Exit

set_option warningAsError true

namespace EDSL.CallMemoryLoop64.GCC
open X86 OS

/-- Natural remaining-count induction composes the actual mixed executions.
Every recursive call receives the evolved world and the AF stream dropped by
the preceding ten actual instructions. The original descriptor stays frozen. -/
theorem loop {resource : Resources} {initial state : State} {shared : Shared} {remaining : Nat}
    (same : resource.descriptor.frame.call.bytes = text)
    (capacity : 32 ≤ resource.descriptor.frame.capacity)
    (current : Current resource.descriptor shared state)
    (inv : Invariant resource initial state remaining) (choices : CallReturn.Choices) :
    ∃ evolved result, CoveredExecution resource.descriptor choices shared state evolved result ∧
      Output resource initial result.state ∧ result.instructions = 7 + 10 * remaining := by
  induction remaining generalizing shared state choices with
  | zero =>
      obtain ⟨result, execution, cost, output⟩ := exit same capacity current inv choices
      exact ⟨shared, result, execution, output, cost⟩
  | succ remaining induction =>
      obtain ⟨middleWorld, middle, reads, history, middleCurrent, middleInv⟩ :=
        body same capacity current inv choices
      obtain ⟨evolved, result, execution, output, cost⟩ :=
        induction middleCurrent middleInv (choices.drop 10)
      refine ⟨evolved, result.prepend 10 reads, history.then_execution execution, output, ?_⟩
      simp only [Sequential.Result.prepend, Nat.mul_succ]
      omega

end EDSL.CallMemoryLoop64.GCC
