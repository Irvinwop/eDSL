/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Examples.Compiler.Increment

namespace EDSL.Certificate
open X86 Examples.Compiler

/-- First deliberately narrow contract profile. Other encodings are unsupported,
not automatically incorrect. Soundness below is about machine execution. -/
def acceptsIncrement (candidate : List Byte) : Bool :=
  decide (candidate = Increment.bytes)

theorem increment_sound (candidate : List Byte)
    (accepted : acceptsIncrement candidate = true)
    (initial : State) (returnAddress : Word)
    (code : CodeAt initial.memory initial.rip candidate)
    (stack : readWord initial.memory (initial.registers .rsp) = .ok returnAddress)
    (returnValid : canonical returnAddress = true) :
    Executes initial (Increment.finalState initial returnAddress) 2 ∧
    ¬ Diverges initial ∧
    ∀ final count, Executes initial final count →
      final = Increment.finalState initial returnAddress ∧ count = 2 := by
  have equal : candidate = Increment.bytes := of_decide_eq_true accepted
  subst candidate
  exact Increment.terminates_and_all_results_match initial returnAddress code stack returnValid

end EDSL.Certificate
