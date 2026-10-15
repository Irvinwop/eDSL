/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Semantics

namespace EDSL.Examples.Increment

/- A deliberately tiny abstract machine, not an ISA or OS model.
Each add instruction costs one abstract operation. Inputs are natural numbers. -/
inductive Instruction where
  | add (amount : Nat)

def execute : List Instruction → Nat → Nat
  | [], input => input
  | .add amount :: rest, input => execute rest (input + amount)

/-- The specification is independent of the program syntax. -/
def ImplementsIncrement (program : List Instruction) : Prop :=
  ∀ input, execute program input = input + 1

def implementation : List Instruction := [.add 1]

theorem implementation_correct : ImplementsIncrement implementation := by
  intro input
  rfl

/-- Every program in this instruction language meeting the specification
needs at least one operation. This quantifies over all candidate programs. -/
theorem operation_lower_bound (program : List Instruction)
    (correct : ImplementsIncrement program) : 1 ≤ program.length := by
  cases program with
  | nil =>
    have impossible := correct 0
    simp [execute] at impossible
  | cons instruction rest =>
    exact Nat.succ_le_succ (Nat.zero_le rest.length)

theorem implementation_attains_bound : implementation.length = 1 := by
  rfl

theorem implementation_is_optimal (program : List Instruction)
    (correct : ImplementsIncrement program) :
    implementation.length ≤ program.length := by
  exact operation_lower_bound program correct

def semantics : Semantics (List Instruction) Nat Nat :=
  ⟨fun program input output => execute program input = output⟩

theorem implementation_has_behavior :
    HasBehavior semantics implementation (fun _ => True) := by
  intro input _
  exact ⟨execute implementation input, rfl⟩

theorem implementation_satisfies :
    Satisfies semantics implementation (fun _ => True)
      (fun input output => output = input + 1) := by
  intro input _ output behavior
  exact behavior.symm.trans (implementation_correct input)

end EDSL.Examples.Increment
