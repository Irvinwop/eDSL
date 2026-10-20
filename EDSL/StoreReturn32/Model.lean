/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Write32.Resources
import EDSL.StoreReturn32.Contract

set_option warningAsError true

namespace EDSL.StoreReturn32
open X86 X86.Sequential

/-- Exact callable windows. The independent callable contract does not fix
these instruction choices or their ordering. -/
inductive Shape where
  | storeCopy
  | copyStore
  | copyStoreRax
  deriving DecidableEq, Repr

def Shape.bytes : Shape → List Byte
  | .storeCopy => [0x89, 0x37, 0x48, 0x89, 0xf8, 0xc3]
  | .copyStore => [0x48, 0x89, 0xf8, 0x89, 0x37, 0xc3]
  | .copyStoreRax => [0x48, 0x89, 0xf8, 0x89, 0x30, 0xc3]

def Shape.name : Shape → String
  | .storeCopy => "storeCopy"
  | .copyStore => "copyStore"
  | .copyStoreRax => "copyStoreRax"

/-- Admission binds a complete raw window to a supported exact shape. It does
not assert execution, present memory permissions, or current OS authority. -/
def check (candidate : List Byte) : Option Shape :=
  if candidate = Shape.storeCopy.bytes then some .storeCopy
  else if candidate = Shape.copyStore.bytes then some .copyStore
  else if candidate = Shape.copyStoreRax.bytes then some .copyStoreRax
  else none

theorem check_sound {candidate : List Byte} {shape : Shape}
    (accepted : check candidate = some shape) : candidate = shape.bytes := by
  unfold check at accepted
  split at accepted
  · next same => cases accepted; exact same
  · split at accepted
    · next same => cases accepted; exact same
    · split at accepted
      · next same => cases accepted; exact same
      · cases accepted

/-- Exact accounting for these three-instruction implementations, separate
from their mathematical result. Fetches are outside the operand-read list.
This is not an operation-optimality, cycle, or micro-op bound. -/
def ResultContract (input : Grading.Write32.Input) (initial : State) (result : Result) : Prop :=
  Post input initial result.state ∧ result.instructions = 3 ∧
    result.reads = [⟨.stack, initial.registers .rsp, 8⟩]

end EDSL.StoreReturn32
