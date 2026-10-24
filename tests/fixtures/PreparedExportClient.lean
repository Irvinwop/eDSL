/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Known

set_option warningAsError true
set_option autoImplicit false

/-! Synthetic client data for checked preparation/replay. This module is never
part of the grader's trusted import closure. -/
namespace PreparedExportFixture
universe u

-- Keep separate type and value dependencies so a partial rewrite cannot pass.
def Ty : Type := Nat
def datum : Nat := 37
def keep : Ty := datum

theorem root : keep = datum := rfl

def redirected : Nat := 37
theorem overrideRoot : keep = (37 : Nat) := rfl

def polyKeep (α : Sort u) (value : α) : α := value
theorem polyRoot : polyKeep Nat datum = datum := rfl

inductive Header (α : Type u) : Type u where
  | pack (payload : α) (count : Ty) : Header α

noncomputable def payload {α : Type u} (header : Header α) : α :=
  Header.rec (motive := fun _ => α) (fun value _ => value) header

theorem headerRoot : payload (Header.pack datum datum : Header Nat) = datum := rfl

opaque sealed : datum = datum := rfl
theorem opaqueRoot : datum = datum := sealed

-- A positive integration with the independent machine-code task, rather than
-- only synthetic equality propositions.
def originalPairBytes : List EDSL.X86.Byte := EDSL.Pair32.bytes
def pairProgram : List EDSL.X86.Byte := originalPairBytes

theorem pairRoot : EDSL.Grading.Claim .pair32 pairProgram := EDSL.Grading.Known.pair

end PreparedExportFixture
