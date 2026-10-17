/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Comparison64.Resources
import EDSL.Grading.Domain

set_option warningAsError true

namespace EDSL.Comparison64.Domain
open X86 X86.Sequential OS

/-- Only the existing executable-span and original caller-slot loans are
needed. A register comparison has no owned mutable target. -/
def call (bytes : List Byte) : CallResources.Call :=
  ⟨10, 4096, 65544, 8192, bytes, 0, 1⟩

def resource (bytes : List Byte) (left right : Word) : Resources :=
  ⟨Grading.Domain.shared bytes, call bytes, left, right⟩

/-- Full64 operands, arbitrary other registers (including RAX) and arbitrary
flags are independent of the selected code and its eventual behavior. -/
def initial (bytes : List Byte) (left right : Word)
    (registers : Register → Word := fun _ => 0xfedcba9876543210)
    (flags : Word := 0x602) : State where
  registers register := match register with
    | .rdi => left
    | .rsi => right
    | .rsp => 65544
    | _ => registers register
  rip := 4096
  flags := flags
  memory := AddressSpace.toMemory (Grading.Domain.space bytes)

/-- Present bytes, current world validity and the code/slot loans suffice;
there is no decoding, execution or mutable-allocation premise. -/
theorem contract (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) :
    CallResources.Contract (call bytes) (Grading.Domain.shared bytes) := by
  have base := Grading.Domain.contractA bytes positive bound
  exact ⟨base.wellFormed, base.held.code, base.held.stack, base.code, base.stack,
    base.returnCanonical, base.stackBound, base.postStackCanonical⟩

/-- Every nonempty bounded candidate admits all full64 inputs and flags,
including equal operands and arbitrary incoming RAX. -/
theorem resource_pre (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) (left right : Word)
    (registers : Register → Word := fun _ => 0xfedcba9876543210)
    (flags : Word := 0x602) :
    ResourcePre bytes (resource bytes left right) (initial bytes left right registers flags) :=
  ⟨⟨contract bytes positive bound, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩

/-- Useful unequal witnesses are chosen without interpreting the code. The
construction inhabits the raw and current-resource domains for every operation;
neither witness establishes any execution or result claim. -/
theorem nonvacuous (operation : Operation) (bytes : List Byte)
    (positive : 0 < bytes.length) (bound : bytes.length ≤ 4096) :
    Grading.ReadOnlyNonvacuous (readOnlyTask operation) bytes := by
  let admitted := resource bytes 0xffffffffffffffff 0x100000000
  let entry := initial bytes 0xffffffffffffffff 0x100000000
  have pre : ResourcePre bytes admitted entry :=
    resource_pre bytes positive bound 0xffffffffffffffff 0x100000000
  have useful : Useful (resourceInput admitted) := by
    change (0xffffffffffffffff : Word) ≠ 0x100000000
    decide
  exact ⟨⟨resourceInput admitted, entry, useful, pre.machine⟩,
    ⟨admitted, entry, useful, pre⟩⟩

end EDSL.Comparison64.Domain
