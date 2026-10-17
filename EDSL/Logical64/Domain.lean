/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Logical64.Resources
import EDSL.Grading.Domain

set_option warningAsError true

namespace EDSL.Logical64.Domain
open X86 X86.Sequential OS

def call (bytes : List Byte) : CallResources.Call :=
  ⟨10,4096,65544,8192,bytes,0,1⟩

def resource (bytes : List Byte) (left right : Word) : Resources :=
  ⟨Grading.Domain.shared bytes,call bytes,left,right⟩

/-- Every full64 operand pair, independent other registers and arbitrary flags
are admitted without interpreting the selected program. -/
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

theorem contract (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) :
    CallResources.Contract (call bytes) (Grading.Domain.shared bytes) := by
  have base := Grading.Domain.contractA bytes positive bound
  exact ⟨base.wellFormed,base.held.code,base.held.stack,base.code,base.stack,
    base.returnCanonical,base.stackBound,base.postStackCanonical⟩

theorem resource_pre (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) (left right : Word)
    (registers : Register → Word := fun _ => 0xfedcba9876543210)
    (flags : Word := 0x602) :
    ResourcePre bytes (resource bytes left right) (initial bytes left right registers flags) :=
  ⟨⟨contract bytes positive bound,rfl⟩,rfl,rfl,rfl,rfl,rfl⟩

/-- Independent nonzero, unequal inputs inhabit both domains for every
operation and every nonempty bounded candidate, without executing it. -/
theorem nonvacuous (operation : Operation) (bytes : List Byte)
    (positive : 0 < bytes.length) (bound : bytes.length ≤ 4096) :
    Grading.ReadOnlyNonvacuous (readOnlyTask operation) bytes := by
  let admitted := resource bytes 0xf0 0x33
  let entry := initial bytes 0xf0 0x33
  have pre : ResourcePre bytes admitted entry := resource_pre bytes positive bound 0xf0 0x33
  have useful : Useful (resourceInput admitted) := by
    change (0xf0 : Word) ≠ 0 ∧ (0x33 : Word) ≠ 0 ∧ (0xf0 : Word) ≠ 0x33
    decide
  exact ⟨⟨resourceInput admitted,entry,useful,pre.machine⟩,⟨admitted,entry,useful,pre⟩⟩

end EDSL.Logical64.Domain
