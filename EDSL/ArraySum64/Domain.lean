/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.ArraySum64.Resources
import EDSL.Grading.Domain

set_option warningAsError true

namespace EDSL.ArraySum64.Domain
open X86 X86.Sequential OS

/-- The existing current read-only input allocation contains two complete
qwords. Their values are chosen independently of candidate decoding/results. -/
def values : List Word := [0xdeadbeefffffffff,0x0000000b00000002]

def call (bytes : List Byte) : ArrayResources64.Call where
  toCall := ⟨10,4096,65544,8192,bytes,0,1⟩
  base := 131072
  values := values
  inputLoan := 2

def resource (bytes : List Byte) : Resources := ⟨Grading.Domain.shared bytes,call bytes⟩

def initial (bytes : List Byte)
    (registers : Register → Word := fun _ => 0xfedcba9876543210)
    (flags : Word := 0x602) : State where
  registers register := match register with
    | .rdi => 131072 | .rsi => 2 | .rsp => 65544 | _ => registers register
  rip := 4096
  flags := flags
  memory := AddressSpace.toMemory (Grading.Domain.space bytes)

theorem array_current (bytes : List Byte) (bound : bytes.length ≤ 4096) :
    ArrayAt64 (AddressSpace.toMemory (Grading.Domain.space bytes)) 131072 values := by
  intro index value present
  match index with
  | 0 | 1 =>
    simp [values] at present
    subst value
    rw [loadQWord_congr _ (AddressSpace.toMemory Grading.Domain.payload) _
      (Grading.Domain.memory_agrees_far bytes bound _ 8 (by decide) (by decide))]
    rfl
  | index + 2 => simp [values] at present

/-- Present code/caller-slot/input loans and current values suffice. The
construction works for every nonempty bounded span, including unsupported code. -/
theorem contract (bytes : List Byte) (positive : 0 < bytes.length) (bound : bytes.length ≤ 4096) :
    ArrayResources64.Contract (call bytes) (Grading.Domain.shared bytes) := by
  have old := Grading.Domain.contractA bytes positive bound
  refine ⟨⟨old.wellFormed,old.held.code,old.held.stack,old.code,old.stack,
    old.returnCanonical,old.stackBound,old.postStackCanonical⟩,
    array_current bytes bound,?_,?_⟩
  · change (131072 : Word).toNat + 8 * 2 ≤ 2^64
    decide
  · intro _
    exact old.held.input (by change Grading.Domain.valuesA ≠ []; decide)

theorem resource_pre (bytes : List Byte) (positive : 0 < bytes.length) (bound : bytes.length ≤ 4096)
    (registers : Register → Word := fun _ => 0xfedcba9876543210) (flags : Word := 0x602) :
    ResourcePre bytes (resource bytes) (initial bytes registers flags) :=
  ⟨⟨contract bytes positive bound,rfl⟩,rfl,rfl,rfl,rfl,rfl⟩

/-- Positivity is a property of the independent mathematical sum alone. -/
theorem positive_sum : 0 < sumMod values := by decide

/-- Useful nonvacuity is independent of machine success. Arbitrary other
registers and full incoming flags are admitted by the same current construction. -/
theorem nonvacuous (bytes : List Byte) (positive : 0 < bytes.length) (bound : bytes.length ≤ 4096) :
    Grading.ReadOnlyNonvacuous readOnlyTask bytes := by
  let admitted := resource bytes
  let entry := initial bytes
  have pre : ResourcePre bytes admitted entry := resource_pre bytes positive bound
  have useful : Useful (resourceInput admitted) := positive_sum
  exact ⟨⟨resourceInput admitted,entry,useful,pre.machine⟩,⟨admitted,entry,useful,pre⟩⟩

end EDSL.ArraySum64.Domain
