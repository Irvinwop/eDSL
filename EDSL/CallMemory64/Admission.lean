/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CallMemory64.Domain
import EDSL.CallMemory64.Verification

set_option warningAsError true

namespace EDSL.CallMemory64
open X86

def Domain.resource (program : Program) (input : Word) (old : Word := 0) : Resources :=
  ⟨Domain.shared program.bytes old, Domain.descriptor program.bytes, input⟩

/-- Reachable resource construction gives every scalar input, old target word,
other GPRs and flags a present admission for arbitrary bounded code. -/
theorem Domain.resource_pre (program : Program) (entry : program.entry < program.bytes.length)
    (bound : program.bytes.length ≤ 4096) (input : Word) (old : Word := 0)
    (registers : Register → Word := fun _ => 0xfedcba9876543210) (flags : Word := 0x602) :
    ResourcePre program (Domain.resource program input old)
      (Domain.initial program input old registers flags) :=
  ⟨Domain.current program entry bound input old registers flags, rfl, rfl,
    entry, rfl, rfl, rfl, by change 16 ≤ 16; decide,
    by change (65544 : Word).toNat % 16 = 8; decide⟩

/-- Both outputs need to change in this actual admitted world. Admission
remains independent of whether the submitted bytes decode or execute. -/
theorem domain_nonvacuous (program : Program) (entry : program.entry < program.bytes.length)
    (bound : program.bytes.length ≤ 4096) : Nonvacuous program := by
  refine ⟨Domain.resource program 1 0, Domain.initial program 1 0,
    Domain.resource_pre program entry bound 1 0, ?_, ?_⟩
  · change (0xfedcba9876543210 : Word).toNat ≠ resultNat 1
    decide
  · have observed := (Domain.target_read program.bytes (by omega) bound 0).2
    change readWord (OS.AddressSpace.toMemory (Domain.shared program.bytes 0).resources.space)
      Domain.target ≠ .ok (1 : Word)
    rw [observed]
    intro same
    exact (by decide : (0 : Word) ≠ 1) (Except.ok.inj same)

end EDSL.CallMemory64
