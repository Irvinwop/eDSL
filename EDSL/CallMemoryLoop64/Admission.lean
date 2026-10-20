/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CallMemoryLoop64.Verification
import EDSL.CallMemory64.CapacityDomain

set_option warningAsError true

namespace EDSL.CallMemoryLoop64
open X86

namespace Domain

def resource (program : Program) (input count : Word) (old : Word := 0) : Resources :=
  ⟨CallMemory64.CapacityDomain.resource 32 program input old, count⟩

/-- Bind only the external count in an otherwise arbitrary register seed.
The checked domain independently installs code, original slot, private stack
and DATA and initializes the old target through actual resource mutations. -/
def initial (program : Program) (input count : Word) (old : Word := 0)
    (registers : Register → Word := fun _ => 0xfedcba9876543210)
    (flags : Word := 0x602) : State :=
  CallMemory64.CapacityDomain.initialCPU 32 program input old
    (fun register => if register = .rdx then count else registers register) flags

theorem resource_pre (program : Program) (entry : program.entry < program.bytes.length)
    (bound : program.bytes.length ≤ 4096) (input count : Word) (old : Word := 0)
    (registers : Register → Word := fun _ => 0xfedcba9876543210) (flags : Word := 0x602) :
    ResourcePre program (resource program input count old)
      (initial program input count old registers flags) :=
  ⟨CallMemory64.CapacityDomain.resource_pre 32 CallStack.CapacityDomain.supported32
    (by decide) program entry bound input old
    (fun register => if register = .rdx then count else registers register) flags,
    rfl, by change 32 ≤ 32; decide⟩

end Domain

/-- Nonvacuity is derived from actual checked allocation for arbitrary bounded
code, including unsupported bytes. No future run or count restriction is needed. -/
theorem domain_nonvacuous (program : Program) (entry : program.entry < program.bytes.length)
    (bound : program.bytes.length ≤ 4096) : Nonvacuous program := by
  refine ⟨Domain.resource program 1 1 0, Domain.initial program 1 1 0,
    Domain.resource_pre program entry bound 1 1 0, ?_, ?_, ?_⟩
  · change (0xfedcba9876543210 : Word).toNat ≠ resultNat 1 1
    decide
  · change (1 : Word) ≠ 0
    decide
  · have observed := (CallMemory64.CapacityDomain.target_read 32
      CallStack.CapacityDomain.supported32 program.bytes (by omega) bound 0).2
    change readWord (OS.AddressSpace.toMemory
      (CallMemory64.CapacityDomain.shared 32 program.bytes 0).resources.space)
      CallMemory64.CapacityDomain.target ≠ .ok (targetWord 1 1)
    rw [observed]
    intro same
    exact (by decide : (0 : Word) ≠ targetWord 1 1) (Except.ok.inj same)

end EDSL.CallMemoryLoop64
