/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CallMemory64.Contract

set_option warningAsError true

namespace EDSL.CallMemoryLoop64
open X86 OS OS.AddressSpace

/-! An independent contract for a full-width counted transformation of one
owned DATA word. The original caller slot and current private-stack/DATA
capabilities use the ordinary sequential RAM model. CPU correspondence still
requires the stated AC/CET-disabled, no-asynchronous-interference assumptions;
these definitions establish no source-language or kernel refinement. -/

abbrev Program := CallStack.Program

structure Resources extends CallMemory64.Resources where
  count : Word

structure Input extends CallMemory64.Input where
  count : Word

def resourceInput (resource : Resources) : Input :=
  ⟨CallMemory64.resourceInput resource.toResources, resource.count⟩

/-- Arithmetic specification independent of instruction selection and order. -/
def resultNat (value count : Word) : Nat := (value.toNat + count.toNat) % 2^64

/-- Used only for nonzero counts; the last stored value precedes the returned
value by one in modular arithmetic. The zero-count case retains the old word. -/
def targetWord (value count : Word) : Word :=
  BitVec.ofNat 64 (value.toNat + count.toNat - 1)

theorem resultNat_lt (value count : Word) : resultNat value count < 2^64 :=
  Nat.mod_lt _ (by decide)

theorem resultNat_add (value count : Word) :
    (value + count).toNat = resultNat value count := by
  simp only [BitVec.toNat_add, resultNat]

/-- Present current resources and external ABI bindings, for every full64
count including zero. No decoding, loop shape, CALL, future result, access
order, termination or instruction budget appears in admission. -/
structure ResourcePre (program : Program) (resource : Resources) (initial : State) : Prop
    extends CallMemory64.ResourcePre program resource.toResources initial where
  counter : initial.registers .rdx = resource.count
  stackCapacity : 32 ≤ resource.descriptor.frame.capacity

/-- Only the target and private stack may change. For zero count the target
retains its actual initial word; all other counts have an independent final
word specification. The original caller slot, permissions and ABI are framed. -/
structure Post (input : Input) (initial final : State) : Prop where
  value : (final.registers .rax).toNat = resultNat input.value input.count
  stored : readWord final.memory input.pointer =
    if input.count = 0 then readWord initial.memory input.pointer
    else .ok (targetWord input.value input.count)
  outside : ∀ query, ¬input.privateStack.Contains query →
    ¬(qwordRegion input.pointer).Contains query →
    final.memory.read query = initial.memory.read query
  executable : final.memory.executable = initial.memory.executable
  writable : final.memory.writable = initial.memory.writable
  returnAddress : final.rip = input.returnAddress
  stackPointer : final.registers .rsp = initial.registers .rsp + 8
  preserved : ∀ register, register ∉ CallStack.clobbers →
    final.registers register = initial.registers register
  flags : final.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask

end EDSL.CallMemoryLoop64
