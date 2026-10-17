/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CallStack.Resources
import EDSL.OS.CallMemory64.Model

set_option warningAsError true

namespace EDSL.CallMemory64
open X86 OS OS.AddressSpace

/-! Contracts concern the ordinary-RAM CallReturn model with canonical
addresses and a frozen original caller-slot return boundary. Physical CPU
correspondence additionally requires AC/CET disabled and no asynchronous
interference. These definitions assert no kernel or source refinement. -/

abbrev Program := CallStack.Program

structure Resources where
  shared : Borrowing.State
  descriptor : OS.CallMemory64.Descriptor
  value : Word

structure Input where
  value : Word
  pointer : Word
  returnAddress : Word
  privateStack : Region

def resourceInput (resource : Resources) : Input :=
  ⟨resource.value, resource.descriptor.target,
    resource.descriptor.frame.call.returnAddress, resource.descriptor.frame.region⟩

/-- Independent unsigned arithmetic specification, with no helper, instruction
selection, access order or cost in its definition. -/
def resultNat (value : Word) : Nat := (value.toNat + 1) % 2^64

theorem resultNat_lt (value : Word) : resultNat value < 2^64 :=
  Nat.mod_lt _ (by decide)

theorem one_addition (value : Word) : (value + 1).toNat = resultNat value := by
  simp only [BitVec.toNat_add, resultNat]
  rfl

/-- Present resources and external ABI bindings. The target's initial contents
are arbitrary. Admission contains no decoding, future access, result or fuel
premise, and creates no target read loan. -/
structure ResourcePre (program : Program) (resource : Resources) (initial : State) : Prop where
  current : OS.CallMemory64.Current resource.descriptor resource.shared initial
  code : resource.descriptor.frame.call.bytes = program.bytes
  entry : initial.rip = resource.descriptor.frame.call.code + BitVec.ofNat 64 program.entry
  entryBound : program.entry < program.bytes.length
  stack : initial.registers .rsp = resource.descriptor.frame.top
  pointer : initial.registers .rdi = resource.descriptor.target
  argument : initial.registers .rsi = resource.value
  capacity : 16 ≤ resource.descriptor.frame.capacity
  alignment : (initial.registers .rsp).toNat % 16 = 8

theorem ResourcePre.code_base {program resource initial}
    (pre : ResourcePre program resource initial) :
    program.codeBase initial = resource.descriptor.frame.call.code := by
  simp only [CallStack.Program.codeBase, pre.entry, BitVec.add_sub_cancel]

theorem ResourcePre.codeAt {program resource initial}
    (pre : ResourcePre program resource initial) :
    CodeAt initial.memory (program.codeBase initial) program.bytes := by
  rw [pre.current.coupled, pre.code_base, ← pre.code]
  exact pre.current.contract.stack.pureCall.code

/-- The DATA word and private stack are the complete mutable footprint. The
original return slot, all other RAM, permissions, the ABI and nonarithmetic
flags retain their independent caller-visible contracts. -/
structure Post (input : Input) (initial final : State) : Prop where
  value : (final.registers .rax).toNat = resultNat input.value
  stored : readWord final.memory input.pointer = .ok input.value
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

end EDSL.CallMemory64
