/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.ArrayMemory
import EDSL.X86.Flags
import EDSL.X86.Sequential.Model

namespace EDSL.Sum32
open X86

/-- The shared input contract is independent of either loop's control flow.
Memory denotes current stable ordinary RAM for this sequential call. -/
structure Pre (bytes : List Byte) (initial : State) (values : List (BitVec 32))
    (target : Word) : Prop where
  code : CodeAt initial.memory initial.rip bytes
  array : ArrayAt initial.memory (initial.registers .rdi) values
  bound : ArrayBound (initial.registers .rdi) values
  count : initial.registers .rsi = BitVec.ofNat 64 values.length
  stack : readWord initial.memory (initial.registers .rsp) = .ok target
  canonicalTarget : canonical target = true
  canonicalStackAfter : canonical (initial.registers .rsp + 8) = true

/-- These are the only general registers either admitted loop may change.
All SysV callee-saved general-purpose registers are consequently preserved. -/
def clobbers : List Register := [.rax, .rcx, .rsi, .rdi, .rsp]

/-- Common observable behavior. Arithmetic status flags may differ between
legal implementations and choices; every other abstract flag bit survives. -/
structure Post (initial : State) (values : List (BitVec 32)) (target : Word)
    (final : State) : Prop where
  value : final.registers .rax = (sum32 values).setWidth 64
  memory : final.memory = initial.memory
  returnAddress : final.rip = target
  stackPointer : final.registers .rsp = initial.registers .rsp + 8
  preserved : ∀ register, register ∉ clobbers → final.registers register = initial.registers register
  flags : final.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask

/-- The input footprint enumerates four-byte elements independently of either
loop's control representation. It includes no read at the one-past address. -/
def inputReads (base : Word) : List (BitVec 32) → List Sequential.Read
  | [] => []
  | _ :: rest => ⟨.data, base, 4⟩ :: inputReads (base + 4) rest

/-- Input operand reads followed by the actual return-stack read.
Instruction fetches are a different observation. -/
def operandReads (initial : State) (values : List (BitVec 32)) : List Sequential.Read :=
  inputReads (initial.registers .rdi) values ++
    [⟨.stack, initial.registers .rsp, 8⟩]

theorem operandReads_empty (initial : State) :
    operandReads initial [] = [⟨.stack, initial.registers .rsp, 8⟩] := rfl

theorem inputReads_length (base : Word) (values : List (BitVec 32)) :
    (inputReads base values).length = values.length := by
  induction values generalizing base with
  | nil => rfl
  | cons value rest induction => simp only [inputReads, List.length_cons, induction]

theorem Pre.count_lt {bytes : List Byte} {initial : State} {values : List (BitVec 32)}
    {target : Word} (admitted : Pre bytes initial values target) : values.length < 2^64 :=
  admitted.bound.length_lt

theorem Post.callee_saved {initial final : State} {values : List (BitVec 32)} {target : Word}
    (result : Post initial values target final) (register : Register)
    (saved : register ∈ [.rbx, .rbp, .r12, .r13, .r14, .r15]) :
    final.registers register = initial.registers register := by
  apply result.preserved register
  simp only [List.mem_cons, List.not_mem_nil, or_false] at saved
  rcases saved with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end EDSL.Sum32
