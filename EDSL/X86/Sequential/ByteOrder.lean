/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Search

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.X86.Sequential

/-- Decode authenticates actual executable RAM; the memory operand still uses
the complete prestate and the production DATA1 primitive, with its exact faults. -/
theorem step_movzxMem8 {state : State} {destination : Register} {address : Address}
    {prefixed : Bool} (decoded : decodeAt state = .ok (.movzxMem8 destination address prefixed))
    (af : Bool) :
    step af state = do
      let value ← readDataByte state.memory (address.eval state)
      return ⟨.next { state.writeRegister destination ((value.setWidth 32).setWidth 64) with
        rip := state.rip + BitVec.ofNat 64 (Instruction.movzxMem8 destination address prefixed).length },
        [⟨.data, address.eval state, 1⟩]⟩ := by
  rw [step_eq_execute af decoded, execute_movzxMem8]

theorem step_movzxReg8 {state : State} {destination source : Register} {prefixed : Bool}
    (decoded : decodeAt state = .ok (.movzxReg8 destination source prefixed)) (af : Bool) :
    step af state = .ok ⟨.next { state.writeRegister destination
      ((((state.registers source).setWidth 8).setWidth 32).setWidth 64) with
      rip := state.rip + BitVec.ofNat 64 (Instruction.movzxReg8 destination source prefixed).length },
      []⟩ := by
  rw [step_eq_execute af decoded, execute_movzxReg8]

theorem step_cmpReg8 {state : State} {left right : Register} {prefixed : Bool}
    (decoded : decodeAt state = .ok (.cmpReg8 left right prefixed)) (af : Bool) :
    step af state = .ok ⟨.next { state with
      rip := state.rip + BitVec.ofNat 64 (Instruction.cmpReg8 left right prefixed).length
      flags := cmpFlags8 state.flags ((state.registers left).setWidth 8)
        ((state.registers right).setWidth 8) }, []⟩ := by
  rw [step_eq_execute af decoded, execute_cmpReg8]

theorem step_subReg32 {state : State} {destination source : Register} {prefixed : Bool}
    (decoded : decodeAt state = .ok (.subReg32 destination source prefixed)) (af : Bool) :
    step af state = .ok ⟨.next { state.writeRegister destination
      ((((state.registers destination).setWidth 32) -
        ((state.registers source).setWidth 32)).setWidth 64) with
      rip := state.rip + BitVec.ofNat 64 (Instruction.subReg32 destination source prefixed).length
      flags := cmpFlags32 state.flags ((state.registers destination).setWidth 32)
        ((state.registers source).setWidth 32) }, []⟩ := by
  rw [step_eq_execute af decoded, execute_subReg32]

/-- MOVZX's unsigned value is independent of every old destination bit.
This also states the upper32 clearing rule without a chosen input fixture. -/
theorem execute_movzxMem8_context {state final : State} {destination : Register} {address : Address}
    {prefixed af : Bool} {observation : Observation}
    (success : execute state (.movzxMem8 destination address prefixed) af = .ok observation)
    (next : observation.result = .next final) :
    ∃ value, readDataByte state.memory (address.eval state) = .ok value ∧
      (final.registers destination).toNat = value.toNat ∧
      (final.registers destination).toNat < 256 ∧
      (∀ register, register ≠ destination → final.registers register = state.registers register) ∧
      final.memory = state.memory ∧ final.flags = state.flags ∧
      observation.reads = [⟨.data, address.eval state, 1⟩] ∧
      final.rip = state.rip + BitVec.ofNat 64 (Instruction.movzxMem8 destination address prefixed).length := by
  obtain ⟨value, loaded, rfl⟩ := execute_movzxMem8_success_iff.mp success
  cases next
  refine ⟨value, loaded, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · simp only [State.writeRegister, ↓reduceIte]
    rw [BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64),
      BitVec.toNat_setWidth_of_le (by decide : 8 ≤ 32)]
  · simp only [State.writeRegister, ↓reduceIte]
    rw [BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64),
      BitVec.toNat_setWidth_of_le (by decide : 8 ≤ 32)]
    exact value.isLt
  · intro register other
    simp [State.writeRegister, other]

theorem execute_movzxReg8_context (state : State) (destination source : Register)
    (prefixed af : Bool) :
    ∃ final, execute state (.movzxReg8 destination source prefixed) af = .ok ⟨.next final, []⟩ ∧
      (final.registers destination).toNat = (state.registers source).toNat % 256 ∧
      (final.registers destination).toNat < 256 ∧
      (∀ register, register ≠ destination → final.registers register = state.registers register) ∧
      final.memory = state.memory ∧ final.flags = state.flags ∧
      final.rip = state.rip + BitVec.ofNat 64 (Instruction.movzxReg8 destination source prefixed).length := by
  refine ⟨_, rfl, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp only [State.writeRegister, ↓reduceIte]
    rw [BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64),
      BitVec.toNat_setWidth_of_le (by decide : 8 ≤ 32)]
    rfl
  · simp only [State.writeRegister, ↓reduceIte]
    rw [BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64),
      BitVec.toNat_setWidth_of_le (by decide : 8 ≤ 32)]
    exact ((state.registers source).setWidth 8).isLt
  · intro register other
    simp [State.writeRegister, other]

/-- CMP preserves the entire register file, RAM and permission maps, and all
nonarithmetic flag bits. Both operands come from the original low-byte bank. -/
theorem execute_cmpReg8_context (state : State) (left right : Register) (prefixed af : Bool) :
    ∃ final, execute state (.cmpReg8 left right prefixed) af = .ok ⟨.next final, []⟩ ∧
      final.registers = state.registers ∧ final.memory = state.memory ∧
      final.flags = cmpFlags8 state.flags ((state.registers left).setWidth 8)
        ((state.registers right).setWidth 8) ∧
      final.flags &&& ~~~arithmeticFlagMask = state.flags &&& ~~~arithmeticFlagMask ∧
      final.rip = state.rip + BitVec.ofNat 64 (Instruction.cmpReg8 left right prefixed).length :=
  ⟨_, rfl, rfl, rfl, rfl, cmpFlags8_preserves .., rfl⟩

/-- Independent unsigned modular subtraction contract and complete frames.
The subtraction is at width32 even if the source/destination high halves differ. -/
theorem execute_subReg32_context (state : State) (destination source : Register) (prefixed af : Bool) :
    ∃ final, execute state (.subReg32 destination source prefixed) af = .ok ⟨.next final, []⟩ ∧
      (final.registers destination).toNat =
        (2^32 - (state.registers source).toNat % 2^32 +
          (state.registers destination).toNat % 2^32) % 2^32 ∧
      (final.registers destination).toNat < 2^32 ∧
      (∀ register, register ≠ destination → final.registers register = state.registers register) ∧
      final.memory = state.memory ∧
      final.flags = cmpFlags32 state.flags ((state.registers destination).setWidth 32)
        ((state.registers source).setWidth 32) ∧
      final.flags &&& ~~~arithmeticFlagMask = state.flags &&& ~~~arithmeticFlagMask ∧
      final.rip = state.rip + BitVec.ofNat 64 (Instruction.subReg32 destination source prefixed).length := by
  refine ⟨_, rfl, ?_, ?_, ?_, rfl, rfl, cmpFlags32_preserves .., rfl⟩
  · simp [State.writeRegister, BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64),
      BitVec.toNat_sub, BitVec.toNat_setWidth]
  · simp only [State.writeRegister, ↓reduceIte,
      BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)]
    exact (((state.registers destination).setWidth 32) -
      ((state.registers source).setWidth 32)).isLt
  · intro register other
    simp [State.writeRegister, other]

/-- Every SUB32 arithmetic flag uses the existing width32 subtraction laws,
including signed overflow and the low-nibble borrow defining AF. -/
theorem execute_subReg32_flags {state final : State} {destination source : Register}
    {prefixed af : Bool} {reads : List Read}
    (success : execute state (.subReg32 destination source prefixed) af = .ok ⟨.next final, reads⟩) :
    let left := (state.registers destination).setWidth 32
    let right := (state.registers source).setWidth 32
    (final.flags.getLsbD 0 = true ↔ left.toNat < right.toNat) ∧
    (final.flags.getLsbD 2 = evenParity ((left - right).setWidth 8)) ∧
    (final.flags.getLsbD 4 = true ↔ left.toNat % 16 < right.toNat % 16) ∧
    (final.flags.getLsbD 6 = (left == right)) ∧
    (final.flags.getLsbD 7 = (left - right).msb) ∧
    (final.flags.getLsbD 11 = true ↔
      left.toInt - right.toInt < -(2^31 : Int) ∨ 2^31 ≤ left.toInt - right.toInt) := by
  cases success
  exact ⟨cmpFlags32_borrow .., (cmpFlags32_bits ..).2.1, cmpFlags32_auxiliary ..,
    cmpFlags32_zero .., (cmpFlags32_bits ..).2.2.2.2.1, cmpFlags32_overflow ..⟩

namespace Literals

private def byteOrderRegisterCode : Register → Nat
  | .rax => 0 | .rcx => 1 | .rdx => 2 | .rbx => 3
  | .rsp => 4 | .rbp => 5 | .rsi => 6 | .rdi => 7
  | .r8 => 8 | .r9 => 9 | .r10 => 10 | .r11 => 11
  | .r12 => 12 | .r13 => 13 | .r14 => 14 | .r15 => 15

private def byteOrderRegisterBytes (opcodes : List Byte) (reg rm : Register)
    (prefixed byteReg byteRM : Bool) : Option (List Byte) :=
  let r := byteOrderRegisterCode reg
  let b := byteOrderRegisterCode rm
  if !prefixed ∧ (8 ≤ r ∨ 8 ≤ b ∨ (byteReg ∧ 4 ≤ r) ∨ (byteRM ∧ 4 ≤ b)) then none
  else some ((if prefixed then [BitVec.ofNat 8 (0x40 + r / 8 * 4 + b / 8)] else []) ++
    opcodes ++ [BitVec.ofNat 8 (0xc0 + r % 8 * 8 + b % 8)])

private def byteOrderMemoryBytes (destination : Register) (address : Address)
    (prefixed : Bool) : Option (List Byte) :=
  let r := byteOrderRegisterCode destination
  let build (b x : Nat) (suffix : List Byte) :=
    if !prefixed ∧ (8 ≤ r ∨ 8 ≤ b ∨ 8 ≤ x) then none
    else some ((if prefixed then [BitVec.ofNat 8 (0x40 + r / 8 * 4 + x / 8 * 2 + b / 8)] else []) ++
      [0x0f, 0xb6] ++ suffix)
  match address with
  | .base base =>
    let b := byteOrderRegisterCode base
    if b % 8 = 4 ∨ b % 8 = 5 then none
    else build b 0 [BitVec.ofNat 8 (r % 8 * 8 + b % 8)]
  | .indexed base index scale =>
    let b := byteOrderRegisterCode base
    let x := byteOrderRegisterCode index
    if b % 8 = 5 ∨ x = 4 then none
    else build b x [BitVec.ofNat 8 (r % 8 * 8 + 4),
      BitVec.ofNat 8 (scale.val * 64 + x % 8 * 8 + b % 8)]
  | .baseDisp8 _ _ | .sibDisp8 _ _ _ _ => none

private def byteOrderCandidate : Instruction → Option (List Byte)
  | .movzxReg8 destination source prefixed =>
    byteOrderRegisterBytes [0x0f,0xb6] destination source prefixed false true
  | .movzxMem8 destination address prefixed => byteOrderMemoryBytes destination address prefixed
  | .cmpReg8 left right prefixed => byteOrderRegisterBytes [0x38] right left prefixed true true
  | .subReg32 destination source prefixed =>
    byteOrderRegisterBytes [0x29] source destination prefixed false false
  | _ => none

/-- A partial same-constructor encoder. The real production decoder and exact
length guard every released result. Unencodable banks/addresses/prefix states
return none, so no high-byte, upper-bank or address shape can silently change. -/
def byteOrderEncoding (instruction : Instruction) : Option (List Byte) :=
  match byteOrderCandidate instruction with
  | none => none
  | some bytes =>
    match decodeAt (codeState bytes 0) with
    | .ok decoded =>
      if decoded = instruction ∧ bytes.length = instruction.length then some bytes else none
    | .error _ => none

theorem byteOrderEncoding_decoded {instruction : Instruction} {bytes : List Byte}
    (encoded : byteOrderEncoding instruction = some bytes) :
    decodeAt (codeState bytes 0) = .ok instruction ∧ bytes.length = instruction.length := by
  unfold byteOrderEncoding at encoded
  cases candidate : byteOrderCandidate instruction with
  | none => simp [candidate] at encoded
  | some values =>
    simp only [candidate] at encoded
    cases decoded : decodeAt (codeState values 0) with
    | error fault => simp [decoded] at encoded
    | ok actual =>
      simp only [decoded] at encoded
      split at encoded
      next checked =>
        cases encoded
        exact ⟨by rw [decoded, checked.1], checked.2⟩
      next => cases encoded

end Literals
end EDSL.X86.Sequential
