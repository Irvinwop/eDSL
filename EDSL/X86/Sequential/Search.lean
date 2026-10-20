/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Machine
import EDSL.X86.Sequential.Code
import EDSL.X86.Sequential.Literals

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.X86.Sequential

/-- A finite-window decode transfers to the actual production step, without
requiring a CFG. CodeAt binds current executable RAM; operand accesses still
use the complete current state and the production memory primitives. -/
theorem step_code_eq_execute {bytes : List Byte} {memory : Memory} {base : Word}
    {offset : Nat} {instruction : Instruction} (code : CodeAt memory base bytes)
    (size : bytes.length ≤ 64) (inside : offset < bytes.length) (state : State)
    (currentMemory : state.memory = memory)
    (currentPC : state.rip = base + BitVec.ofNat 64 offset)
    (decoded : decodeAt (codeState bytes offset) = .ok instruction) (af : Bool) :
    step af state = execute state instruction af :=
  step_eq_execute af (decodeAt_transport
    (code_fetch_transport code size offset inside state currentMemory currentPC) decoded)

/-- Exact success/fault behavior of a decoded memory-left byte comparison.
The equation covers every AF choice, all source/address aliases and high bits. -/
theorem step_cmpMemReg8 {state : State} {address : Address} {source : Register}
    (decoded : decodeAt state = .ok (.cmpMemReg8 address source)) (af : Bool) :
    step af state = do
      let value ← readDataByte state.memory (address.eval state)
      return ⟨.next { state with
        rip := state.rip + BitVec.ofNat 64 (Instruction.cmpMemReg8 address source).length
        flags := cmpFlags8 state.flags value ((state.registers source).setWidth 8) },
        [⟨.data, address.eval state, 1⟩]⟩ := by
  rw [step_eq_execute af decoded, execute_cmpMemReg8]

theorem step_cmpMemReg32 {state : State} {address : Address} {source : Register}
    (decoded : decodeAt state = .ok (.cmpMemReg32 address source)) (af : Bool) :
    step af state = do
      let value ← loadDWord state.memory (address.eval state)
      return ⟨.next { state with
        rip := state.rip + BitVec.ofNat 64 (Instruction.cmpMemReg32 address source).length
        flags := cmpFlags32 state.flags value ((state.registers source).setWidth 32) },
        [⟨.data, address.eval state, 4⟩]⟩ := by
  rw [step_eq_execute af decoded, execute_cmpMemReg32]

theorem step_movSignImm32 {state : State} {destination : Register} {immediate : BitVec 32}
    (decoded : decodeAt state = .ok (.movSignImm32 destination immediate)) (af : Bool) :
    step af state = .ok ⟨.next { state.writeRegister destination (immediate.signExtend 64) with
      rip := state.rip + 7 }, []⟩ := by
  rw [step_eq_execute af decoded, execute_movSignImm32]

namespace Literals

private def registerCode : Register → Nat
  | .rax => 0 | .rcx => 1 | .rdx => 2 | .rbx => 3
  | .rsp => 4 | .rbp => 5 | .rsi => 6 | .rdi => 7
  | .r8 => 8 | .r9 => 9 | .r10 => 10 | .r11 => 11
  | .r12 => 12 | .r13 => 13 | .r14 => 14 | .r15 => 15

private def memoryOperandBytes (source : Register) (operand : Address) : Option (List Byte) := do
  let reg := registerCode source
  if 8 ≤ reg then none else
  match operand with
  | .base base =>
    let rm := registerCode base
    if 8 ≤ rm ∨ rm = 4 ∨ rm = 5 then none
    else some [BitVec.ofNat 8 (reg * 8 + rm)]
  | .indexed base index scale =>
    let b := registerCode base
    let i := registerCode index
    if 8 ≤ b ∨ 8 ≤ i ∨ b = 5 ∨ i = 4 then none
    else some [BitVec.ofNat 8 (reg * 8 + 4), BitVec.ofNat 8 (scale.val * 64 + i * 8 + b)]
  | .baseDisp8 _ _ | .sibDisp8 _ _ _ _ => none

private def searchCandidate : Instruction → Option (List Byte)
  | .cmpMemReg8 operand source =>
    if 4 ≤ registerCode source then none
    else (List.cons 0x38) <$> memoryOperandBytes source operand
  | .cmpMemReg32 operand source => (List.cons 0x39) <$> memoryOperandBytes source operand
  | .movSignImm32 destination immediate =>
    let code := registerCode destination
    some [if code < 8 then 0x48 else 0x49, BitVec.ofNat 8 0xc7,
      BitVec.ofNat 8 (0xc0 + code % 8), immediate.setWidth 8,
      (immediate >>> 8).setWidth 8, (immediate >>> 16).setWidth 8, (immediate >>> 24).setWidth 8]
  | _ => none

/-- A deliberately partial byte literal generator for the three search ISA
families. Unsupported widths, registers and addresses return none. The real
decoder checks constructor identity and length before any bytes are released;
no LOW8/high-byte, bank, address or immediate truncation can silently lower an
instruction to a different supported operation. Other families return none. -/
def searchEncoding (instruction : Instruction) : Option (List Byte) :=
  match searchCandidate instruction with
  | none => none
  | some bytes =>
    match decodeAt (codeState bytes 0) with
    | .ok decoded =>
      if decoded = instruction ∧ bytes.length = instruction.length then some bytes else none
    | .error _ => none

theorem searchEncoding_decoded {instruction : Instruction} {bytes : List Byte}
    (encoded : searchEncoding instruction = some bytes) :
    decodeAt (codeState bytes 0) = .ok instruction ∧ bytes.length = instruction.length := by
  unfold searchEncoding at encoded
  cases candidate : searchCandidate instruction with
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
