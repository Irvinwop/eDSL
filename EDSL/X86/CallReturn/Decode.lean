/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.CallReturn.Model

namespace EDSL.X86.CallReturn

def rexPrefix (opcode : Byte) : Bool := decide (0x40 ≤ opcode.toNat ∧ opcode.toNat ≤ 0x4f)

def stackOpcode (opcode : Byte) : Bool := decide (0x50 ≤ opcode.toNat ∧ opcode.toNat ≤ 0x5f)

def decodeStack (rex opcode : Byte) (prefixed : Bool) : Instruction :=
  let register := Sequential.rexModRMRM rex opcode
  if opcode.toNat < 0x58 then .push64 register prefixed else .pop64 register prefixed

/-- Exactly one REX.W, mod=01, and a signed byte displacement. No memory
operand is read. A SIB missing-index field is distinct from R12 when X=1. -/
def decodeLeaAt (state : State) (rex : Byte) : Except Error Instruction := do
  let modrm ← fetchByte state.memory (state.rip + 2)
  if modrm.toNat / 64 ≠ 1 then throw .unsupportedEncoding
  if modrm.toNat % 8 = 4 then
    let sib ← fetchByte state.memory (state.rip + 3)
    let index := if sib.toNat / 8 % 8 = 4 ∧ rex.getLsbD 1 = false then none
      else some (Sequential.rexSIBIndex rex sib)
    let address := Address.sib (Sequential.rexModRMRM rex sib) index
      ⟨sib.toNat / 64, by have := sib.isLt; omega⟩
    return .leaDisp8 (Sequential.rexModRMReg rex modrm) address
      (← fetchByte state.memory (state.rip + 4))
  else
    return .leaDisp8 (Sequential.rexModRMReg rex modrm)
      (.plain (Sequential.rexModRMRM rex modrm)) (← fetchByte state.memory (state.rip + 3))

/-- Only E8, opcode-register PUSH/POP, and the selected displacement LEA.
Every immediate/SIB/displacement byte is fetched with execute permission. -/
def decodeNewAt (state : State) (fallback : Error) : Except Error Instruction := do
  let opcode ← fetchByte state.memory state.rip
  if opcode = 0xe8 then
    let b0 ← fetchByte state.memory (state.rip + 1)
    let b1 ← fetchByte state.memory (state.rip + 2)
    let b2 ← fetchByte state.memory (state.rip + 3)
    let b3 ← fetchByte state.memory (state.rip + 4)
    return .callRelative32 (joinDWord b0 b1 b2 b3)
  else if stackOpcode opcode then
    return decodeStack 0 opcode false
  else if rexPrefix opcode then
    let operation ← fetchByte state.memory (state.rip + 1)
    if stackOpcode operation then return decodeStack opcode operation true
    else if Sequential.rexWPrefix opcode && operation == 0x8d then decodeLeaAt state opcode
    else throw .unsupportedEncoding
  else throw fallback

/-- Existing successes embed verbatim. In particular the old RET and INC
executor/decoder stay unchanged. An actual failed fetch is never a fallback. -/
def decodeAt (state : State) : Except Error Instruction :=
  match Sequential.decodeAt state with
  | .ok instruction => .ok (.sequential instruction)
  | .error (.inaccessibleInstruction address) => .error (.inaccessibleInstruction address)
  | .error fault => decodeNewAt state fault

theorem decodeAt_sequential {state : State} {instruction : Sequential.Instruction}
    (decoded : Sequential.decodeAt state = .ok instruction) :
    decodeAt state = .ok (.sequential instruction) := by rw [decodeAt, decoded]

theorem decodeAt_fetch_fault {state : State} {address : Word}
    (fault : Sequential.decodeAt state = .error (.inaccessibleInstruction address)) :
    decodeAt state = .error (.inaccessibleInstruction address) := by rw [decodeAt, fault]

theorem decodeAt_extension_rejects_sequential {state : State} {instruction : Instruction}
    (decoded : decodeAt state = .ok instruction) (newInstruction : instruction.isExtension = true) :
    ∃ fault, Sequential.decodeAt state = .error fault := by
  cases old : Sequential.decodeAt state with
  | error fault => exact ⟨fault, rfl⟩
  | ok old =>
    simp only [decodeAt, old, Except.ok.injEq] at decoded
    cases decoded
    cases newInstruction

end EDSL.X86.CallReturn
