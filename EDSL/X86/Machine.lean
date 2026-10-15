/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Memory

namespace EDSL.X86

inductive Instruction where
  /-- `8D 47 ib`: LEA EAX, [RDI + sign_extend(disp8)], default 64-bit address size. -/
  | leaEaxRdiDisp8 (displacement : Byte)
  /-- `8B 07`: MOV EAX, DWORD PTR [RDI]. -/
  | loadEaxRdi
  /-- `89 37`: MOV DWORD PTR [RDI], ESI. -/
  | storeEsiRdi
  /-- `C3`: near return, with an accessible stack word and canonical target. -/
  | ret
  deriving DecidableEq, Repr

def decodeAt (state : State) : Except Error Instruction := do
  let opcode ← fetchByte state.memory state.rip
  if opcode = 0xc3 then
    return .ret
  else if opcode = 0x8d then
    let modrm ← fetchByte state.memory (state.rip + 1)
    if modrm ≠ 0x47 then
      throw .unsupportedEncoding
    let displacement ← fetchByte state.memory (state.rip + 2)
    return .leaEaxRdiDisp8 displacement
  else if opcode = 0x8b then
    let modrm ← fetchByte state.memory (state.rip + 1)
    if modrm ≠ 0x07 then throw .unsupportedEncoding
    return .loadEaxRdi
  else if opcode = 0x89 then
    let modrm ← fetchByte state.memory (state.rip + 1)
    if modrm ≠ 0x37 then throw .unsupportedEncoding
    return .storeEsiRdi
  else
    throw (.unsupportedOpcode opcode)

def executeLea (state : State) (displacement : Byte) : State :=
  let address := state.registers .rdi + displacement.signExtend 64
  let result := (address.setWidth 32).setWidth 64
  { state.writeRegister .rax result with rip := state.rip + 3 }

def executeLoad (state : State) : Except Error State := do
  let value ← loadDWord state.memory (state.registers .rdi)
  return { state.writeRegister .rax (value.setWidth 64) with rip := state.rip + 2 }

def executeStore (state : State) : Except Error State := do
  let memory ← storeDWord state.memory (state.registers .rdi) ((state.registers .rsi).setWidth 32)
  return { state with memory := memory, rip := state.rip + 2 }

def executeRet (state : State) : Except Error State := do
  let target ← readWord state.memory (state.registers .rsp)
  if canonical target then
    return { state.writeRegister .rsp (state.registers .rsp + 8) with rip := target }
  else
    throw (.noncanonicalReturn target)

inductive StepResult where
  | next (state : State)
  | returned (state : State)

def step (state : State) : Except Error StepResult := do
  match ← decodeAt state with
  | .leaEaxRdiDisp8 displacement => return .next (executeLea state displacement)
  | .loadEaxRdi => return .next (← executeLoad state)
  | .storeEsiRdi => return .next (← executeStore state)
  | .ret => return .returned (← executeRet state)

structure Execution where
  state : State
  instructions : Nat

/-- Fuel bounds the supported evaluator, not a claim about arbitrary executions.
Returning through a validated near RET is the function observation boundary. -/
def run : Nat → State → Except Error Execution
  | 0, _ => .error .exhaustedFuel
  | fuel + 1, state => do
    match ← step state with
    | .returned final => return ⟨final, 1⟩
    | .next next =>
      let result ← run fuel next
      return { result with instructions := result.instructions + 1 }


end EDSL.X86
