/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.AtomicMemory64

namespace EDSL.X86.LockedLogical64

/-- Separate exact-byte profile, with no enrollment in legacy32, ordinary
scalar64, TSO or grading engines. Physical interpretation additionally assumes
normal four-level user control state, CET off, stable code and private context,
and the WB/translation/no-alias boundary of `atomicAddressable64`. Native
atomic-object initialization/lifetime and OS scheduling remain external. -/
inductive Instruction where
  | orRdiRsi
  | ret
  deriving DecidableEq, Repr

def Instruction.bytes : Instruction → List Byte
  | .orRdiRsi => [0xf0, 0x48, 0x09, 0x37]
  | .ret => [0xc3]

def Instruction.length (instruction : Instruction) : Nat := instruction.bytes.length

/-- An RMW requires joint read/write authority. A stack loan can authorize
`stack8`; an ordinary data-read loan cannot authorize `rmw8`. Fetches and
permission queries are separate from these operand accesses. -/
inductive Access where
  | rmw8 (address : Word)
  | stack8 (address : Word)
  deriving DecidableEq, Repr

inductive StepResult where
  | atomic64 (event : LogicalEvent64) (state : State)
  | returned (state : State)

def StepResult.state : StepResult → State
  | .atomic64 _ state | .returned state => state

structure Observation where
  result : StepResult
  accesses : List Access

def Instruction.accesses (instruction : Instruction) (state : State) : List Access :=
  match instruction with
  | .orRdiRsi => [.rmw8 (state.registers .rdi)]
  | .ret => [.stack8 (state.registers .rsp)]

/-- Successful actual operand access, independent of future OS authority. -/
def AccessSucceeds (state : State) : Access → Prop
  | .rmw8 address => atomicAddressable64 address = true ∧
      dataOnly64 state.memory address = true ∧ canStoreQWord state.memory address = true ∧
      ∃ old, loadQWord state.memory address = .ok old
  | .stack8 address => ∃ target, readWord state.memory address = .ok target

end EDSL.X86.LockedLogical64
