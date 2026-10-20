/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.LockedLogical64.Execution

namespace EDSL.X86.LockedSet64

/-- Exact full64 locked logical/RET profile. Physical interpretation requires
normal four-level user controls, CET off, stable code/private context and the
WB/coherence/translation/no-alias assumptions of `atomicAddressable64`.
Atomic-object initialization/lifetime and scheduling remain external. -/
inductive Instruction where
  | logicalRdiRsi (op : Sequential.LogicalOp)
  | ret
  deriving DecidableEq, Repr

def logicalOpcode : Sequential.LogicalOp → Byte
  | .band => 0x21
  | .bor => 0x09
  | .bxor => 0x31

def Instruction.bytes : Instruction → List Byte
  | .logicalRdiRsi op => [0xf0, 0x48, logicalOpcode op, 0x37]
  | .ret => [0xc3]

def Instruction.length (instruction : Instruction) : Nat := instruction.bytes.length

abbrev Access := LockedLogical64.Access
abbrev StepResult := LockedLogical64.StepResult
abbrev Observation := LockedLogical64.Observation
abbrev AccessSucceeds := LockedLogical64.AccessSucceeds

def Instruction.accesses (instruction : Instruction) (state : State) : List Access :=
  match instruction with
  | .logicalRdiRsi _ => [.rmw8 (state.registers .rdi)]
  | .ret => [.stack8 (state.registers .rsp)]

end EDSL.X86.LockedSet64
