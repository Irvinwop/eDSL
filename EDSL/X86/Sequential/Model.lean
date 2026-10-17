/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Machine
import EDSL.X86.Memory64
import EDSL.X86.Sequential.Condition

namespace EDSL.X86.Sequential

/-- The selected ordinary addressing forms use full 64-bit registers. A SIB
scale is an exponent, so `scale = 2` multiplies the index by four. -/
inductive Address where
  | base (register : Register)
  | indexed (base index : Register) (scale : Fin 4)
  deriving DecidableEq, Repr

def Address.eval (address : Address) (state : State) : Word :=
  match address with
  | .base register => state.registers register
  | .indexed baseReg index scale => state.registers baseReg + (state.registers index <<< scale.val)

/-- A separate sequential ISA extension. Existing deterministic and concurrent
decoders keep their original supported subset. -/
inductive Instruction where
  | legacy (instruction : X86.Instruction)
  | xorSelf32 (destination : Register)
  | test64 (left right : Register)
  | cmp64 (left right : Register)
  | addMem32 (destination : Register) (address : Address)
  /-- A 32-bit register copy; the destination is zero-extended to 64 bits. -/
  | movReg32 (destination source : Register)
  /-- A full-width register copy, encoded with one REX.W prefix. -/
  | movReg64 (destination source : Register)
  /-- Register-only conditional full-width copy. The false case retains the
  complete destination; flags and operand memory are unchanged. -/
  | cmovReg64 (condition : Condition) (destination source : Register)
  /-- Full-width effective-address arithmetic. It performs no data access and
  preserves every flag, including when the computed value is noncanonical. -/
  | lea64 (destination : Register) (address : Address)
  /-- Register-register addition with full-width result and arithmetic flags. -/
  | addReg64 (destination source : Register)
  /-- Full-width register exchange using the ModRM encoding. -/
  | xchgReg64 (left right : Register)
  /-- Full-width exchange with RAX using the opcode-register encoding. -/
  | xchgRax64 (other : Register)
  | loadMem32 (destination : Register) (address : Address)
  | storeMem32 (address : Address) (source : Register)
  /-- Full-width ordinary DATA load with the pre-instruction address. -/
  | loadMem64 (destination : Register) (address : Address)
  /-- Full-width checked ordinary store; this is not a locked operation. -/
  | storeMem64 (address : Address) (source : Register)
  | addImm64 (destination : Register) (immediate : Byte)
  | inc64 (destination : Register)
  | dec64 (destination : Register)
  | je (displacement : Byte)
  | jmp (displacement : Byte)
  deriving DecidableEq, Repr

/-- Successful operand reads, separate from instruction fetches. -/
inductive ReadKind where
  | data | stack
  deriving DecidableEq, Repr

structure Read where
  kind : ReadKind
  address : Word
  bytes : Nat
  deriving DecidableEq, Repr

structure Observation where
  result : StepResult
  reads : List Read

end EDSL.X86.Sequential
