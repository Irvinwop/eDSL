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
  | baseDisp8 (base : Register) (displacement : Byte)
  | sibDisp8 (base : Register) (index : Option Register) (scale : Fin 4) (displacement : Byte)
  deriving DecidableEq, Repr

def Address.eval (address : Address) (state : State) : Word :=
  match address with
  | .base register => state.registers register
  | .indexed baseReg index scale => state.registers baseReg + (state.registers index <<< scale.val)
  | .baseDisp8 baseReg displacement => state.registers baseReg + displacement.signExtend 64
  | .sibDisp8 baseReg index scale displacement =>
    (match index with
      | none => state.registers baseReg
      | some index => state.registers baseReg + (state.registers index <<< scale.val)) +
      displacement.signExtend 64

/-- Encoded bytes after ModRM. SIB and explicit zero displacements retain
their original lengths even when they do not change the computed value. -/
@[simp] def Address.suffixBytes : Address → Nat
  | .base _ => 0
  | .indexed _ _ _ | .baseDisp8 _ _ => 1
  | .sibDisp8 _ _ _ _ => 2

/-- Full-width logical operations. The destination and source are both read
before any register update, including when the registers alias. -/
inductive LogicalOp where
  | band | bor | bxor
  deriving DecidableEq, Repr

def LogicalOp.eval (operation : LogicalOp) (left right : Word) : Word :=
  match operation with
  | .band => left &&& right
  | .bor => left ||| right
  | .bxor => left ^^^ right

/-- Exact supported alignment encodings from Intel SDM NOP, lengths 1..5 and 9
bytes. These are instruction encodings, not a general prefix grammar. The
multi-byte forms require a processor supporting 0F 1F /0. Their apparent
address operands are never evaluated and cause no operand memory access. -/
inductive NopEncoding where
  | one | two | three | four | five | nine
  deriving DecidableEq, Repr

/-- Environmental contract of the selected sequential target, outside the
modeled GPR/RFLAGS/RAM state. Hardware correspondence assumes 64-bit mode,
CET indirect-branch tracking and shadow stacks disabled, and support for
multi-byte NOP. These are assumptions, not facts established by decoding. -/
structure TargetProfile where
  longMode : Bool
  ibtEnabled : Bool
  shadowStackEnabled : Bool
  multiByteNop : Bool
  deriving DecidableEq, Repr

def targetProfile : TargetProfile := ⟨true, false, false, true⟩

/-- A separate sequential ISA extension. Existing deterministic and concurrent
decoders keep their original supported subset. -/
inductive Instruction where
  | legacy (instruction : X86.Instruction)
  | xorSelf32 (destination : Register)
  /-- Low32 register TEST; `prefixed` records one non-W REX byte for length.
  No GPR is written, and AF is an independent undefined choice. -/
  | test32 (left right : Register) (prefixed : Bool)
  /-- Low32 register CMP, left minus right, with no register write. -/
  | cmp32 (left right : Register) (prefixed : Bool)
  /-- LOW8 register CMP, left minus right. Without REX only AL/CL/DL/BL
  decode; with REX every low-byte GPR is available. No high-byte bank is modeled. -/
  | cmpReg8 (left right : Register) (prefixed : Bool)
  /-- LOW32 register subtraction using prestate operands and defined arithmetic
  flags. The destination's upper32 bits are cleared, including self-aliases. -/
  | subReg32 (destination source : Register) (prefixed : Bool)
  /-- Register-only low32 two's-complement negation. The source is the old
  destination, the full destination is zero extended, and all six arithmetic
  flags (including AF) are defined by subtraction from zero. Prefix presence
  records the canonical optional 40/41 REX byte, not a different operation. -/
  | negReg32 (destination : Register) (prefixed : Bool)
  /-- Register-only full64 byte reversal, with every modeled flag preserved.
  Canonical bytes are 48/49 0F C8+rd; REX.B selects the high register bank. -/
  | bswapReg64 (destination : Register)
  /-- Register-only logical right shift by exactly one at full width. CF is
  the old low bit, OF the old high bit; AF is an independent undefined choice.
  One REX.W D1 /5 encoding, with B selecting the destination and R/X ignored. -/
  | shrOne64 (destination : Register)
  /-- MOVZX r32, r/m8. Exactly one DATA1 read at the full64 prestate address;
  the complete destination is the zero-extended byte and all flags survive. -/
  | movzxMem8 (destination : Register) (address : Address) (prefixed : Bool)
  /-- MOVZX r32, LOW8 source. The source is captured before any destination
  update. Prefix presence distinguishes low-byte banks and instruction length. -/
  | movzxReg8 (destination source : Register) (prefixed : Bool)
  /-- Unprefixed 80 /7 ib with an existing mod=00 address. Reads one DATA byte,
  subtracts the immediate at width eight, and writes only arithmetic flags. -/
  | cmpMemImm8 (address : Address) (immediate : Byte)
  /-- Unprefixed 38 /r, memory left minus LOW8 source. The decoder admits
  AL/CL/DL/BL only; high-byte registers and all prefixes are unsupported. -/
  | cmpMemReg8 (address : Address) (source : Register)
  /-- Unprefixed 39 /r, memory left minus LOW32 source, with one DATA4 read. -/
  | cmpMemReg32 (address : Address) (source : Register)
  /-- Exactly F3 0F 1E FA. Its no-op interpretation is restricted to
  `targetProfile`, with CET/IBT disabled; no CET tracker is modeled. -/
  | endbr64IbtDisabled
  | nop (encoding : NopEncoding)
  | test64 (left right : Register)
  | cmp64 (left right : Register)
  | addMem32 (destination : Register) (address : Address)
  /-- Full-width ordinary DATA-source addition. Both the old destination and
  effective address are captured before writing, including register aliases. -/
  | addMem64 (destination : Register) (address : Address)
  /-- A 32-bit register copy; the destination is zero-extended to 64 bits. -/
  | movReg32 (destination source : Register)
  /-- A full-width register copy, encoded with one REX.W prefix. -/
  | movReg64 (destination source : Register)
  /-- Register-only REX.W C7 /0 id. Sign-extend the complete imm32 into the
  full64 destination, preserving FLAGS and requiring no operand memory. -/
  | movSignImm32 (destination : Register) (immediate : BitVec 32)
  /-- Register-only conditional full-width copy. The false case retains the
  complete destination; flags and operand memory are unchanged. -/
  | cmovReg64 (condition : Condition) (destination source : Register)
  /-- Register-only low32 conditional copy. Both outcomes zero the upper half
  of the destination, including a false condition. One optional non-W REX
  prefix is recorded for the exact instruction length. Flags are unchanged. -/
  | cmovReg32 (condition : Condition) (destination source : Register) (prefixed : Bool)
  /-- Full-width effective-address arithmetic. It performs no data access and
  preserves every flag, including when the computed value is noncanonical. -/
  | lea64 (destination : Register) (address : Address)
  /-- Register-register addition with full-width result and arithmetic flags. -/
  | addReg64 (destination source : Register)
  /-- Register-only full-width AND/OR/XOR, with an independent undefined AF
  choice. This is an ordinary instruction, not a locked operation. -/
  | logicalReg64 (operation : LogicalOp) (destination source : Register)
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
  /-- Register-only 83 /0 ib, arithmetic at width32 with a signed imm8 and
  full zero extension of the destination. Prefix presence records 40/41. -/
  | addImm32 (destination : Register) (immediate : Byte) (prefixed : Bool)
  /-- Register-only FF /0. Arithmetic at width32, upper32 clearing, incoming
  CF preserved. All other arithmetic status flags are defined. -/
  | inc32 (destination : Register) (prefixed : Bool)
  | inc64 (destination : Register)
  | dec64 (destination : Register)
  | je (displacement : Byte)
  /-- Short conditional control flow using the incoming architectural flags.
  Decoder compatibility retains opcode 74 as `je` and opcode 75 as legacy JNZ. -/
  | jcc (condition : Condition) (displacement : Byte)
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
