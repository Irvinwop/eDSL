/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.LockedAdd64.Model
import EDSL.X86.Sequential.Flags

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.X86.AddRMW64

/-- The initial ADD/INC profile admits W=1, R=X=0 and either B bank.
This restriction is deliberately independent of the legacy XADD profile. -/
def rexBasePrefix (rex : Byte) : Bool := rex == 0x48 || rex == 0x49

/-- Exact LOCK REX.W 83 /0 ib, with a real mod00 base, no SIB or displacement. -/
structure AddImm8Encoding where
  rex : Byte
  modrm : Byte
  imm8 : Byte
  rexSupported : rexBasePrefix rex = true
  indirect : LockedAdd64.indirect64 modrm = true
  groupZero : modrm.toNat / 8 % 8 = 0
  deriving DecidableEq, Repr

/-- Exact LOCK REX.W FF /0 under the same addressing restrictions. -/
structure IncEncoding where
  rex : Byte
  modrm : Byte
  rexSupported : rexBasePrefix rex = true
  indirect : LockedAdd64.indirect64 modrm = true
  groupZero : modrm.toNat / 8 % 8 = 0
  deriving DecidableEq, Repr

inductive Instruction where
  | xadd (old : LockedAdd64.Instruction)
  | addImm8 (encoding : AddImm8Encoding)
  | inc (encoding : IncEncoding)
  deriving DecidableEq, Repr

def Instruction.base : Instruction → Register
  | .xadd old => old.base
  | .addImm8 encoding => Sequential.rexModRMRM encoding.rex encoding.modrm
  | .inc encoding => Sequential.rexModRMRM encoding.rex encoding.modrm

/-- Both the address and this delta are read before any register writeback. -/
def Instruction.delta : Instruction → State → Word
  | .xadd old, state => state.registers old.source
  | .addImm8 encoding, _ => encoding.imm8.signExtend 64
  | .inc _, _ => 1

def Instruction.oldDestination : Instruction → Option Register
  | .xadd old => some old.source
  | .addImm8 _ | .inc _ => none

def Instruction.bytes : Instruction → List Byte
  | .xadd old => old.bytes
  | .addImm8 encoding => [0xf0, encoding.rex, 0x83, encoding.modrm, encoding.imm8]
  | .inc encoding => [0xf0, encoding.rex, 0xff, encoding.modrm]

def Instruction.length : Instruction → Nat
  | .xadd old => old.length
  | .addImm8 _ => 5
  | .inc _ => 4

@[simp] theorem Instruction.bytes_length (instruction : Instruction) :
    instruction.bytes.length = instruction.length := by cases instruction <;> rfl

def Instruction.isInc : Instruction → Bool
  | .inc _ => true
  | .xadd _ | .addImm8 _ => false

/-- No invented destination register for ADD/INC. XADD receives the entire
old qword, including aliases of the base and the RSP source case. -/
def Instruction.registersAfter (instruction : Instruction) (state : State)
    (event : FetchAddEvent64) : Register → Word :=
  match instruction.oldDestination with
  | some destination => (state.writeRegister destination event.event.before).registers
  | none => state.registers

def Instruction.flagsAfter (instruction : Instruction) (incoming before delta : Word) : Word :=
  match instruction with
  | .xadd _ | .addImm8 _ => Sequential.addFlags64 incoming before delta
  | .inc _ => Sequential.incFlags64 incoming before

theorem Instruction.flagsAfter_preserves (instruction : Instruction) (incoming before delta : Word) :
    instruction.flagsAfter incoming before delta &&& ~~~arithmeticFlagMask =
      incoming &&& ~~~arithmeticFlagMask := by
  cases instruction with
  | xadd _ => exact Sequential.addFlags64_preserves ..
  | addImm8 _ => exact Sequential.addFlags64_preserves ..
  | inc _ => exact Sequential.incFlags64_preserves ..

/-- The common five arithmetic bits use the captured full-width delta.
CF is explicitly tag-sensitive; an ADD carry law would be false for INC. -/
theorem Instruction.flagsAfter_bits (instruction : Instruction) (state : State) (before : Word) :
    (instruction.flagsAfter state.flags before (instruction.delta state)).getLsbD 0 =
      (if instruction.isInc then state.flags.getLsbD 0 else before.uaddOverflow (instruction.delta state)) ∧
    (instruction.flagsAfter state.flags before (instruction.delta state)).getLsbD 2 =
      evenParity ((before + instruction.delta state).setWidth 8) ∧
    (instruction.flagsAfter state.flags before (instruction.delta state)).getLsbD 4 =
      (before.setWidth 4).uaddOverflow ((instruction.delta state).setWidth 4) ∧
    (instruction.flagsAfter state.flags before (instruction.delta state)).getLsbD 6 =
      (before + instruction.delta state == 0) ∧
    (instruction.flagsAfter state.flags before (instruction.delta state)).getLsbD 7 =
      (before + instruction.delta state).msb ∧
    (instruction.flagsAfter state.flags before (instruction.delta state)).getLsbD 11 =
      before.saddOverflow (instruction.delta state) := by
  cases instruction with
  | xadd _ => exact Sequential.addFlags64_bits ..
  | addImm8 _ => exact Sequential.addFlags64_bits ..
  | inc _ => exact Sequential.incFlags64_bits ..

abbrev Access := LockedAdd64.Access
abbrev AccessSucceeds := LockedAdd64.AccessSucceeds
abbrev Observation := LockedAdd64.Observation

def Instruction.accesses (instruction : Instruction) (state : State) : List Access :=
  [.rmw8 (state.registers instruction.base)]

/-- Registers, PC and flags are derived from the same prestate as the RMW.
Physical LOCK refinement is outside this abstract machine; see the ISA note. -/
def afterRmw (state : State) (instruction : Instruction) (memory : Memory)
    (event : FetchAddEvent64) : State :=
  { state with
    registers := instruction.registersAfter state event
    memory := memory
    rip := state.rip + BitVec.ofNat 64 instruction.length
    flags := instruction.flagsAfter state.flags event.event.before (instruction.delta state) }

end EDSL.X86.AddRMW64
