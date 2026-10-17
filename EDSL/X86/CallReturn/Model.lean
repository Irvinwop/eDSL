/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Machine

namespace EDSL.X86.CallReturn

abbrev Read := Sequential.Read
abbrev Observation := Sequential.Observation

/-- Encoding shape matters: even a SIB without an index occupies a byte.
All forms here use mod=01, so RBP/R13 are real bases. -/
inductive Address where
  | plain (base : Register)
  | sib (base : Register) (index : Option Register) (scale : Fin 4)
  deriving DecidableEq, Repr

def Address.eval (address : Address) (state : State) : Word :=
  match address with
  | .plain base => state.registers base
  | .sib base none _ => state.registers base
  | .sib base (some index) scale => state.registers base + (state.registers index <<< scale.val)

/-- Additive sibling ISA. A prefix-presence bit records PUSH/POP length; the
REX R/X/W bits have no semantic effect for these opcode-register forms.
Constructed combinations need not have a decoding. -/
inductive Instruction where
  | sequential (instruction : Sequential.Instruction)
  | callRelative32 (displacement : BitVec 32)
  | push64 (source : Register) (prefixed : Bool)
  | pop64 (destination : Register) (prefixed : Bool)
  | leaDisp8 (destination : Register) (address : Address) (displacement : Byte)
  deriving DecidableEq, Repr

def stackLength (prefixed : Bool) : Nat := if prefixed then 2 else 1

def Instruction.length : Instruction → Nat
  | .sequential old => old.length
  | .callRelative32 _ => 5
  | .push64 _ prefixed | .pop64 _ prefixed => stackLength prefixed
  | .leaDisp8 _ (.plain _) _ => 4
  | .leaDisp8 _ (.sib _ _ _) _ => 5

theorem Instruction.length_pos (instruction : Instruction) : 0 < instruction.length := by
  cases instruction with
  | sequential old => exact old.length_pos
  | push64 _ p | pop64 _ p => cases p <;> simp [Instruction.length, stackLength]
  | leaDisp8 _ a _ => cases a <;> simp [Instruction.length]
  | callRelative32 _ => simp [Instruction.length]

theorem Instruction.length_le_five (instruction : Instruction) : instruction.length ≤ 5 := by
  cases instruction with
  | sequential old => exact old.length_le_five
  | push64 _ p | pop64 _ p => cases p <;> simp [Instruction.length, stackLength]
  | leaDisp8 _ a _ => cases a <;> simp [Instruction.length]
  | callRelative32 _ => simp [Instruction.length]

def Instruction.isExtension : Instruction → Bool
  | .sequential _ => false
  | _ => true

def Instruction.operandReads (instruction : Instruction) (state : State) : List Read :=
  match instruction with
  | .sequential old => old.operandReads state
  | .pop64 _ _ => [⟨.stack, state.registers .rsp, 8⟩]
  | _ => []

/-- Stack writes have their own classification; they are never ordinary DATA
store intents and this classification confers no resource authority. -/
inductive WriteEffect where
  | embeddedData32 (address : Word) (value : BitVec 32)
  | embeddedData64 (address value : Word)
  | callPush64 (address returnAddress : Word)
  | pushStack64 (address value : Word)
  deriving DecidableEq, Repr

def returnAddress (state : State) : Word := state.rip + 5

def callTarget (state : State) (displacement : BitVec 32) : Word :=
  returnAddress state + displacement.signExtend 64

def stackDestination (state : State) : Word := state.registers .rsp - 8

def Instruction.storeIntent (instruction : Instruction) (state : State) : Option (Word × BitVec 32) :=
  match instruction with
  | .sequential old => old.storeIntent state
  | _ => none

def Instruction.storeIntent64 (instruction : Instruction) (state : State) : Option (Word × Word) :=
  match instruction with
  | .sequential old => old.storeIntent64 state
  | _ => none

def Instruction.writeEffect (instruction : Instruction) (state : State) : Option WriteEffect :=
  match instruction with
  | .sequential old =>
    match old.storeIntent state with
    | some (address, value) => some (.embeddedData32 address value)
    | none => match old.storeIntent64 state with
      | some (address, value) => some (.embeddedData64 address value)
      | none => none
  | .callRelative32 _ => some (.callPush64 (stackDestination state) (returnAddress state))
  | .push64 source _ => some (.pushStack64 (stackDestination state) (state.registers source))
  | _ => none

def Instruction.isLocked : Instruction → Bool
  | .sequential old => old.isLocked
  | _ => false

def Instruction.choosesAF : Instruction → Bool
  | .sequential old => old.choosesAF
  | _ => false

@[simp] theorem call_no_data_intent (state : State) (d : BitVec 32) :
    (Instruction.callRelative32 d).storeIntent state = none ∧
    (Instruction.callRelative32 d).storeIntent64 state = none := ⟨rfl, rfl⟩

@[simp] theorem push_no_data_intent (state : State) (r : Register) (p : Bool) :
    (Instruction.push64 r p).storeIntent state = none ∧
    (Instruction.push64 r p).storeIntent64 state = none := ⟨rfl, rfl⟩

end EDSL.X86.CallReturn
