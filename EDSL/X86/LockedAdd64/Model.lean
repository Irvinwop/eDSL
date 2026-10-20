/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.AtomicAdd64
import EDSL.X86.Sequential.Decode

namespace EDSL.X86.LockedAdd64

/-- Exactly mod=00 with a real GPR base and no SIB/displacement. Low encoding
4 requires SIB (including R12); 5 requires RIP-relative/displacement handling
(including R13). Neither is admitted. -/
def indirect64 (modrm : Byte) : Bool :=
  decide (modrm.toNat < 64 ∧ modrm.toNat % 8 ≠ 4 ∧ modrm.toNat % 8 ≠ 5)

/-- One reusable LOCK XADD qword family, retaining the exact encoded REX and
ModRM, including the ignored X bit. In 64-bit mode X extends only a SIB index;
there is no SIB in this subset. R/B extend the source/base independently.
Source is any of the sixteen GPRs, including RSP and base/source aliases.

Physical interpretation assumes long mode, CET disabled and the environmental
WB/translation/alias boundary documented by `atomicAddressable64`. This family
has a separate dispatch step; it is not integrated into Sequential, an OS
resource model, a scheduler or a physical LOCK refinement. -/
structure Instruction where
  rex : Byte
  modrm : Byte
  rexW : Sequential.rexWPrefix rex = true
  indirect : indirect64 modrm = true
  deriving DecidableEq, Repr

def Instruction.base (instruction : Instruction) : Register :=
  Sequential.rexModRMRM instruction.rex instruction.modrm

def Instruction.source (instruction : Instruction) : Register :=
  Sequential.rexModRMReg instruction.rex instruction.modrm

def Instruction.bytes (instruction : Instruction) : List Byte :=
  [0xf0, instruction.rex, 0x0f, 0xc1, instruction.modrm]

def Instruction.length (_ : Instruction) : Nat := 5

@[simp] theorem Instruction.bytes_length (instruction : Instruction) :
    instruction.bytes.length = instruction.length := rfl

/-- This named encoding is only a corollary client of the generic family. -/
def frozen : Instruction := ⟨0x48, 0x07, by decide, by decide⟩

/-- Joint eight-byte read/write intent, using the original register file.
Fetches and validation queries are separate from this operand footprint. -/
inductive Access where
  | rmw8 (address : Word)
  deriving DecidableEq, Repr

def Instruction.accesses (instruction : Instruction) (state : State) : List Access :=
  [.rmw8 (state.registers instruction.base)]

def AccessSucceeds (state : State) : Access → Prop
  | .rmw8 address => dataOnly64 state.memory address = true ∧
      atomicAddressable64 address = true ∧ canStoreQWord state.memory address = true ∧
      ∃ old, loadQWord state.memory address = .ok old

/-- There is exactly one full-width arithmetic event and one final state on
success. The error alternative of Except contains neither a state nor an event. -/
structure Observation where
  event : FetchAddEvent64
  state : State
  accesses : List Access

end EDSL.X86.LockedAdd64
