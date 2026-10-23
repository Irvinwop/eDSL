/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.MachineChoices
import EDSL.X86.Sequential.Code
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Owned synthetic byte-level controls. Literal expected results distinguish
logical/arithmetic shifts, low32 zero extension, old-bit carry, count masking,
count-one overflow and independent AF/OF. No native-processor claim is made.
-/

namespace EDSL.Tests.SequentialShiftRight32
open X86 X86.Sequential

private def entry (bytes : List Byte) (value : Word := 0x1234567880000001)
    (flags : Word := 0x602) : State :=
  { codeState bytes 0 with registers := fun _ => value, flags := flags }

private structure Snapshot where
  destination : Word
  flags : Word
  rip : Word
  reads : List Read
  deriving DecidableEq, Repr

private def snapshot (choices : FlagChoices) (initial : State)
    (destination : Register := .rax) : Option Snapshot :=
  match stepWith choices initial with
  | .ok ⟨.next final, reads⟩ =>
    some ⟨final.registers destination, final.flags, final.rip, reads⟩
  | _ => none

private def choices (af of : Bool) : FlagChoices :=
  ⟨true, true, af, true, true, of⟩

/-- All four undefined-flag patterns are tested independently against literal
RFLAGS words. Defined PF/ZF/SF/CF ignore the deliberately conflicting choices. -/
theorem independent_af_of_words :
    ([choices false false, choices false true, choices true false, choices true true] :
      List FlagChoices).map (fun selected =>
        snapshot selected (entry [0xc1,0xe8,31])) =
      [some ⟨1,0x602,3,[]⟩,some ⟨1,0xe02,3,[]⟩,
       some ⟨1,0x612,3,[]⟩,some ⟨1,0xe12,3,[]⟩] := by
  decide +kernel

/-- SAR sign-fills at width32 and then zero-extends; signed -3 divided by two
rounds down to -2. SHR instead fills zero. Incoming high32 bits do not shift in. -/
theorem sign_and_width_corners :
    [snapshot (choices false false) (entry [0xc1,0xf8,31]),
     snapshot (choices false false) (entry [0xc1,0xf8,1] 0xdeadbeeffffffffd),
     snapshot (choices false false) (entry [0xc1,0xe8,1] 0xdeadbeeffffffffd),
     snapshot (choices false false) (entry [0xc1,0xe8,31] 0xdeadbeef40000000),
     snapshot (choices false false) (entry [0xc1,0xf8,31] 0xdeadbeef40000000)] =
    [some ⟨0xffffffff,0x686,3,[]⟩,
     some ⟨0xfffffffe,0x683,3,[]⟩,
     some ⟨0x7ffffffe,0xe03,3,[]⟩,
     some ⟨0,0x647,3,[]⟩,
     some ⟨0,0x647,3,[]⟩] := by
  decide +kernel

/-- Count-one overflow is defined and cannot be overridden by the OF field.
CF uses the old bit0 even when the new bit0 differs. -/
theorem count_one_defined_overflow :
    [snapshot (choices false false) (entry [0xc1,0xe8,1]),
     snapshot (choices false true) (entry [0xc1,0xe8,1]),
     snapshot (choices false false) (entry [0xc1,0xf8,1]),
     snapshot (choices false true) (entry [0xc1,0xf8,1])] =
    [some ⟨0x40000000,0xe07,3,[]⟩,some ⟨0x40000000,0xe07,3,[]⟩,
     some ⟨0xc0000000,0x687,3,[]⟩,some ⟨0xc0000000,0x687,3,[]⟩] := by
  decide +kernel

/-- Literal 63 masks to 31 and 33 masks to one, with the corresponding OF
contract. These expectations do not call the count-mask helper. -/
theorem masked_counts :
    [snapshot (choices false false) (entry [0xc1,0xe8,63]),
     snapshot (choices false true) (entry [0xc1,0xe8,33])] =
    [some ⟨1,0x602,3,[]⟩,some ⟨0x40000000,0xe07,3,[]⟩] := by
  decide +kernel

private def decoded (bytes : List Byte) (expected : Sequential.Instruction) : Bool :=
  match Sequential.decodeAt (entry bytes) with
  | .ok actual => actual == expected
  | .error _ => false

/-- B extends the GPR. R and X must not alter the /5 opcode group selector. -/
theorem rex_banks_and_group_selector :
    ([0x40,0x41,0x42,0x43,0x44,0x45,0x46,0x47] : List Byte).map (fun rex =>
      (Sequential.decodeAt (entry [rex,0xc1,0xe8,31])).toOption) =
    [some (.shiftRightImm32 .logical .rax 31 true),
     some (.shiftRightImm32 .logical .r8 31 true),
     some (.shiftRightImm32 .logical .rax 31 true),
     some (.shiftRightImm32 .logical .r8 31 true),
     some (.shiftRightImm32 .logical .rax 31 true),
     some (.shiftRightImm32 .logical .r8 31 true),
     some (.shiftRightImm32 .logical .rax 31 true),
     some (.shiftRightImm32 .logical .r8 31 true)] := by
  decide +kernel

/-- OR's two directions differ, R/B are independent, and old self-XOR remains
its own exact constructor. Low32 OR needs no second interpreter. -/
theorem logical_or_directions :
    decoded [0x09,0xc8] (.logicalReg32 .bor .rax .rcx false) = true ∧
    decoded [0x0b,0xc8] (.logicalReg32 .bor .rcx .rax false) = true ∧
    decoded [0x45,0x09,0xc8] (.logicalReg32 .bor .r8 .r9 true) = true ∧
    decoded [0x45,0x0b,0xc8] (.logicalReg32 .bor .r9 .r8 true) = true ∧
    decoded [0x31,0xc0] (.xorSelf32 .rax) = true := by
  decide +kernel

private def rejected (bytes : List Byte) : Bool :=
  match Sequential.decodeAt (entry bytes) with
  | .error _ => true
  | .ok _ => false

/-- Unsupported memory, width, zero-count, group, CL and extra-prefix forms
cannot silently acquire the supported register low32 contract. -/
theorem unsupported_forms :
    ([[0xc1,0xe8,0],[0xc1,0xe8,32],[0xc1,0xf8,64],
      [0xc1,0x28,31],[0xc1,0x68,0,31],[0xc1,0xa8,0,0,0,0,31],
      [0xc1,0xc0,31],[0xc1,0xe0,31],[0xc1,0xf0,31],
      [0x48,0xc1,0xe8,31],[0x66,0xc1,0xe8,31],
      [0xf0,0xc1,0xe8,31],[0xf3,0xc1,0xe8,31],
      [0x40,0x40,0xc1,0xe8,31],[0xd3,0xe8],
      [0x09,0x08],[0x0b,0x08]] : List (List Byte)).all rejected = true := by
  decide +kernel

private def faultAt (bytes : List Byte) (address : Word) : Bool :=
  match Sequential.decodeAt (entry bytes) with
  | .error (.inaccessibleInstruction actual) => actual == address
  | _ => false

/-- Every fetched byte, including the immediate, needs execute permission.
No byte after the encoded instruction is required. -/
theorem truncation_addresses :
    faultAt [] 0 = true ∧ faultAt [0xc1] 1 = true ∧
    faultAt [0xc1,0xe8] 2 = true ∧ faultAt [0x47] 1 = true ∧
    faultAt [0x47,0xc1] 2 = true ∧ faultAt [0x47,0xc1,0xe8] 3 = true := by
  decide +kernel

private def denied (offset : Word) : State :=
  let initial := entry [0x47,0xc1,0xe8,31]
  { initial with memory := { initial.memory with
      executable := fun address => if address = offset then false
        else initial.memory.executable address } }

theorem denied_required_bytes :
    ([0,1,2,3] : List Word).all (fun address =>
      match Sequential.decodeAt (denied address) with
      | .error (.inaccessibleInstruction actual) => actual == address
      | _ => false) = true := by
  decide +kernel

end EDSL.Tests.SequentialShiftRight32

#audit_edsl
