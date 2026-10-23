/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.TestImmediate8
import EDSL.X86.Sequential.Code
import EDSL.X86.Sequential.Literals
import EDSL.X86.CallReturn.Machine

import tests.Support.ExceptDecidable

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.Tests.TestImmediate8
open scoped EDSL.Tests.Support
open X86 X86.Sequential

private def registers : Register → Word
  | .rax => 0x1122334455667781 | .rcx => 0x2132435465768702
  | .rdx => 0x3142536475869703 | .rbx => 0x415263748596a700
  | .rsp => 0x8000000000000080 | .rbp => 0x61728394a5b6c77f
  | .rsi => 0x718293a4b5c6d701 | .rdi => 0x8192a3b4c5d6e7ff
  | .r8 => 0x91a2b3c4d5e6f710 | .r9 => 0xa1b2c3d4e5f60711
  | .r10 => 0xb1c2d3e4f50617fe | .r11 => 0xc1d2e3f40516277f
  | .r12 => 0xd1e2f30415263780 | .r13 => 0xe1f2031425364781
  | .r14 => 0xf102132435465700 | .r15 => 0x0123456789abcdff

private def entry (bytes : List Byte) (flags : Word := 0xdeadbeef00000ed7)
    (input : Register → Word := registers) : State :=
  { codeState bytes 0 with registers := input, flags := flags }

private def view (operand : Register) (af : Bool) (before : State) :
    Except Error (Word × Word × Word × List Read) := do
  let observation ← Sequential.step af before
  match observation.result with
  | .next after => return (after.registers operand,after.flags,after.rip,observation.reads)
  | _ => throw .unexpectedReturn

/-- Frozen GCC ordinary-counter instruction, observed through the real public
decode and step. The full dirty RSI survives for both AF choices. -/
theorem needed_window :
    Sequential.decodeAt (entry [0x40,0xf6,0xc6,1]) = .ok (.testImm8 .rsi 1 true) ∧
    view .rsi false (entry [0x40,0xf6,0xc6,1]) =
      .ok (0x718293a4b5c6d701,0xdeadbeef00000602,4,[]) ∧
    view .rsi true (entry [0x40,0xf6,0xc6,1]) =
      .ok (0x718293a4b5c6d701,0xdeadbeef00000612,4,[]) := by
  refine ⟨?_,?_,?_⟩ <;> decide +kernel

/-- Explicit byte-bank expectations. Contrasting low bits and dirty upper
halves catch bank confusion, accidental writes and widened TEST semantics. -/
private def banks : List (List Byte × Register × Word × Word × Word) :=
  [([0xf6,0xc0,1],.rax,0x1122334455667781,0xdeadbeef00000602,0xdeadbeef00000612),
   ([0xf6,0xc1,1],.rcx,0x2132435465768702,0xdeadbeef00000646,0xdeadbeef00000656),
   ([0xf6,0xc2,1],.rdx,0x3142536475869703,0xdeadbeef00000602,0xdeadbeef00000612),
   ([0xf6,0xc3,1],.rbx,0x415263748596a700,0xdeadbeef00000646,0xdeadbeef00000656),
   ([0x40,0xf6,0xc4,1],.rsp,0x8000000000000080,0xdeadbeef00000646,0xdeadbeef00000656),
   ([0x40,0xf6,0xc5,1],.rbp,0x61728394a5b6c77f,0xdeadbeef00000602,0xdeadbeef00000612),
   ([0x40,0xf6,0xc6,1],.rsi,0x718293a4b5c6d701,0xdeadbeef00000602,0xdeadbeef00000612),
   ([0x40,0xf6,0xc7,1],.rdi,0x8192a3b4c5d6e7ff,0xdeadbeef00000602,0xdeadbeef00000612),
   ([0x41,0xf6,0xc0,1],.r8,0x91a2b3c4d5e6f710,0xdeadbeef00000646,0xdeadbeef00000656),
   ([0x41,0xf6,0xc1,1],.r9,0xa1b2c3d4e5f60711,0xdeadbeef00000602,0xdeadbeef00000612),
   ([0x41,0xf6,0xc2,1],.r10,0xb1c2d3e4f50617fe,0xdeadbeef00000646,0xdeadbeef00000656),
   ([0x41,0xf6,0xc3,1],.r11,0xc1d2e3f40516277f,0xdeadbeef00000602,0xdeadbeef00000612),
   ([0x41,0xf6,0xc4,1],.r12,0xd1e2f30415263780,0xdeadbeef00000646,0xdeadbeef00000656),
   ([0x41,0xf6,0xc5,1],.r13,0xe1f2031425364781,0xdeadbeef00000602,0xdeadbeef00000612),
   ([0x41,0xf6,0xc6,1],.r14,0xf102132435465700,0xdeadbeef00000646,0xdeadbeef00000656),
   ([0x41,0xf6,0xc7,1],.r15,0x0123456789abcdff,0xdeadbeef00000602,0xdeadbeef00000612)]

theorem all_banks :
    banks.all (fun (bytes,operand,word,clearFlags,setFlags) =>
      (Sequential.decodeAt (entry bytes)).toOption ==
        some (.testImm8 operand 1 (bytes.length == 4)) &&
      (view operand false (entry bytes)).toOption ==
        some (word,clearFlags,BitVec.ofNat 64 bytes.length,[]) &&
      (view operand true (entry bytes)).toOption ==
        some (word,setFlags,BitVec.ofNat 64 bytes.length,[])) = true := by decide +kernel

/-- Bit7 drives SF at width8; parity observes the masked byte. Immediate 80/FF
is never sign-extended into the dirty upper operand bits. -/
theorem raw_immediate_and_flags :
    (view .rax false (entry [0xf6,0xc0,0]),
      view .rax false (entry [0xf6,0xc0,0x80]),
      view .rax false (entry [0xf6,0xc0,0xff]),
      view .rdx false (entry [0xf6,0xc2,0xff]),
      view .rbp false (entry [0x40,0xf6,0xc5,0xff]),
      view .rsi false (entry [0x40,0xf6,0xc6,0xfe]),
      view .rdi true (entry [0x40,0xf6,0xc7,0xff])) =
    (.ok (0x1122334455667781,0xdeadbeef00000646,3,[]),
      .ok (0x1122334455667781,0xdeadbeef00000682,3,[]),
      .ok (0x1122334455667781,0xdeadbeef00000686,3,[]),
      .ok (0x3142536475869703,0xdeadbeef00000606,3,[]),
      .ok (0x61728394a5b6c77f,0xdeadbeef00000602,4,[]),
      .ok (0x718293a4b5c6d701,0xdeadbeef00000646,4,[]),
      .ok (0x8192a3b4c5d6e7ff,0xdeadbeef00000696,4,[])) := by
  simp only [Prod.mk.injEq]
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- AF is neither preserved nor fixed. In each row it changes away from the
old bit, while CF/OF are cleared and all unrelated flag bits survive. -/
theorem undefined_AF_is_a_choice :
    view .rsi false (entry [0x40,0xf6,0xc6,1] 0xdeadbeef00000ed7) =
      .ok (0x718293a4b5c6d701,0xdeadbeef00000602,4,[]) ∧
    view .rsi true (entry [0x40,0xf6,0xc6,1] 0xdeadbeef00000ec7) =
      .ok (0x718293a4b5c6d701,0xdeadbeef00000612,4,[]) := by
  constructor <;> decide +kernel

theorem canonical_low_bank_aliases :
    ([([0x40,0xf6,0xc0,1],.rax),([0x40,0xf6,0xc1,1],.rcx),
      ([0x40,0xf6,0xc2,1],.rdx),([0x40,0xf6,0xc3,1],.rbx)] :
      List (List Byte × Register)).all (fun (bytes,operand) =>
        (Sequential.decodeAt (entry bytes)).toOption == some (.testImm8 operand 1 true)) = true :=
  by decide +kernel

theorem actual_decode_metadata :
    ((Sequential.decodeAt (entry [0x40,0xf6,0xc6,1])).map (fun instruction =>
      (instruction.choosesAF,instruction.choiceFlag (entry []),
       instruction.undefinedFlags (entry []),instruction.boolChoiceProfile))) =
      .ok (true,some .af,[.af],true) := by rfl

private def vectorView (choices : FlagChoices) : Except Error (Word × Word × List Read) := do
  let observation ← stepWith choices (entry [0x40,0xf6,0xc6,1])
  match observation.result with
  | .next after => return (after.flags,after.rip,observation.reads)
  | _ => throw .unexpectedReturn

theorem vector_projects_only_AF :
    (vectorView ⟨true,true,false,true,true,true⟩,
      vectorView ⟨false,false,true,false,false,false⟩,
      vectorView ⟨false,false,false,false,false,false⟩) =
    (.ok (0xdeadbeef00000602,4,[]),.ok (0xdeadbeef00000612,4,[]),
      .ok (0xdeadbeef00000602,4,[])) := by
  simp only [Prod.mk.injEq]
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- Arbitrary full64 GPRs and every RAM/permission bit are framed by actual
production execution, including an arbitrary old RSP and all upper halves. -/
theorem arbitrary_production_frame {before : State} {operand : Register} {immediate : Byte}
    {prefixed : Bool} (decoded : Sequential.decodeAt before = .ok (.testImm8 operand immediate prefixed))
    (af : Bool) :
    ∃ after, Sequential.step af before = .ok ⟨.next after, []⟩ ∧
      after.registers = before.registers ∧ after.memory = before.memory ∧
      after.flags &&& ~~~arithmeticFlagMask = before.flags &&& ~~~arithmeticFlagMask ∧
      after.flags.getLsbD 4 = af := by
  obtain ⟨after, executed, context⟩ := execute_testImm8_context before operand immediate prefixed af
  exact ⟨after, (step_eq_execute af decoded).trans executed, context.registers,
    context.memory, context.frame, context.auxiliary⟩

/-- No-prefix codes4..7 mean AH/CH/DH/BH, not the low-byte bank. Missing
immediates must not conceal unsupported memory, selectors or aliases. -/
theorem rejection_before_unneeded_fetch :
    ([[0xf6,0xc4],[0xf6,0xc5],[0xf6,0xc6],[0xf6,0xc7],
      [0xf6,0xc8],[0xf6,0xd0],[0xf6,0xd8],[0xf6,0xe0],
      [0xf6,0xe8],[0xf6,0xf0],[0xf6,0xf8],
      [0xf6,0x00],[0xf6,0x04],[0xf6,0x40],[0xf6,0x80],
      [0x40,0xf6,0xc8],[0x41,0xf6,0xff],[0x40,0xf6,0x04],
      [0x42,0xf6],[0x43,0xf6],[0x44,0xf6],[0x45,0xf6],[0x46,0xf6],[0x47,0xf6],
      [0x48,0xf6],[0x49,0xf6],[0x4a,0xf6],[0x4b,0xf6],[0x4c,0xf6],[0x4d,0xf6],
      [0x4e,0xf6],[0x4f,0xf6],[0x66,0xf6],[0xf0,0xf6],[0xf3,0xf6],
      [0x40,0x40],[0x40,0x41]] : List (List Byte)).all (fun bytes =>
        match Sequential.step false (entry bytes) with
        | .error .unsupportedEncoding => true | _ => false) = true ∧
    Sequential.decodeAt (entry [0x67]) = .error (.unsupportedOpcode 0x67) := by decide +kernel

theorem exact_truncations :
    ([([],0),([0xf6],1),([0xf6,0xc0],2),([0xf6,0xc3],2),
      ([0x40],1),([0x40,0xf6],2),([0x40,0xf6,0xc6],3),
      ([0x41,0xf6],2),([0x41,0xf6,0xc4],3)] : List (List Byte × Word)).all
      (fun (bytes,address) => match Sequential.step true (entry bytes) with
        | .error (.inaccessibleInstruction actual) => actual == address | _ => false) = true :=
  by decide +kernel

theorem required_read_and_execute_permissions :
    ([([0xf6,0xc0,0x80],0),([0xf6,0xc0,0x80],1),([0xf6,0xc0,0x80],2),
      ([0x40,0xf6,0xc6,1],0),([0x40,0xf6,0xc6,1],1),
      ([0x40,0xf6,0xc6,1],2),([0x40,0xf6,0xc6,1],3),
      ([0x41,0xf6,0xc4,0xff],3)] : List (List Byte × Word)).all (fun (bytes,denied) =>
        let before := entry bytes
        let noExecute := { before with memory := { before.memory with
          executable := fun address => before.memory.executable address && address != denied } }
        let noRead := { before with memory := { before.memory with
          read := fun address => if address = denied then none else before.memory.read address } }
        (match Sequential.step false before with | .ok _ => true | _ => false) &&
        (match Sequential.step false noExecute with
          | .error (.inaccessibleInstruction address) => address == denied | _ => false) &&
        (match Sequential.step false noRead with
          | .error (.inaccessibleInstruction address) => address == denied | _ => false)) = true :=
  by decide +kernel

private def crossingHole : State where
  registers := registers
  rip := 0x7ffffffffffd
  flags := 0xdeadbeef00000ed7
  memory := {
    read := fun address => ([0x40,0xf6,0xc6,1] : List Byte)[(address - 0x7ffffffffffd).toNat]?
    executable := fun _ => true }

theorem canonical_fetch_boundary :
    Sequential.step true crossingHole = .error (.inaccessibleInstruction 0x800000000000) := by rfl

theorem needed_immediate_is_not_optional :
    (view .rsi false (entry [0x40,0xf6,0xc6,1]),
      view .rsi false (entry [0x40,0xf6,0xc6,2])) =
    (.ok (0x718293a4b5c6d701,0xdeadbeef00000602,4,[]),
      .ok (0x718293a4b5c6d701,0xdeadbeef00000646,4,[])) := by
  simp only [Prod.mk.injEq]
  exact ⟨by decide +kernel, by decide +kernel⟩

theorem sibling_and_literal :
    CallReturn.decodeAt (entry [0x40,0xf6,0xc6,1]) =
      .ok (.sequential (.testImm8 .rsi 1 true)) ∧
    Literals.instruction (.testImm8 .r12 0x80 true) = "(.testImm8 .r12 128 true)" := by
  constructor <;> decide +kernel

end EDSL.Tests.TestImmediate8
