/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Address32
import EDSL.X86.Sequential.Code
import EDSL.X86.Sequential.Literals
import EDSL.X86.CallReturn.Machine

import tests.Support.ExceptDecidable

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.Tests.Address32
open scoped EDSL.Tests.Support
open X86 X86.Sequential

private def registers : Register → Word
  | .rax => 0xfedcba9876543210 | .rcx => 0x100000001 | .rdx => 3
  | .rsp => 0x800000000001 | .rbp => 0x100000080 | .rsi => 0x100000000
  | .rdi => 0xffffffffffffffff | .r12 => 0x400000001 | .r13 => 0xffffffffffffff80
  | .r14 => 0x800000000000 | .r15 => 0xfffffffffffffff0
  | _ => 0xabcdef0123456789

/-- Only the instruction bytes are mapped. Effective addresses have no DATA
or stack mapping; execute permission ends exactly at the instruction. -/
private def entry (bytes : List Byte) (flags : Word := 0xfedcba9876543ed7) : State :=
  { codeState bytes 0 with registers := registers, flags := flags }

private def view (destination : Register) (choice : Bool) (before : State) :
    Except Error (Word × Word × Word × List Read) := do
  let observation ← Sequential.step choice before
  match observation.result with
  | .next after => return (after.registers destination, after.flags, after.rip, observation.reads)
  | _ => throw .unexpectedReturn

/-- Actual frozen instruction bytes. The borrow from a zero low32 base must
produce 0x00000000ffffffff, with the complete incoming flags retained. -/
theorem needed_window (choice : Bool) :
    Sequential.decodeAt (entry [0x8d,0x46,0xff]) =
      .ok (.lea32 .rax (.baseDisp8 .rsi 0xff) false) ∧
    view .rax choice (entry [0x8d,0x46,0xff]) =
      .ok (0xffffffff,0xfedcba9876543ed7,3,[]) := by
  cases choice <;> exact ⟨rfl, rfl⟩

/-- Explicit destination encodings in both banks. All low32 writes zero
extend, including RSP and callee-saved registers. No ABI claim is made. -/
private def destinations : List (List Byte × Register × Nat) :=
  [([0x8d,0x46,0xff],.rax,3),([0x8d,0x4e,0xff],.rcx,3),
   ([0x8d,0x56,0xff],.rdx,3),([0x8d,0x5e,0xff],.rbx,3),
   ([0x8d,0x66,0xff],.rsp,3),([0x8d,0x6e,0xff],.rbp,3),
   ([0x8d,0x76,0xff],.rsi,3),([0x8d,0x7e,0xff],.rdi,3),
   ([0x44,0x8d,0x46,0xff],.r8,4),([0x44,0x8d,0x4e,0xff],.r9,4),
   ([0x44,0x8d,0x56,0xff],.r10,4),([0x44,0x8d,0x5e,0xff],.r11,4),
   ([0x44,0x8d,0x66,0xff],.r12,4),([0x44,0x8d,0x6e,0xff],.r13,4),
   ([0x44,0x8d,0x76,0xff],.r14,4),([0x44,0x8d,0x7e,0xff],.r15,4)]

theorem every_destination (choice : Bool) :
    destinations.all (fun (bytes,destination,pc) =>
      (view destination choice (entry bytes)).toOption ==
        some (0xffffffff,0xfedcba9876543ed7,BitVec.ofNat 64 pc,[])) = true := by
  cases choice <;> decide +kernel

theorem rex_aliases_and_banks :
    ([([0x40,0x8d,0x46,0xff],.rax,.rsi),([0x41,0x8d,0x46,0xff],.rax,.r14),
      ([0x42,0x8d,0x46,0xff],.rax,.rsi),([0x43,0x8d,0x46,0xff],.rax,.r14),
      ([0x44,0x8d,0x46,0xff],.r8,.rsi),([0x45,0x8d,0x46,0xff],.r8,.r14),
      ([0x46,0x8d,0x46,0xff],.r8,.rsi),([0x47,0x8d,0x46,0xff],.r8,.r14)] :
      List (List Byte × Register × Register)).all (fun (bytes,destination,base) =>
        (Sequential.decodeAt (entry bytes)).toOption ==
          some (.lea32 destination (.baseDisp8 base 0xff) true)) = true := by decide +kernel

theorem explicit_zero_suffix_lengths (choice : Bool) :
    ([([0x8d,0x06],2),([0x8d,0x46,0],3),([0x8d,0x44,0x26,0],4),
      ([0x40,0x8d,0x06],3),([0x40,0x8d,0x46,0],4),
      ([0x40,0x8d,0x44,0x26,0],5)] : List (List Byte × Word)).all (fun (bytes,pc) =>
        (view .rax choice (entry bytes)).toOption == some (0,0xfedcba9876543ed7,pc,[])) = true :=
  by cases choice <;> decide +kernel

/-- Aliases read the original base/index. REX.X turns encoded index4 into
R12; without X it is no index, even with a nonzero scale. -/
theorem sib_and_aliases (choice : Bool) :
    (view .rax choice (entry [0x41,0x8d,0x44,0xa5,0x80]),
      view .rax choice (entry [0x43,0x8d,0x44,0xa5,0x80]),
      view .r12 choice (entry [0x47,0x8d,0x64,0xa5,0x80]),
      view .r13 choice (entry [0x47,0x8d,0x6c,0xa5,0x80]),
      view .rsp choice (entry [0x8d,0x64,0x24,0xff])) =
    (.ok (0xffffff00,0xfedcba9876543ed7,5,[]),
      .ok (0xffffff04,0xfedcba9876543ed7,5,[]),
      .ok (0xffffff04,0xfedcba9876543ed7,5,[]),
      .ok (0xffffff04,0xfedcba9876543ed7,5,[]),
      .ok (0,0xfedcba9876543ed7,4,[])) := by
  cases choice <;> simp only [Prod.mk.injEq] <;>
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
      by decide +kernel, by decide +kernel⟩

theorem signed_displacements_and_width (choice : Bool) :
    (view .rax choice (entry [0x8d,0x45,0x80]),
      view .rax choice (entry [0x8d,0x46,0x7f]),
      view .rax choice (entry [0x8d,0x46,0x80]),
      view .rax choice (entry [0x41,0x8d,0x47,0x7f]),
      view .rax choice (entry [0x40,0x8d,0x47,1])) =
    (.ok (0,0xfedcba9876543ed7,3,[]),
      .ok (127,0xfedcba9876543ed7,3,[]),
      .ok (0xffffff80,0xfedcba9876543ed7,3,[]),
      .ok (111,0xfedcba9876543ed7,4,[]),
      .ok (0,0xfedcba9876543ed7,4,[])) := by
  cases choice <;> simp only [Prod.mk.injEq] <;>
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
      by decide +kernel, by decide +kernel⟩

theorem all_scales_and_mod00 (choice : Bool) :
    ([([0x8d,0x04,0x0e],1),([0x8d,0x04,0x4e],2),
      ([0x8d,0x04,0x8e],4),([0x8d,0x04,0xce],8),
      ([0x8d,0x06],0),([0x42,0x8d,0x06],0),
      ([0x43,0x8d,0x04,0xa6],4)] : List (List Byte × Word)).all (fun (bytes,value) =>
        (view .rax choice (entry bytes)).toOption ==
          some (value,0xfedcba9876543ed7,BitVec.ofNat 64 bytes.length,[])) = true := by
  cases choice <;> decide +kernel

/-- A canonicality check belongs to memory access, and LEA has none. -/
theorem noncanonical_address_is_arithmetic (choice : Bool) :
    canonical (registers .r14) = false ∧
    view .rax choice (entry [0x41,0x8d,0x06]) =
      .ok (0,0xfedcba9876543ed7,3,[]) := by cases choice <;> exact ⟨rfl,rfl⟩

/-- This production-step frame quantifies arbitrary states and every bit of
FLAGS/RAM, rather than sampling unchanged assigned fixture values. -/
theorem arbitrary_production_frame {before : State} {destination : Register} {address : Address}
    {prefixed : Bool} (decoded : Sequential.decodeAt before = .ok (.lea32 destination address prefixed)) :
    ∃ after, (∀ choice, Sequential.step choice before = .ok ⟨.next after, []⟩) ∧
      after.flags = before.flags ∧ after.memory = before.memory ∧
      (∀ register, register ≠ destination → after.registers register = before.registers register) ∧
      (after.registers destination).toNat < 2^32 := by
  obtain ⟨after, executed, context⟩ := execute_lea32_context before destination address prefixed
  exact ⟨after, fun choice => (step_eq_execute choice decoded).trans (executed choice),
    context.flags, context.memory, context.other, context.width⟩

theorem vector_step_preserves_full_flags :
    (stepWith ⟨true,false,true,false,true,false⟩ (entry [0x8d,0x46,0xff])).map
      (fun observation => match observation.result with
        | .next after => (after.registers .rax,after.flags,after.rip,observation.reads)
        | _ => (0,0,0,observation.reads)) =
      .ok (0xffffffff,0xfedcba9876543ed7,3,[]) := by rfl

theorem historical_overlaps :
    (Sequential.decodeAt (entry [0x8d,0x40,0xff]),
      Sequential.decodeAt (entry [0x8d,0x47,0x80]),
      Sequential.decodeAt (entry [0x48,0x8d,0x46,0xff])) =
    (.ok (.legacy (.leaEaxRaxDisp8 0xff)),
      .ok (.legacy (.leaEaxRdiDisp8 0x80)),
      .ok (.lea64 .rax (.baseDisp8 .rsi 0xff))) := by decide +kernel

/-- Reject impossible/unsupported address shapes before fetching an absent
disp32 or any other unused suffix. Existing prefix error identities survive. -/
theorem early_rejections :
    ([[0x8d,0xc6],[0x8d,0x86],[0x8d,0x05],[0x8d,0x04,0x25],
      [0x8d,0x04,0x26],[0x40,0x8d,0xc6],[0x41,0x8d,0x05],
      [0x41,0x8d,0x04,0x25],[0x40,0x8d,0x04,0x26],
      [0x66,0x8d],[0xf0,0x8d],[0xf3,0x8d],[0x40,0x40],
      [0x40,0x41]] : List (List Byte)).all (fun bytes =>
        match Sequential.decodeAt (entry bytes) with
        | .error .unsupportedEncoding => true
        | _ => false) = true ∧
    Sequential.decodeAt (entry [0x67]) = .error (.unsupportedOpcode 0x67) := by
  constructor <;> decide +kernel

theorem missing_needed_bytes :
    ([([0x8d],1),([0x8d,0x46],2),([0x8d,0x44],2),([0x8d,0x44,0x20],3),
      ([0x40],1),([0x40,0x8d],2),([0x41,0x8d,0x45],3),
      ([0x43,0x8d,0x44],3),([0x43,0x8d,0x44,0xa5],4),
      ([0x8d,0x40],2),([0x8d,0x47],2)] : List (List Byte × Word)).all
      (fun (bytes,address) => match Sequential.step false (entry bytes) with
        | .error (.inaccessibleInstruction actual) => actual == address
        | _ => false) = true := by decide +kernel

/-- Each required byte is checked for execute permission and readability.
Complete instructions succeed with the following byte absent. -/
theorem exact_fetch_permissions :
    ([([0x8d,0x46,0xff],0),([0x8d,0x46,0xff],1),([0x8d,0x46,0xff],2),
      ([0x43,0x8d,0x44,0xa5,0x80],0),([0x43,0x8d,0x44,0xa5,0x80],1),
      ([0x43,0x8d,0x44,0xa5,0x80],2),([0x43,0x8d,0x44,0xa5,0x80],3),
      ([0x43,0x8d,0x44,0xa5,0x80],4)] : List (List Byte × Word)).all (fun (bytes,denied) =>
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
  rip := 0x7ffffffffffe
  flags := 0xfedcba9876543ed7
  memory := {
    read := fun address => ([0x8d,0x46,0xff] : List Byte)[(address - 0x7ffffffffffe).toNat]?
    executable := fun _ => true }

theorem canonical_fetch_boundary :
    Sequential.step false crossingHole = .error (.inaccessibleInstruction 0x800000000000) := by rfl

theorem sibling_and_literal :
    CallReturn.decodeAt (entry [0x8d,0x46,0xff]) =
      .ok (.sequential (.lea32 .rax (.baseDisp8 .rsi 0xff) false)) ∧
    Literals.instruction (.lea32 .r12 (.sibDisp8 .r13 (some .r12) 2 0x80) true) =
      "(.lea32 .r12 (.sibDisp8 .r13 (some .r12) 2 128) true)" := by
  constructor <;> decide +kernel

end EDSL.Tests.Address32
