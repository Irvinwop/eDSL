/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.CFGDiscovery
import EDSL.X86.Sequential.Return
import EDSL.X86.Sequential.Literals
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.SequentialAddMemory64
open X86

-- Independent literal byte arrays supply ordinary read-only DATA memory.
-- Instruction fetches and eight-byte data accesses have separate mappings.
def entry (code : List Byte) (registers : Register → Word := fun _ => 0)
    (dataBase : Nat := 0) (data : List Byte := []) (flags : Word := 0x200ed7) : State where
  registers := registers
  rip := 4096
  flags := flags
  memory := {
    read := fun address =>
      if 4096 ≤ address.toNat ∧ address.toNat < 4096 + code.length then
        code[address.toNat - 4096]?
      else if dataBase ≤ address.toNat ∧ address.toNat < dataBase + data.length then
        data[address.toNat - dataBase]?
      else none
    executable := fun address => decide (4096 ≤ address.toNat ∧ address.toNat < 4096 + code.length)
    writable := fun _ => false }

def nextView (af : Bool) (state : State)
    (view : State → List Sequential.Read → α) : Except Error α := do
  let observation ← Sequential.step af state
  match observation.result with
  | .next after => return view after observation.reads
  | _ => throw .unexpectedReturn

theorem all_destination_banks :
    ([[0x48,0x03,0x07], [0x48,0x03,0x0f], [0x48,0x03,0x17], [0x48,0x03,0x1f],
      [0x48,0x03,0x27], [0x48,0x03,0x2f], [0x48,0x03,0x37], [0x48,0x03,0x3f],
      [0x4c,0x03,0x07], [0x4c,0x03,0x0f], [0x4c,0x03,0x17], [0x4c,0x03,0x1f],
      [0x4c,0x03,0x27], [0x4c,0x03,0x2f], [0x4c,0x03,0x37], [0x4c,0x03,0x3f]] :
      List (List Byte)).map (fun code => Sequential.decodeAt (entry code)) =
    [.ok (.addMem64 .rax (.base .rdi)), .ok (.addMem64 .rcx (.base .rdi)),
      .ok (.addMem64 .rdx (.base .rdi)), .ok (.addMem64 .rbx (.base .rdi)),
      .ok (.addMem64 .rsp (.base .rdi)), .ok (.addMem64 .rbp (.base .rdi)),
      .ok (.addMem64 .rsi (.base .rdi)), .ok (.addMem64 .rdi (.base .rdi)),
      .ok (.addMem64 .r8 (.base .rdi)), .ok (.addMem64 .r9 (.base .rdi)),
      .ok (.addMem64 .r10 (.base .rdi)), .ok (.addMem64 .r11 (.base .rdi)),
      .ok (.addMem64 .r12 (.base .rdi)), .ok (.addMem64 .r13 (.base .rdi)),
      .ok (.addMem64 .r14 (.base .rdi)), .ok (.addMem64 .r15 (.base .rdi))] := by rfl

-- Every extension bit has a distinct role; X is ignored without SIB.
theorem rex_roles :
    ([[0x48,0x03,0x0f], [0x49,0x03,0x0f], [0x4a,0x03,0x0f], [0x4b,0x03,0x0f],
      [0x4c,0x03,0x0f], [0x4d,0x03,0x0f], [0x4e,0x03,0x0f], [0x4f,0x03,0x0f],
      [0x48,0x03,0x14,0x8f], [0x49,0x03,0x14,0x8f], [0x4a,0x03,0x14,0x8f],
      [0x4b,0x03,0x14,0x8f], [0x4c,0x03,0x14,0x8f], [0x4d,0x03,0x14,0x8f],
      [0x4e,0x03,0x14,0x8f], [0x4f,0x03,0x14,0x8f]] : List (List Byte)).map
      (fun code => Sequential.decodeAt (entry code)) =
    [.ok (.addMem64 .rcx (.base .rdi)), .ok (.addMem64 .rcx (.base .r15)),
      .ok (.addMem64 .rcx (.base .rdi)), .ok (.addMem64 .rcx (.base .r15)),
      .ok (.addMem64 .r9 (.base .rdi)), .ok (.addMem64 .r9 (.base .r15)),
      .ok (.addMem64 .r9 (.base .rdi)), .ok (.addMem64 .r9 (.base .r15)),
      .ok (.addMem64 .rdx (.indexed .rdi .rcx 2)), .ok (.addMem64 .rdx (.indexed .r15 .rcx 2)),
      .ok (.addMem64 .rdx (.indexed .rdi .r9 2)), .ok (.addMem64 .rdx (.indexed .r15 .r9 2)),
      .ok (.addMem64 .r10 (.indexed .rdi .rcx 2)), .ok (.addMem64 .r10 (.indexed .r15 .rcx 2)),
      .ok (.addMem64 .r10 (.indexed .rdi .r9 2)), .ok (.addMem64 .r10 (.indexed .r15 .r9 2))] := by rfl

def sumRegisters (left : Word) : Register → Word
  | .rax => left | .rdi => 0x100000001 | .rdx => 1
  | _ => 0xfedcba9876543210

-- Literal arithmetic answers distinguish full64 carry, signed overflow,
-- nibble carry, parity and zero, including preservation of ID/DF/IF.
theorem exact_arithmetic_flags (af : Bool) :
    ([((0xffffffffffffffff : Word), [1,0,0,0,0,0,0,0]),
      (0x7fffffffffffffff, [1,0,0,0,0,0,0,0]),
      (0x8000000000000000, [0,0,0,0,0,0,0,0x80]),
      (0x1ffffffff, [2,0,0,0,0,0,0,0])] : List (Word × List Byte)).map
      (fun (left,bytes) => nextView af
        (entry [0x48,0x03,0x07] (sumRegisters left) 0x100000001 bytes)
        (fun after reads => (after.registers .rax,after.flags,after.rip,reads))) =
    [.ok (0,0x200657,4099,[⟨.data,0x100000001,8⟩]),
      .ok (0x8000000000000000,0x200e96,4099,[⟨.data,0x100000001,8⟩]),
      .ok (0,0x200e47,4099,[⟨.data,0x100000001,8⟩]),
      .ok (0x200000001,0x200612,4099,[⟨.data,0x100000001,8⟩])] := by rfl

-- Overwriting the base must use its original pointer and original full value.
theorem destination_base_alias (af : Bool) :
    nextView af (entry [0x48,0x03,0x3f] (sumRegisters 0) 0x100000001
      [3,0,0,0,2,0,0,0])
      (fun after reads => (after.registers .rdi,after.registers .rdx,after.flags,reads)) =
    .ok (0x300000004,1,0x200602,[⟨.data,0x100000001,8⟩]) := by rfl

-- Overwriting the index must not change this instruction's address or read.
theorem destination_index_alias (af : Bool) :
    nextView af (entry [0x48,0x03,0x14,0xd7] (sumRegisters 0) 0x100000001
      [0,0,0,0,0,0,0,0,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff])
      (fun after reads => (after.registers .rdx,after.registers .rdi,after.flags,reads)) =
    .ok (0,0x100000001,0x200657,[⟨.data,0x100000009,8⟩]) := by rfl

-- Missing only byte seven must fault; a narrowed four-byte load would succeed.
theorem eighth_byte_required (af : Bool) :
    (Sequential.step af (entry [0x48,0x03,0x07] (sumRegisters 0) 0x100000001
      [1,0,0,0,0,0,0])).map (fun _ => ()) =
      .error (.inaccessibleData 0x100000008) := by rfl

theorem full_index_required (af : Bool) :
    (Sequential.step af (entry [0x48,0x03,0x04,0xd7]
      (fun register => if register = .rdx then 0x100000001 else sumRegisters 0 register)
      0x100000001 [0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0])).map (fun _ => ()) =
      .error (.inaccessibleData 0x900000009) := by rfl

-- All bytes are present here; the complete source still crosses the canonical
-- hole. A start-only canonicality check or dword read would wrongly succeed.
theorem canonical_source_span (af : Bool) :
    (Sequential.step af (entry [0x48,0x03,0x07]
      (fun register => if register = .rdi then 0x7ffffffffffb else sumRegisters 0 register)
      0x7ffffffffffb [1,0,0,0,0,0,0,0])).map (fun _ => ()) =
      .error (.inaccessibleData 0x800000000000) := by rfl

theorem nonwrapping_qword (af : Bool) :
    (Sequential.step af (entry [0x48,0x03,0x07]
      (fun register => if register = .rdi then 0xfffffffffffffffa else sumRegisters 0 register)
      0xfffffffffffffffa [1,0,0,0,0,0,0,0])).map (fun _ => ()) =
      .error (.inaccessibleData 0xfffffffffffffffa) := by rfl

-- SIB scales and R12's extended index remain real decoded operands.
theorem sib_scales_and_extended_index :
    ([[0x48,0x03,0x04,0x0f], [0x48,0x03,0x04,0x4f],
      [0x48,0x03,0x04,0x8f], [0x48,0x03,0x04,0xcf],
      [0x4a,0x03,0x04,0x27], [0x4f,0x03,0x24,0xe4]] : List (List Byte)).map
      (fun code => Sequential.decodeAt (entry code)) =
    [.ok (.addMem64 .rax (.indexed .rdi .rcx 0)), .ok (.addMem64 .rax (.indexed .rdi .rcx 1)),
      .ok (.addMem64 .rax (.indexed .rdi .rcx 2)), .ok (.addMem64 .rax (.indexed .rdi .rcx 3)),
      .ok (.addMem64 .rax (.indexed .rdi .r12 0)), .ok (.addMem64 .r12 (.indexed .r12 .r12 3))] := by rfl

theorem unsupported_forms :
    ([[0x48,0x01,0x07], [0x48,0x03,0x47,0], [0x48,0x03,0x87,0,0,0,0],
      [0x48,0x03,0x05,0,0,0,0], [0x49,0x03,0x05,0,0,0,0],
      [0x48,0x03,0x04,0x27], [0x4b,0x03,0x04,0x0d],
      [0x48,0x48,0x03,0x07], [0x48,0x66,0x03,0x07], [0x48,0xf0,0x03,0x07]] :
      List (List Byte)).map (fun code => Sequential.decodeAt (entry code)) =
    List.replicate 10 (.error .unsupportedEncoding) := by rfl

theorem truncated_and_nonexecutable_fetch (af : Bool) :
    (([[0x48,0x03], [0x48,0x03,0x04]] : List (List Byte)).map
      (fun code => (Sequential.step af (entry code)).map (fun _ => ())),
      (Sequential.step af { entry [0x48,0x03,0x04,0xcf] with memory :=
        { (entry [0x48,0x03,0x04,0xcf]).memory with
          executable := fun address => decide (address ≠ 4099) } }).map (fun _ => ())) =
    ([.error (.inaccessibleInstruction 4098), .error (.inaccessibleInstruction 4099)],
      .error (.inaccessibleInstruction 4099)) := by rfl

-- This extension must retain both opcode directions of register ADD64 and the
-- existing unprefixed dword form. It does not enroll the legacy/TSO decoders.
theorem existing_widths_and_profiles :
    (Sequential.decodeAt (entry [0x03,0x07]),
      Sequential.decodeAt (entry [0x48,0x03,0xc7]),
      Sequential.decodeAt (entry [0x48,0x01,0xf8]),
      X86.decodeAt (entry [0x48,0x03,0x07])) =
    (.ok (.addMem32 .rax (.base .rdi)), .ok (.addReg64 .rax .rdi),
      .ok (.addReg64 .rax .rdi), .error (.unsupportedOpcode 0x48)) := by rfl

end EDSL.Tests.SequentialAddMemory64

#print axioms EDSL.X86.Sequential.execute_addMem64_context
#print axioms EDSL.X86.Sequential.execute_reads_succeed
#audit_edsl
