/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.CFGDiscovery
import EDSL.OS.TSO.Model
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.SequentialXchg64
open X86

def allRegisters : List Register :=
  [.rax,.rcx,.rdx,.rbx,.rsp,.rbp,.rsi,.rdi,.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15]

/-- Distinct nonzero high halves catch truncation and lost second operands. -/
def registerInput : Register → Word
  | .rax => 0x1111111180000001 | .rcx => 0x2222222280000002
  | .rdx => 0x3333333380000003 | .rbx => 0x4444444480000004
  | .rsp => 0x5555555580000005 | .rbp => 0x6666666680000006
  | .rsi => 0x7777777780000007 | .rdi => 0x8888888880000008
  | .r8 => 0x9999999980000009 | .r9 => 0xaaaaaaaa8000000a
  | .r10 => 0xbbbbbbbb8000000b | .r11 => 0xcccccccc8000000c
  | .r12 => 0xdddddddd8000000d | .r13 => 0xeeeeeeee8000000e
  | .r14 => 0xfedcba988000000f | .r15 => 0xf123456780000010

def emptyMemory : Memory where
  read := fun _ => none
  executable := fun _ => false

/-- Operands may include an arbitrary, unreadable RSP. Only code is fetched. -/
def entry (code : List Byte) (registers : Register → Word := registerInput)
    (flags : Word := 0xfedcba9876543210) (data : Memory := emptyMemory) : State where
  registers := registers
  flags := flags
  rip := 4096
  memory := {
    read := fun address => if 4096 ≤ address.toNat ∧ address.toNat < 4096 + code.length
      then code[address.toNat - 4096]? else data.read address
    executable := fun address =>
      if 4096 ≤ address.toNat ∧ address.toNat < 4096 + code.length then true
      else data.executable address
    writable := data.writable }

def nextView (af : Bool) (state : State)
    (view : State → List Sequential.Read → α) : Except Error α := do
  let observation ← Sequential.step af state
  match observation.result with
  | .next final => return view final observation.reads
  | _ => throw .unexpectedReturn

/-- Literal opcode vectors specify all short-form operands. Repeating them
under each unused R/X combination checks those bits independently of B. -/
theorem short_operands :
    ([0x48,0x4a,0x4c,0x4e,0x49,0x4b,0x4d,0x4f] : List Byte).map
      (fun rex => ([0x90,0x91,0x92,0x93,0x94,0x95,0x96,0x97] : List Byte).map
        (fun opcode => Sequential.decodeAt (entry [rex,opcode]))) =
    List.replicate 4 [.ok (.xchgRax64 .rax), .ok (.xchgRax64 .rcx),
      .ok (.xchgRax64 .rdx), .ok (.xchgRax64 .rbx), .ok (.xchgRax64 .rsp),
      .ok (.xchgRax64 .rbp), .ok (.xchgRax64 .rsi), .ok (.xchgRax64 .rdi)] ++
    List.replicate 4 [.ok (.xchgRax64 .r8), .ok (.xchgRax64 .r9),
      .ok (.xchgRax64 .r10), .ok (.xchgRax64 .r11), .ok (.xchgRax64 .r12),
      .ok (.xchgRax64 .r13), .ok (.xchgRax64 .r14), .ok (.xchgRax64 .r15)] := by rfl

/-- R and B select separate ModRM operands. X has no register-mode effect. -/
theorem modrm_bank_bits :
    ([[0x48,0x87,0xd8], [0x49,0x87,0xd8], [0x4a,0x87,0xd8], [0x4b,0x87,0xd8],
      [0x4c,0x87,0xd8], [0x4d,0x87,0xd8], [0x4e,0x87,0xd8], [0x4f,0x87,0xd8]] :
      List (List Byte)).map (fun bytes => Sequential.decodeAt (entry bytes)) =
    [.ok (.xchgReg64 .rax .rbx), .ok (.xchgReg64 .r8 .rbx),
      .ok (.xchgReg64 .rax .rbx), .ok (.xchgReg64 .r8 .rbx),
      .ok (.xchgReg64 .rax .r11), .ok (.xchgReg64 .r8 .r11),
      .ok (.xchgReg64 .rax .r11), .ok (.xchgReg64 .r8 .r11)] := by rfl

/-- Short-form execution exchanges both full64 values, including extended
opcode registers. The RAX/RAX special case retains its original high half. -/
theorem all_short_executions (af : Bool) :
    ([([0x48,0x90], .rax), ([0x48,0x91], .rcx), ([0x48,0x92], .rdx),
      ([0x48,0x93], .rbx), ([0x48,0x94], .rsp), ([0x48,0x95], .rbp),
      ([0x48,0x96], .rsi), ([0x48,0x97], .rdi), ([0x49,0x90], .r8),
      ([0x49,0x91], .r9), ([0x49,0x92], .r10), ([0x49,0x93], .r11),
      ([0x49,0x94], .r12), ([0x49,0x95], .r13), ([0x49,0x96], .r14),
      ([0x49,0x97], .r15)] : List (List Byte × Register)).map (fun (bytes, other) =>
        nextView af (entry bytes) (fun s _ => (s.registers .rax,s.registers other))) =
    [.ok (0x1111111180000001,0x1111111180000001),
      .ok (0x2222222280000002,0x1111111180000001),
      .ok (0x3333333380000003,0x1111111180000001),
      .ok (0x4444444480000004,0x1111111180000001),
      .ok (0x5555555580000005,0x1111111180000001),
      .ok (0x6666666680000006,0x1111111180000001),
      .ok (0x7777777780000007,0x1111111180000001),
      .ok (0x8888888880000008,0x1111111180000001),
      .ok (0x9999999980000009,0x1111111180000001),
      .ok (0xaaaaaaaa8000000a,0x1111111180000001),
      .ok (0xbbbbbbbb8000000b,0x1111111180000001),
      .ok (0xcccccccc8000000c,0x1111111180000001),
      .ok (0xdddddddd8000000d,0x1111111180000001),
      .ok (0xeeeeeeee8000000e,0x1111111180000001),
      .ok (0xfedcba988000000f,0x1111111180000001),
      .ok (0xf123456780000010,0x1111111180000001)] := by rfl

/-- All16 registers occur in each operand position; observed values are
independent literal input values, rather than a second swap implementation. -/
theorem all_modrm_operands (af : Bool) :
    ([([0x48,0x87,0xc8], .rax, .rcx), ([0x4c,0x87,0xd1], .rcx, .r10),
      ([0x48,0x87,0xda], .rdx, .rbx), ([0x4c,0x87,0xe3], .rbx, .r12),
      ([0x48,0x87,0xec], .rsp, .rbp), ([0x4c,0x87,0xf5], .rbp, .r14),
      ([0x48,0x87,0xfe], .rsi, .rdi), ([0x4c,0x87,0xc7], .rdi, .r8),
      ([0x4d,0x87,0xc8], .r8, .r9), ([0x49,0x87,0xd1], .r9, .rdx),
      ([0x4d,0x87,0xda], .r10, .r11), ([0x49,0x87,0xe3], .r11, .rsp),
      ([0x4d,0x87,0xec], .r12, .r13), ([0x49,0x87,0xf5], .r13, .rsi),
      ([0x4d,0x87,0xfe], .r14, .r15), ([0x49,0x87,0xc7], .r15, .rax)] :
      List (List Byte × Register × Register)).map (fun (bytes, left, right) =>
        nextView af (entry bytes) (fun s _ => (s.registers left, s.registers right))) =
    [.ok (0x2222222280000002,0x1111111180000001),
      .ok (0xbbbbbbbb8000000b,0x2222222280000002),
      .ok (0x4444444480000004,0x3333333380000003),
      .ok (0xdddddddd8000000d,0x4444444480000004),
      .ok (0x6666666680000006,0x5555555580000005),
      .ok (0xfedcba988000000f,0x6666666680000006),
      .ok (0x8888888880000008,0x7777777780000007),
      .ok (0x9999999980000009,0x8888888880000008),
      .ok (0xaaaaaaaa8000000a,0x9999999980000009),
      .ok (0x3333333380000003,0xaaaaaaaa8000000a),
      .ok (0xcccccccc8000000c,0xbbbbbbbb8000000b),
      .ok (0x5555555580000005,0xcccccccc8000000c),
      .ok (0xeeeeeeee8000000e,0xdddddddd8000000d),
      .ok (0x7777777780000007,0xeeeeeeee8000000e),
      .ok (0xf123456780000010,0xfedcba988000000f),
      .ok (0x1111111180000001,0xf123456780000010)] := by rfl

set_option maxRecDepth 4096 in
/-- Swapping RSP preserves the entire unrelated register context, all flags,
and all three memory functions, without reading the old or new stack. -/
theorem modrm_complete_context (registers : Register → Word) (flags : Word) (data : Memory)
    (af : Bool) : nextView af (entry [0x4e,0x87,0xe4] registers flags data)
      (fun s reads => (allRegisters.map s.registers, s.memory, s.flags, s.rip, reads)) =
    .ok ([registers .rax,registers .rcx,registers .rdx,registers .rbx,
      registers .r12,registers .rbp,registers .rsi,registers .rdi,
      registers .r8,registers .r9,registers .r10,registers .r11,
      registers .rsp,registers .r13,registers .r14,registers .r15],
      (entry [0x4e,0x87,0xe4] registers flags data).memory,flags,4099,[]) := by
  have decoded : Sequential.decodeAt (entry [0x4e,0x87,0xe4] registers flags data) =
      .ok (.xchgReg64 .rsp .r12) := by
    simp [Sequential.decodeAt, X86.decodeAt, Sequential.decodeNewAt, Sequential.decodeREXWAt, entry,
      fetchByte, canonical, Sequential.rexWPrefix, Sequential.rexModRMReg,
      Sequential.rexModRMRM, Sequential.highRegister, Sequential.modRMRM, Sequential.lowRegister]
  unfold nextView
  rw [Sequential.step_eq_execute af decoded]
  rfl

set_option maxRecDepth 4096 in
theorem short_complete_context (registers : Register → Word) (flags : Word) (data : Memory)
    (af : Bool) : nextView af (entry [0x4e,0x94] registers flags data)
      (fun s reads => (allRegisters.map s.registers, s.memory, s.flags, s.rip, reads)) =
    .ok ([registers .rsp,registers .rcx,registers .rdx,registers .rbx,
      registers .rax,registers .rbp,registers .rsi,registers .rdi,
      registers .r8,registers .r9,registers .r10,registers .r11,
      registers .r12,registers .r13,registers .r14,registers .r15],
      (entry [0x4e,0x94] registers flags data).memory,flags,4098,[]) := by
  have decoded : Sequential.decodeAt (entry [0x4e,0x94] registers flags data) =
      .ok (.xchgRax64 .rsp) := by
    simp [Sequential.decodeAt, X86.decodeAt, Sequential.decodeNewAt, Sequential.decodeREXWAt, entry,
      fetchByte, canonical, Sequential.rexWPrefix, Sequential.rexModRMRM,
      Sequential.modRMRM, Sequential.lowRegister]
  unfold nextView
  rw [Sequential.step_eq_execute af decoded]
  rfl

/-- ModRM aliases for every GPR and the short-form RAX alias are identities
on full64 values; nonzero upper halves catch accidental XCHG32 semantics. -/
theorem all_self_exchanges (af : Bool) :
    ([[0x48,0x87,0xc0], [0x48,0x87,0xc9], [0x48,0x87,0xd2], [0x48,0x87,0xdb],
      [0x48,0x87,0xe4], [0x48,0x87,0xed], [0x48,0x87,0xf6], [0x48,0x87,0xff],
      [0x4d,0x87,0xc0], [0x4d,0x87,0xc9], [0x4d,0x87,0xd2], [0x4d,0x87,0xdb],
      [0x4d,0x87,0xe4], [0x4d,0x87,0xed], [0x4d,0x87,0xf6], [0x4d,0x87,0xff]] :
      List (List Byte)).map (fun bytes => nextView af (entry bytes)
        (fun s reads => (allRegisters.map s.registers,s.flags,s.rip,reads))) =
    List.replicate 16 (.ok (allRegisters.map registerInput,0xfedcba9876543210,4099,[])) := by rfl

theorem short_self_exchange (af : Bool) :
    ([0x48,0x4a,0x4c,0x4e] : List Byte).map (fun rex =>
      nextView af (entry [rex,0x90])
        (fun s reads => (allRegisters.map s.registers,s.flags,s.rip,reads))) =
    List.replicate 4 (.ok (allRegisters.map registerInput,0xfedcba9876543210,4098,[])) := by rfl

theorem prefixes_and_memory_rejected :
    ([[0x48,0x48,0x97], [0x4f,0x4f,0x87,0xd8], [0x48,0xf0,0x87,0xd8],
      [0xf0,0x48,0x87,0xd8], [0x48,0x66,0x97], [0x48,0x87,0x07],
      [0x49,0x87,0x1b], [0x4f,0x87,0x1c,0x24], [0x48,0x87,0x5b,0],
      [0x48,0x87,0x9b,0,0,0,0], [0x48,0x87,0x1d,0,0,0,0]] : List (List Byte)).map
      (fun bytes => Sequential.decodeAt (entry bytes)) =
    List.replicate 11 (.error .unsupportedEncoding) := by rfl

theorem other_widths_rejected :
    ([[0x40,0x97], [0x41,0x97], [0x42,0x87,0xd8], [0x43,0x87,0xd8],
      [0x44,0x97], [0x45,0x97], [0x46,0x87,0xd8], [0x47,0x87,0xd8],
      [0x66,0x48,0x97], [0x67,0x48,0x97], [0xf2,0x48,0x97], [0xf3,0x48,0x97],
      [0x97], [0x87,0xd8], [0x86,0xd8]] : List (List Byte)).map
      (fun bytes => Sequential.decodeAt (entry bytes)) =
    [.error .unsupportedEncoding, .error .unsupportedEncoding,
      .error .unsupportedEncoding, .error .unsupportedEncoding,
      .error .unsupportedEncoding, .error .unsupportedEncoding,
      .error .unsupportedEncoding, .error .unsupportedEncoding,
      .error .unsupportedEncoding, .error (.unsupportedOpcode 0x67),
      .error (.unsupportedOpcode 0xf2), .error .unsupportedEncoding,
      .error (.unsupportedOpcode 0x97), .error .unsupportedEncoding,
      .error (.unsupportedOpcode 0x86)] := by rfl

theorem truncated_fetch (af : Bool) :
    ([[0x48], [0x4f], [0x48,0x87], [0x4f,0x87]] : List (List Byte)).map
      (fun bytes => (Sequential.step af (entry bytes)).map (fun _ => ())) =
    [.error (.inaccessibleInstruction 4097), .error (.inaccessibleInstruction 4097),
      .error (.inaccessibleInstruction 4098), .error (.inaccessibleInstruction 4098)] := by rfl

theorem modrm_execute_permission (af : Bool) :
    (Sequential.step af { entry [0x4f,0x87,0xd8] with
      memory := { (entry [0x4f,0x87,0xd8]).memory with
        executable := fun address => decide (address = 4096 ∨ address = 4097) } }).map
      (fun _ => ()) = .error (.inaccessibleInstruction 4098) := by rfl

theorem short_read_permission (af : Bool) :
    (Sequential.step af { entry [0x49,0x97] with
      memory := { (entry [0x49,0x97]).memory with
        read := fun address => if address = 4097 then none
          else (entry [0x49,0x97]).memory.read address } }).map
      (fun _ => ()) = .error (.inaccessibleInstruction 4097) := by rfl

theorem cfg_admission :
    (Sequential.CFG.analyze [0x48,0x97,0x4f,0x87,0xd8,0xc3]).map
      (fun graph => graph.nodes.map (fun node =>
        (node.offset,node.instruction,node.instruction.length))) =
    .ok [(0,.xchgRax64 .rdi,2),(2,.xchgReg64 .r8 .r11,3),(5,.legacy .ret,1)] := by rfl

def tsoEntry (bytes : List Byte) : OS.TSO.State :=
  ⟨(entry bytes).memory, [⟨OS.Threads.Context.ofState (entry bytes), false, []⟩]⟩

/-- Register exchange is ordinary sequential computation, and remains absent
from the legacy TSO issuer; memory-XCHG32 keeps its existing locked contract. -/
theorem tso_rejection_and_legacy_atomic :
    (([[0x48,0x97], [0x49,0x97], [0x4a,0x87,0xd8], [0x4b,0x87,0xd8],
      [0x4c,0x97], [0x4d,0x97], [0x4e,0x87,0xd8], [0x4f,0x87,0xd8]] :
      List (List Byte)).map (fun bytes =>
        (OS.TSO.step (tsoEntry bytes) (.issue 0)).map (fun _ => ())),
      Sequential.decodeAt (entry [0x87,0x07]),
      (Sequential.Instruction.legacy .exchangeEaxRdi).isLocked,
      (Sequential.Instruction.xchgReg64 .rax .rdi).isLocked,
      (Sequential.Instruction.xchgRax64 .rdi).isLocked) =
    ([.error (.machine (.unsupportedOpcode 0x48)), .error (.machine (.unsupportedOpcode 0x49)),
      .error (.machine (.unsupportedOpcode 0x4a)), .error (.machine (.unsupportedOpcode 0x4b)),
      .error (.machine (.unsupportedOpcode 0x4c)), .error (.machine (.unsupportedOpcode 0x4d)),
      .error (.machine (.unsupportedOpcode 0x4e)), .error (.machine (.unsupportedOpcode 0x4f))],
      .ok (.legacy .exchangeEaxRdi),true,false,false) := by rfl

end EDSL.Tests.SequentialXchg64

#audit_edsl
