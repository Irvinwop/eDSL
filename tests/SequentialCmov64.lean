/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.CFGDiscovery
import EDSL.X86.Sequential.ConditionFlags
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.SequentialCmov64
open X86

private def entry (code : List Byte) (registers : Register → Word := fun _ => 0)
    (flags : Word := 0x202)
    (ram : Memory := { read := fun _ => none, executable := fun _ => false }) : State where
  registers := registers
  flags := flags
  rip := 4096
  memory := {
    read := fun address => if 4096 ≤ address.toNat ∧ address.toNat < 4096 + code.length
      then code[address.toNat - 4096]? else ram.read address
    executable := fun address =>
      if 4096 ≤ address.toNat ∧ address.toNat < 4096 + code.length then true
      else ram.executable address
    writable := ram.writable }

private def nextView (af : Bool) (state : State)
    (view : State → List Sequential.Read → α) : Except Error α := do
  let observation ← Sequential.step af state
  match observation.result with
  | .next final => return view final observation.reads
  | _ => throw .unexpectedReturn

private def registers : Register → Word
  | .rax => 0xdeadbeef12345678 | .rcx => 0x1111222233334444
  | .rsp => 0xfffffffffffffff0 | .rdi => 0x8765432100000001
  | .r8 => 0xabcdef0087654321 | .r9 => 0x8877665544332211
  | .r12 => 0x1234567887654321 | _ => 0xfeedface12345678

/-- Conditions must preserve the old complete destination on false, transfer
all source bits on true, and leave flags untouched. No operand RAM is mapped. -/
theorem full_width_and_false_retention (af : Bool) :
    ([0x202,0x242] : List Word).map (fun flags =>
      nextView af (entry [0x48,0x0f,0x44,0xc7] registers flags)
        (fun final reads => (final.registers .rax,final.registers .rdi,final.flags,final.rip,reads))) =
    [.ok (0xdeadbeef12345678,0x8765432100000001,0x202,4100,[]),
      .ok (0x8765432100000001,0x8765432100000001,0x242,4100,[])] := by rfl

/-- Literal assembler operand vectors distinguish R/B roles and ignored X.
The last two encode a self-alias and an arbitrary full64 RSP destination. -/
theorem extended_banks_alias_and_rsp (af : Bool) :
    ([([0x48,0x0f,0x44,0xc1],.rax), ([0x49,0x0f,0x44,0xc1],.rax),
      ([0x4a,0x0f,0x44,0xc1],.rax), ([0x4b,0x0f,0x44,0xc1],.rax),
      ([0x4c,0x0f,0x44,0xc1],.r8), ([0x4d,0x0f,0x44,0xc1],.r8),
      ([0x4e,0x0f,0x44,0xc1],.r8), ([0x4f,0x0f,0x44,0xc1],.r8),
      ([0x4f,0x0f,0x44,0xe4],.r12), ([0x48,0x0f,0x44,0xe7],.rsp)] :
      List (List Byte × Register)).map (fun (bytes,destination) =>
        nextView af (entry bytes registers 0x242)
          (fun final reads => (final.registers destination,final.flags,reads))) =
    [.ok (0x1111222233334444,0x242,[]),.ok (0x8877665544332211,0x242,[]),
      .ok (0x1111222233334444,0x242,[]),.ok (0x8877665544332211,0x242,[]),
      .ok (0x1111222233334444,0x242,[]),.ok (0x8877665544332211,0x242,[]),
      .ok (0x1111222233334444,0x242,[]),.ok (0x8877665544332211,0x242,[]),
      .ok (0x1234567887654321,0x242,[]),.ok (0x8765432100000001,0x242,[])] := by rfl

/-- A signed overflow vector distinguishes SF alone from signed order:
CMP INT64_MIN,1 has a positive modular difference but signed-less is true. -/
theorem signed_overflow_and_unsigned_borrow :
    (Sequential.Condition.holds .less (Sequential.cmpFlags64 0x202 0x8000000000000000 1),
      Sequential.Condition.holds .below (Sequential.cmpFlags64 0x202 0x8000000000000000 1),
      Sequential.Condition.holds .greater (Sequential.cmpFlags64 0x202 0x7fffffffffffffff 0xffffffffffffffff),
      Sequential.Condition.holds .below (Sequential.cmpFlags64 0x202 0x7fffffffffffffff 0xffffffffffffffff)) =
    (true,false,true,true) := by rfl

set_option maxRecDepth 4096 in
/-- The real byte decoder and executor preserve arbitrary complete RAM and
flags. The fourth byte is the final required fetch; no following byte exists. -/
theorem full_context (gprs : Register → Word) (flags : Word) (ram : Memory) (af : Bool) :
    nextView af (entry [0x4f,0x0f,0x44,0xe4] gprs flags ram)
      (fun final reads => (final.registers,final.memory,final.flags,final.rip,reads)) =
    .ok (gprs,(entry [0x4f,0x0f,0x44,0xe4] gprs flags ram).memory,flags,4100,[]) := by
  simp only [nextView, Sequential.step, Sequential.decodeAt, X86.decodeAt,
    Sequential.decodeNewAt, Sequential.decodeREXWAt, entry, fetchByte, canonical,
    Sequential.rexWPrefix, Sequential.rexModRMReg, Sequential.rexModRMRM,
    Sequential.highRegister, Sequential.Condition.ofNibble]
  change _ = _
  simp [Sequential.execute, Sequential.Instruction.operandReads, State.writeRegister]
  funext register
  by_cases same : register = .r12 <;> simp [same]

/-- Memory CMOV is deliberately unsupported even for a false condition;
the architecture reads its memory source unconditionally. No fault suppression
or narrower variant is inferred from these encodings. -/
theorem unsupported_memory_and_inner_prefixes :
    ([[0x48,0x0f,0x44,0x07], [0x4f,0x0f,0x44,0x44], [0x48,0x0f,0x44,0x87],
      [0x48,0x48,0x0f,0x44,0xc7], [0x48,0x66,0x0f,0x44,0xc7],
      [0x48,0x0f,0x3f,0xc7], [0x48,0x0f,0x50,0xc7]] : List (List Byte)).map
      (fun bytes => Sequential.decodeAt (entry bytes registers 0x202)) =
    List.replicate 7 (.error .unsupportedEncoding) := by rfl

theorem width_selection_and_leading_prefixes :
    ([[0x0f,0x44,0xc7], [0x40,0x0f,0x44,0xc7], [0x47,0x0f,0x44,0xc7],
      [0x66,0x48,0x0f,0x44,0xc7], [0x67,0x48,0x0f,0x44,0xc7]] : List (List Byte)).map
      (fun bytes => Sequential.decodeAt (entry bytes)) =
    [.ok (.cmovReg32 .equal .rax .rdi false),.ok (.cmovReg32 .equal .rax .rdi true),
      .ok (.cmovReg32 .equal .r8 .r15 true),.error .unsupportedEncoding,
      .error (.unsupportedOpcode 0x67)] := by rfl

theorem fourth_byte_fetch_required (af : Bool) :
    ((Sequential.step af (entry [0x48,0x0f,0x44])).map (fun _ => ()),
      (Sequential.step af { entry [0x48,0x0f,0x44,0xc7] with
        memory := { (entry [0x48,0x0f,0x44,0xc7]).memory with
          executable := fun address => decide (address ≠ 4099) } }).map (fun _ => ())) =
    (.error (.inaccessibleInstruction 4099),.error (.inaccessibleInstruction 4099)) := by rfl

theorem cfg_admission :
    (Sequential.CFG.analyze [0x48,0x39,0xf7,0x48,0x89,0xf0,0x48,0x0f,0x43,0xc7,0xc3]).map
      (fun graph => graph.nodes.map (fun node =>
        (node.offset,node.instruction,node.instruction.length))) =
    .ok [(0,.cmp64 .rdi .rsi,3),(3,.movReg64 .rax .rsi,3),
      (6,.cmovReg64 .aboveEqual .rax .rdi,4),(10,.legacy .ret,1)] := by rfl

end EDSL.Tests.SequentialCmov64

#audit_edsl
