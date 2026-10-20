/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.CFGDiscovery
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.SequentialLogical64
open X86

private def emptyMemory : Memory where
  read := fun _ => none
  executable := fun _ => false

/-- Only the exact instruction window is accessible. A register operation
cannot obtain operands from a hidden data mapping. -/
private def entry (code : List Byte) (registers : Register → Word := fun _ => 0)
    (flags : Word := 0xed7) (data : Memory := emptyMemory) : State where
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

private def nextView (af : Bool) (state : State)
    (view : State → List Sequential.Read → α) : Except Error α := do
  let observation ← Sequential.step af state
  match observation.result with
  | .next final => return view final observation.reads
  | _ => throw .unexpectedReturn

private def banks : Register → Word
  | .rax => 0x10000000f | .rbx => 0x2000000cc
  | .r8 => 0x4000000aa | .r11 => 0x800000055
  | _ => 0xfeedface12345678

private def aliasRegisters : Register → Word
  | .rax => 0x8000000100000001 | .rcx => 0x8000000100000002
  | .rdx => 0x8000000100000003 | .rbx => 0x8000000100000004
  | .rsp => 0x8000000100000005 | .rbp => 0x8000000100000006
  | .rsi => 0x8000000100000007 | .rdi => 0x8000000100000008
  | .r8 => 0x8000000100000009 | .r9 => 0x800000010000000a
  | .r10 => 0x800000010000000b | .r11 => 0x800000010000000c
  | .r12 => 0x800000010000000d | .r13 => 0x800000010000000e
  | .r14 => 0x800000010000000f | .r15 => 0x8000000100000010

private def bankWindows (opcode : Byte) : List (List Byte) :=
  [[0x48,opcode,0xd8], [0x49,opcode,0xd8], [0x4a,opcode,0xd8], [0x4b,opcode,0xd8],
   [0x4c,opcode,0xd8], [0x4d,opcode,0xd8], [0x4e,opcode,0xd8], [0x4f,opcode,0xd8]]

private def bankView (opcode : Byte) (af : Bool) :=
  (bankWindows opcode).map fun bytes => nextView af (entry bytes banks)
    (fun state reads => (state.registers .rax,state.registers .rbx,
      state.registers .r8,state.registers .r11,state.rip,reads))

/-- Literal operand vectors distinguish all R/B banks and both destination
fields. Complete affected-bank snapshots also catch reversed direction even
though the logical operations themselves are commutative. X must be ignored. -/
theorem and_banks_and_directions (af : Bool) :
    (bankView 0x21 af, bankView 0x23 af) =
    ([.ok (0xc,0x2000000cc,0x4000000aa,0x800000055,4099,[]),
      .ok (0x10000000f,0x2000000cc,0x88,0x800000055,4099,[]),
      .ok (0xc,0x2000000cc,0x4000000aa,0x800000055,4099,[]),
      .ok (0x10000000f,0x2000000cc,0x88,0x800000055,4099,[]),
      .ok (5,0x2000000cc,0x4000000aa,0x800000055,4099,[]),
      .ok (0x10000000f,0x2000000cc,0,0x800000055,4099,[]),
      .ok (5,0x2000000cc,0x4000000aa,0x800000055,4099,[]),
      .ok (0x10000000f,0x2000000cc,0,0x800000055,4099,[])],
     [.ok (0x10000000f,0xc,0x4000000aa,0x800000055,4099,[]),
      .ok (0x10000000f,0x88,0x4000000aa,0x800000055,4099,[]),
      .ok (0x10000000f,0xc,0x4000000aa,0x800000055,4099,[]),
      .ok (0x10000000f,0x88,0x4000000aa,0x800000055,4099,[]),
      .ok (0x10000000f,0x2000000cc,0x4000000aa,5,4099,[]),
      .ok (0x10000000f,0x2000000cc,0x4000000aa,0,4099,[]),
      .ok (0x10000000f,0x2000000cc,0x4000000aa,5,4099,[]),
      .ok (0x10000000f,0x2000000cc,0x4000000aa,0,4099,[])]) := by rfl

theorem or_banks_and_directions (af : Bool) :
    (bankView 0x09 af, bankView 0x0b af) =
    ([.ok (0x3000000cf,0x2000000cc,0x4000000aa,0x800000055,4099,[]),
      .ok (0x10000000f,0x2000000cc,0x6000000ee,0x800000055,4099,[]),
      .ok (0x3000000cf,0x2000000cc,0x4000000aa,0x800000055,4099,[]),
      .ok (0x10000000f,0x2000000cc,0x6000000ee,0x800000055,4099,[]),
      .ok (0x90000005f,0x2000000cc,0x4000000aa,0x800000055,4099,[]),
      .ok (0x10000000f,0x2000000cc,0xc000000ff,0x800000055,4099,[]),
      .ok (0x90000005f,0x2000000cc,0x4000000aa,0x800000055,4099,[]),
      .ok (0x10000000f,0x2000000cc,0xc000000ff,0x800000055,4099,[])],
     [.ok (0x10000000f,0x3000000cf,0x4000000aa,0x800000055,4099,[]),
      .ok (0x10000000f,0x6000000ee,0x4000000aa,0x800000055,4099,[]),
      .ok (0x10000000f,0x3000000cf,0x4000000aa,0x800000055,4099,[]),
      .ok (0x10000000f,0x6000000ee,0x4000000aa,0x800000055,4099,[]),
      .ok (0x10000000f,0x2000000cc,0x4000000aa,0x90000005f,4099,[]),
      .ok (0x10000000f,0x2000000cc,0x4000000aa,0xc000000ff,4099,[]),
      .ok (0x10000000f,0x2000000cc,0x4000000aa,0x90000005f,4099,[]),
      .ok (0x10000000f,0x2000000cc,0x4000000aa,0xc000000ff,4099,[])]) := by rfl

theorem xor_banks_and_directions (af : Bool) :
    (bankView 0x31 af, bankView 0x33 af) =
    ([.ok (0x3000000c3,0x2000000cc,0x4000000aa,0x800000055,4099,[]),
      .ok (0x10000000f,0x2000000cc,0x600000066,0x800000055,4099,[]),
      .ok (0x3000000c3,0x2000000cc,0x4000000aa,0x800000055,4099,[]),
      .ok (0x10000000f,0x2000000cc,0x600000066,0x800000055,4099,[]),
      .ok (0x90000005a,0x2000000cc,0x4000000aa,0x800000055,4099,[]),
      .ok (0x10000000f,0x2000000cc,0xc000000ff,0x800000055,4099,[]),
      .ok (0x90000005a,0x2000000cc,0x4000000aa,0x800000055,4099,[]),
      .ok (0x10000000f,0x2000000cc,0xc000000ff,0x800000055,4099,[])],
     [.ok (0x10000000f,0x3000000c3,0x4000000aa,0x800000055,4099,[]),
      .ok (0x10000000f,0x600000066,0x4000000aa,0x800000055,4099,[]),
      .ok (0x10000000f,0x3000000c3,0x4000000aa,0x800000055,4099,[]),
      .ok (0x10000000f,0x600000066,0x4000000aa,0x800000055,4099,[]),
      .ok (0x10000000f,0x2000000cc,0x4000000aa,0x90000005a,4099,[]),
      .ok (0x10000000f,0x2000000cc,0x4000000aa,0xc000000ff,4099,[]),
      .ok (0x10000000f,0x2000000cc,0x4000000aa,0x90000005a,4099,[]),
      .ok (0x10000000f,0x2000000cc,0x4000000aa,0xc000000ff,4099,[])]) := by rfl

/-- All sixteen register encodings, including RSP/R12 and both register banks,
perform full-width self-XOR. AF is observable at the independently supplied
choice, while zero/parity and preserved DF/IF are checked as literal bits. -/
theorem self_xor_every_register (af : Bool) :
    ([([0x48,0x31,0xc0],.rax), ([0x48,0x33,0xc9],.rcx),
      ([0x48,0x31,0xd2],.rdx), ([0x48,0x33,0xdb],.rbx),
      ([0x48,0x31,0xe4],.rsp), ([0x48,0x33,0xed],.rbp),
      ([0x48,0x31,0xf6],.rsi), ([0x48,0x33,0xff],.rdi),
      ([0x4d,0x31,0xc0],.r8), ([0x4f,0x33,0xc9],.r9),
      ([0x4d,0x31,0xd2],.r10), ([0x4f,0x33,0xdb],.r11),
      ([0x4d,0x31,0xe4],.r12), ([0x4f,0x33,0xed],.r13),
      ([0x4d,0x31,0xf6],.r14), ([0x4f,0x33,0xff],.r15)] :
      List (List Byte × Register)).map (fun (bytes,destination) =>
        nextView af (entry bytes aliasRegisters)
          (fun state reads => (state.registers destination,
            state.flags &&& ~~~(0x10 : Word),state.flags.getLsbD 4,state.rip,reads))) =
    List.replicate 16 (.ok (0,0x646,af,4099,[])) := by cases af <;> rfl

/-- High-half-only nonzero results distinguish 64-bit ZF/SF from a narrowed
implementation. CF/OF begin set and must clear; parity uses only the low byte.
The oracle gives literal result/status words, independent of flag helpers. -/
theorem defined_status_vectors (af : Bool) :
    ([(0x21,0xffffffffffffffff,0x8000000000000001),
      (0x23,0x100000000,0x100000000), (0x21,0xaaaaaaaaaaaaaaaa,0x5555555555555555),
      (0x09,0x8000000000000000,1), (0x0b,0x100000000,0), (0x09,1,2),
      (0x31,0x80000001000000ff,0x80000001000000ff),
      (0x33,0x8000000000000000,1), (0x31,1,3)] : List (Byte × Word × Word)).map
      (fun (opcode,left,right) =>
        let modrm : Byte := if opcode = 0x23 ∨ opcode = 0x0b ∨ opcode = 0x33 then 0xc1 else 0xc8
        nextView af (entry [0x48,opcode,modrm]
          (fun (register : Register) => if register = Register.rax then left else if register = Register.rcx then right else 7))
          (fun state reads => (state.registers .rax,state.registers .rcx,
            state.flags &&& ~~~(0x10 : Word),state.flags.getLsbD 4,reads))) =
    [.ok (0x8000000000000001,0x8000000000000001,0x682,af,[]),
     .ok (0x100000000,0x100000000,0x606,af,[]),
     .ok (0,0x5555555555555555,0x646,af,[]),
     .ok (0x8000000000000001,1,0x682,af,[]),
     .ok (0x100000000,0,0x606,af,[]), .ok (3,2,0x606,af,[]),
     .ok (0,0x80000001000000ff,0x646,af,[]),
     .ok (0x8000000000000001,1,0x682,af,[]), .ok (2,3,0x602,af,[])] := by
  cases af <;> rfl

private def allRegisters : List Register :=
  [.rax,.rcx,.rdx,.rbx,.rsp,.rbp,.rsi,.rdi,.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15]

/-- An actual extended-bank AND preserves arbitrary current RAM, every
nondestination register and every nonarithmetic flag. Operand values remain
arbitrary; no accessibility, canonicality or alias restriction is imposed. -/
theorem and_complete_context (registers : Register → Word) (flags : Word)
    (data : Memory) (af : Bool) :
    nextView af (entry [0x4f,0x21,0xd8] registers flags data)
      (fun state reads => (allRegisters.map state.registers,state.memory,
        state.flags &&& ~~~arithmeticFlagMask,state.rip,reads)) =
    .ok ([registers .rax,registers .rcx,registers .rdx,registers .rbx,
      registers .rsp,registers .rbp,registers .rsi,registers .rdi,
      registers .r8 &&& registers .r11,registers .r9,registers .r10,registers .r11,
      registers .r12,registers .r13,registers .r14,registers .r15],
      (entry [0x4f,0x21,0xd8] registers flags data).memory,
      flags &&& ~~~arithmeticFlagMask,4099,[]) := by
  have decoded : Sequential.decodeAt (entry [0x4f,0x21,0xd8] registers flags data) =
      .ok (.logicalReg64 .band .r8 .r11) := by
    simp [Sequential.decodeAt, X86.decodeAt, Sequential.decodeNewAt, Sequential.decodeREXWAt,
      entry, fetchByte, canonical, Sequential.rexWPrefix, Sequential.rexModRMReg,
      Sequential.rexModRMRM, Sequential.highRegister]
  unfold nextView
  rw [Sequential.step_eq_execute af decoded]
  simp only [Sequential.execute_logicalReg64, Sequential.LogicalOp.eval, State.writeRegister,
    allRegisters, List.map_cons,List.map_nil,reduceCtorEq,ite_true,ite_false,
    Sequential.logicalFlags64_preserves,ok_bind,pure_ok,entry] <;> rfl

/-- None of the six register opcodes may fall through to a memory form.
Immediate, repeated/interposed prefix and W=0 forms remain outside this subset. -/
theorem unsupported_forms :
    ([[0x48,0x21,0x08], [0x48,0x23,0x48,0], [0x48,0x09,0x88,0,0,0,0],
      [0x48,0x0b,0x08], [0x48,0x31,0x48,0], [0x48,0x33,0x88,0,0,0,0],
      [0x48,0x81,0xe0,1,0,0,0], [0x48,0x83,0xe0,1],
      [0x48,0x83,0xc8,1], [0x48,0x83,0xf0,1],
      [0x48,0x25,1,0,0,0], [0x48,0x0d,1,0,0,0], [0x48,0x35,1,0,0,0],
      [0x48,0x48,0x21,0xc8], [0x48,0x66,0x09,0xc8],
      [0x48,0xf0,0x31,0xc8]] : List (List Byte)).map
      (fun bytes => Sequential.decodeAt (entry bytes)) =
    List.replicate 16 (.error .unsupportedEncoding) := by rfl

theorem unsupported_leading_prefixes :
    ([[0x40,0x21,0xc8], [0x47,0x09,0xc8], [0x66,0x48,0x31,0xc8],
      [0x67,0x48,0x21,0xc8], [0xf0,0x48,0x09,0xc8],
      [0xf2,0x48,0x31,0xc8], [0xf3,0x48,0x33,0xc8]] : List (List Byte)).map
      (fun bytes => Sequential.decodeAt (entry bytes)) =
    [.error .unsupportedEncoding, .error .unsupportedEncoding,
      .error .unsupportedEncoding, .error (.unsupportedOpcode 0x67),
      .error .unsupportedEncoding, .error (.unsupportedOpcode 0xf2),
      .error .unsupportedEncoding] := by rfl

/-- Every required byte uses execute permission. An inaccessible byte beyond
an unsupported memory ModRM is irrelevant; truncation of a register form is a
real fetch fault rather than an unsupported-encoding result. -/
theorem truncated_and_nonexecutable_fetch (af : Bool) :
    (([[0x48], [0x48,0x21], [0x4f,0x23], [0x48,0x09], [0x4f,0x0b],
        [0x48,0x31], [0x4f,0x33]] : List (List Byte)).map
        (fun bytes => (Sequential.step af (entry bytes)).map (fun _ => ())),
      (Sequential.step af { entry [0x48,0x31,0xc8] with
        memory := { (entry [0x48,0x31,0xc8]).memory with
          executable := fun address => decide (address ≠ 4098) } }).map (fun _ => ())) =
    ([.error (.inaccessibleInstruction 4097), .error (.inaccessibleInstruction 4098),
      .error (.inaccessibleInstruction 4098), .error (.inaccessibleInstruction 4098),
      .error (.inaccessibleInstruction 4098), .error (.inaccessibleInstruction 4098),
      .error (.inaccessibleInstruction 4098)], .error (.inaccessibleInstruction 4098)) := by rfl

/-- This also exercises constructor data, lengths and CFG admission of all
three operations; the unchanged final RET sits at the exact final byte. -/
theorem cfg_admission :
    (Sequential.CFG.analyze [0x48,0x21,0xc8,0x4f,0x0b,0xd8,0x4a,0x31,0xe4,0xc3]).map
      (fun graph => graph.nodes.map (fun node =>
        (node.offset,node.instruction,node.instruction.length))) =
    .ok [(0,.logicalReg64 .band .rax .rcx,3),
      (3,.logicalReg64 .bor .r11 .r8,3),
      (6,.logicalReg64 .bxor .rsp .rsp,3),(9,.legacy .ret,1)] := by rfl

/-- Self XOR retains its existing constructor and zero-extension behavior;
non-self XOR32 uses the shared logical instruction with its decoded operands. -/
theorem legacy_self_xor_unchanged (af : Bool) :
    (Sequential.decodeAt (entry [0x31,0xc0]),
      Sequential.decodeAt (entry [0x31,0xc8]),
      nextView af (entry [0x31,0xc0] (fun _ => 0x80000001000000ff))
        (fun state reads => (state.registers .rax,state.rip,reads))) =
    (.ok (.xorSelf32 .rax),.ok (.logicalReg32 .bxor .rax .rcx false),
      .ok (0,4098,[])) := by rfl

end EDSL.Tests.SequentialLogical64

#print axioms EDSL.Tests.SequentialLogical64.and_complete_context
#audit_edsl
