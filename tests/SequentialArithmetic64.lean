/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.CFGDiscovery
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.SequentialArithmetic64
open X86

private def emptyMemory : Memory where
  read := fun _ => none
  executable := fun _ => false

/-- Only instruction bytes are supplied here; operand RAM and permissions
remain independent inputs. LEA must succeed without readable operand RAM. -/
private def entry (code : List Byte) (registers : Register → Word := fun _ => 0)
    (flags : Word := 0x246) (data : Memory := emptyMemory) : State where
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

private def leaRegisters : Register → Word
  | .rax => 0x500000000 | .rcx => 3 | .rdi => 0x100000000
  | .rsi => 7 | .r9 => 5 | .r12 => 0x300000000 | .r15 => 0x200000000
  | .rsp => 0xfffffffffffffff0 | _ => 0xfeedface12345678

/-- The expected addresses are literal assembler operand vectors, rather
than a second ModRM/SIB evaluator. Every scale and each R/X/B role is distinct. -/
theorem lea_scales_and_extended_banks (af : Bool) :
    ([([0x48,0x8d,0x14,0x0f], .rdx), ([0x48,0x8d,0x14,0x4f], .rdx),
      ([0x48,0x8d,0x14,0x8f], .rdx), ([0x48,0x8d,0x14,0xcf], .rdx),
      ([0x49,0x8d,0x14,0x8f], .rdx), ([0x4a,0x8d,0x14,0x8f], .rdx),
      ([0x4b,0x8d,0x14,0x8f], .rdx), ([0x4c,0x8d,0x14,0x8f], .r10),
      ([0x4d,0x8d,0x14,0x8f], .r10), ([0x4e,0x8d,0x14,0x8f], .r10),
      ([0x4f,0x8d,0x14,0x8f], .r10)] : List (List Byte × Register)).map
      (fun (bytes, destination) => nextView af (entry bytes leaRegisters)
        (fun state reads => (state.registers destination, state.rip, reads))) =
    [.ok (0x100000003,4100,[]), .ok (0x100000006,4100,[]),
      .ok (0x10000000c,4100,[]), .ok (0x100000018,4100,[]),
      .ok (0x20000000c,4100,[]), .ok (0x100000014,4100,[]),
      .ok (0x200000014,4100,[]), .ok (0x10000000c,4100,[]),
      .ok (0x20000000c,4100,[]), .ok (0x100000014,4100,[]),
      .ok (0x200000014,4100,[])] := by rfl

theorem lea_base_banks_ignore_x (af : Bool) :
    ([([0x48,0x8d,0x1f], .rbx), ([0x49,0x8d,0x1f], .rbx),
      ([0x4a,0x8d,0x1f], .rbx), ([0x4b,0x8d,0x1f], .rbx),
      ([0x4c,0x8d,0x1f], .r11), ([0x4d,0x8d,0x1f], .r11),
      ([0x4e,0x8d,0x1f], .r11), ([0x4f,0x8d,0x1f], .r11)] :
      List (List Byte × Register)).map (fun (bytes,destination) =>
        nextView af (entry bytes leaRegisters)
          (fun state reads => (state.registers destination,state.rip,reads))) =
    [.ok (0x100000000,4099,[]), .ok (0x200000000,4099,[]),
      .ok (0x100000000,4099,[]), .ok (0x200000000,4099,[]),
      .ok (0x100000000,4099,[]), .ok (0x200000000,4099,[]),
      .ok (0x100000000,4099,[]), .ok (0x200000000,4099,[])] := by rfl

/-- Destination/base/index aliases must use the complete pre-state. X=1
makes index code4 a real R12, and RSP is an ordinary LEA destination/base. -/
theorem lea_aliases (af : Bool) :
    ([([0x48,0x8d,0x3c,0xb7], .rdi), ([0x48,0x8d,0x0c,0xcf], .rcx),
      ([0x4f,0x8d,0x24,0xe4], .r12), ([0x48,0x8d,0x24,0x0c], .rsp),
      ([0x4a,0x8d,0x24,0xe4], .rsp)] : List (List Byte × Register)).map
      (fun (bytes, destination) => nextView af (entry bytes leaRegisters)
        (fun state reads => (state.registers destination, state.flags, reads))) =
    [.ok (0x10000001c,0x246,[]), .ok (0x100000018,0x246,[]),
      .ok (0x1b00000000,0x246,[]), .ok (0xfffffffffffffff3,0x246,[]),
      .ok (0x17fffffff0,0x246,[])] := by rfl

private def allRegisters : List Register :=
  [.rax,.rcx,.rdx,.rbx,.rsp,.rbp,.rsi,.rdi,.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15]

set_option maxRecDepth 4096 in
/-- An arbitrary flag word and the complete RAM record survive. In
particular code/data/stack permissions and every non-destination GPR survive;
the only computed value is the mathematical full64 pre-state address. -/
theorem lea_complete_context (registers : Register → Word) (flags : Word)
    (data : Memory) (af : Bool) :
    nextView af (entry [0x48,0x8d,0x04,0xc8] registers flags data)
      (fun state reads => (allRegisters.map state.registers, state.memory, state.flags, state.rip, reads)) =
    .ok ([registers .rax + (registers .rcx <<< 3), registers .rcx, registers .rdx,
      registers .rbx, registers .rsp, registers .rbp, registers .rsi, registers .rdi,
      registers .r8, registers .r9, registers .r10, registers .r11,
      registers .r12, registers .r13, registers .r14, registers .r15],
      (entry [0x48,0x8d,0x04,0xc8] registers flags data).memory, flags, 4100, []) := by
  have decoded : Sequential.decodeAt (entry [0x48,0x8d,0x04,0xc8] registers flags data) =
      .ok (.lea64 .rax (.indexed .rax .rcx 3)) := by
    simp [Sequential.decodeAt, X86.decodeAt, Sequential.decodeNewAt, Sequential.decodeREXWAt,
      entry, fetchByte, canonical, Sequential.rexWPrefix, Sequential.rexModRMReg,
      Sequential.rexModRMRM, Sequential.decodeQWordAddressAt, Sequential.rexSIBIndex,
      Sequential.modRMReg, Sequential.modRMRM, Sequential.lowRegister]
  unfold nextView
  rw [Sequential.step_eq_execute af decoded]
  rfl

/-- LEA computes an unmapped noncanonical word without reading it. MOV from
the same operand really faults. Modular address addition also wraps at bit64. -/
theorem lea_noncanonical_and_wrap (af : Bool) :
    (nextView af (entry [0x48,0x8d,0x07] (fun _ => 0x800000000000))
        (fun state reads => (state.registers .rax, canonical (state.registers .rax), reads)),
      (Sequential.step af (entry [0x48,0x8b,0x07] (fun _ => 0x800000000000))).map (fun _ => ()),
      nextView af (entry [0x48,0x8d,0x04,0x08]
        (fun register => if register = .rax then 0xffffffffffffffff else 1))
        (fun state reads => (state.registers .rax, state.flags, reads)),
      nextView af (entry [0x48,0x8d,0x04,0xc8]
        (fun register => if register = .rax then 5 else 0x2000000000000001))
        (fun state reads => (state.registers .rax, state.flags, reads))) =
    (.ok (0x800000000000,false,[]), .error (.inaccessibleData 0x800000000000),
      .ok (0,0x246,[]), .ok (13,0x246,[])) := by rfl

private def addRegisters : Register → Word
  | .rax => 0x1111111100000001 | .rbx => 0x2222222200000003
  | .r8 => 0x3333333300000005 | .r11 => 0x4444444400000007
  | _ => 0xfeedface12345678

/-- Both opcode directions and each REX bank affect the destination/source
selected by actual bytes. X is ignored for register mode; high halves matter. -/
theorem add_banks_and_directions (af : Bool) :
    ([([0x48,0x01,0xd8], .rax), ([0x49,0x01,0xd8], .r8),
      ([0x4a,0x01,0xd8], .rax), ([0x4b,0x01,0xd8], .r8),
      ([0x4c,0x01,0xd8], .rax), ([0x4d,0x01,0xd8], .r8),
      ([0x4e,0x01,0xd8], .rax), ([0x4f,0x01,0xd8], .r8),
      ([0x48,0x03,0xd8], .rbx), ([0x49,0x03,0xd8], .rbx),
      ([0x4a,0x03,0xd8], .rbx), ([0x4b,0x03,0xd8], .rbx),
      ([0x4c,0x03,0xd8], .r11), ([0x4d,0x03,0xd8], .r11),
      ([0x4e,0x03,0xd8], .r11), ([0x4f,0x03,0xd8], .r11)] :
      List (List Byte × Register)).map (fun (bytes, destination) =>
        nextView af (entry bytes addRegisters) (fun state reads =>
          (state.registers destination,state.rip,reads))) =
    [.ok (0x3333333300000004,4099,[]), .ok (0x5555555500000008,4099,[]),
      .ok (0x3333333300000004,4099,[]), .ok (0x5555555500000008,4099,[]),
      .ok (0x5555555500000008,4099,[]), .ok (0x777777770000000c,4099,[]),
      .ok (0x5555555500000008,4099,[]), .ok (0x777777770000000c,4099,[]),
      .ok (0x3333333300000004,4099,[]), .ok (0x5555555500000008,4099,[]),
      .ok (0x3333333300000004,4099,[]), .ok (0x5555555500000008,4099,[]),
      .ok (0x5555555500000008,4099,[]), .ok (0x777777770000000c,4099,[]),
      .ok (0x5555555500000008,4099,[]), .ok (0x777777770000000c,4099,[])] := by rfl

/-- Literal arithmetic results and architectural status words cover unsigned
carry, signed overflow, nibble carry, parity, zero and sign independently.
The initial arithmetic bits are set, so stale status bits cannot pass. -/
theorem add_status_vectors (af : Bool) :
    ([(0,0), (0xffffffffffffffff,1), (0x7fffffffffffffff,1),
      (0x8000000000000000,0x8000000000000000), (15,1), (1,2), (0,1),
      (0x100000000,0x100000000)] : List (Word × Word)).map (fun (left,right) =>
      nextView af (entry [0x48,0x01,0xc8]
        (fun (register : Register) => if register = Register.rax then left
          else if register = Register.rcx then right else 0) 0xad7)
        (fun state reads => (state.registers .rax,state.flags,reads))) =
    [.ok (0,0x246,[]), .ok (0,0x257,[]), .ok (0x8000000000000000,0xa96,[]),
      .ok (0,0xa47,[]), .ok (16,0x212,[]), .ok (3,0x206,[]), .ok (1,0x202,[]),
      .ok (0x200000000,0x206,[])] := by rfl

/-- Self-add doubles the original full register rather than observing a
partially updated operand. RSP is supported as both destination and source. -/
theorem add_self_and_rsp (af : Bool) :
    ([([0x48,0x01,0xc0], .rax), ([0x4f,0x03,0xdb], .r11),
      ([0x48,0x01,0xe4], .rsp), ([0x4c,0x03,0xe4], .r12)] :
      List (List Byte × Register)).map (fun (bytes,destination) =>
        nextView af (entry bytes (fun _ => 0x8000000000000001))
          (fun state reads => (state.registers destination,state.flags,reads))) =
    List.replicate 4 (.ok (2,0xa03,[])) := by rfl

set_option maxRecDepth 4096 in
theorem add_complete_context (registers : Register → Word) (flags : Word)
    (data : Memory) (af : Bool) :
    nextView af (entry [0x4f,0x01,0xd8] registers flags data)
      (fun state reads => (allRegisters.map state.registers, state.memory,
        state.flags &&& ~~~arithmeticFlagMask, state.rip, reads)) =
    .ok ([registers .rax, registers .rcx, registers .rdx, registers .rbx,
      registers .rsp, registers .rbp, registers .rsi, registers .rdi,
      registers .r8 + registers .r11, registers .r9, registers .r10, registers .r11,
      registers .r12, registers .r13, registers .r14, registers .r15],
      (entry [0x4f,0x01,0xd8] registers flags data).memory,
      flags &&& ~~~arithmeticFlagMask,4099,[]) := by
  have decoded : Sequential.decodeAt (entry [0x4f,0x01,0xd8] registers flags data) =
      .ok (.addReg64 .r8 .r11) := by
    simp [Sequential.decodeAt, X86.decodeAt, Sequential.decodeNewAt, Sequential.decodeREXWAt,
      entry, fetchByte, canonical, Sequential.rexWPrefix, Sequential.rexModRMReg,
      Sequential.rexModRMRM, Sequential.highRegister]
  unfold nextView
  rw [Sequential.step_eq_execute af decoded]
  simp only [Sequential.execute_addReg64, State.writeRegister, allRegisters, List.map_cons,
    List.map_nil, reduceCtorEq, ite_true, ite_false, Sequential.addFlags64_preserves,
    ok_bind, pure_ok, entry] <;> rfl

/-- The new profile does not silently admit LEA register mode, displacements,
RIP-relative/missing SIB operands, memory ADD, W=0 or extra prefixes. -/
theorem unsupported_forms :
    ([[0x48,0x8d,0xc0], [0x48,0x8d,0x40,0], [0x48,0x8d,0x05,0,0,0,0],
      [0x48,0x8d,0x04,0x20], [0x4b,0x8d,0x04,0x0d],
      [0x48,0x01,0x08], [0x48,0x03,0x08], [0x48,0x48,0x01,0xc8],
      [0x48,0x66,0x8d,0x07], [0x48,0xf0,0x01,0xc8]] : List (List Byte)).map
      (fun bytes => Sequential.decodeAt (entry bytes)) =
    List.replicate 10 (.error .unsupportedEncoding) := by rfl

theorem unsupported_leading_prefixes :
    ([[0x40,0x8d,0x07], [0x47,0x01,0xc8], [0x66,0x48,0x01,0xc8],
      [0x67,0x48,0x8d,0x07], [0xf0,0x48,0x01,0xc8]] : List (List Byte)).map
      (fun bytes => Sequential.decodeAt (entry bytes)) =
    [.error (.unsupportedOpcode 0x40), .error (.unsupportedOpcode 0x47),
      .error (.unsupportedOpcode 0x66), .error (.unsupportedOpcode 0x67),
      .error .unsupportedEncoding] := by rfl

theorem truncated_and_nonexecutable_fetch (af : Bool) :
    (([[0x48,0x8d], [0x48,0x8d,0x04], [0x4f,0x03]] : List (List Byte)).map
        (fun bytes => (Sequential.step af (entry bytes)).map (fun _ => ())),
      (Sequential.step af { entry [0x48,0x8d,0x04,0xc8] with
        memory := { (entry [0x48,0x8d,0x04,0xc8]).memory with
          executable := fun address => decide (address ≠ 4099) } }).map (fun _ => ())) =
    ([.error (.inaccessibleInstruction 4098), .error (.inaccessibleInstruction 4099),
      .error (.inaccessibleInstruction 4098)], .error (.inaccessibleInstruction 4099)) := by rfl

/-- Discovery accepts these register effects and uses the actual SIB and
register instruction lengths before the terminal return. -/
theorem cfg_admission :
    (Sequential.CFG.analyze [0x4f,0x8d,0x14,0x8f,0x4f,0x01,0xd8,0xc3]).map
      (fun graph => graph.nodes.map (fun node =>
        (node.offset,node.instruction,node.instruction.length))) =
    .ok [(0,.lea64 .r10 (.indexed .r15 .r9 2),4),
      (4,.addReg64 .r8 .r11,3),(7,.legacy .ret,1)] := by rfl

end EDSL.Tests.SequentialArithmetic64

#audit_edsl
