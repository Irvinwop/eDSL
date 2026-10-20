/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.ByteOrder
import EDSL.X86.Sequential.CFGDiscovery
import EDSL.X86.Sequential.CFGTransport
import EDSL.X86.Sequential.Return
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.SequentialByteOrderISA
open X86 X86.Sequential

private def entry (bytes : List Byte) (registers : Register → Word := fun _ => 8192)
    (data : Word → Option Byte := fun _ => none) : State where
  registers := registers
  rip := 4096
  flags := 0x602
  memory := {
    read := fun address => if 4096 ≤ address.toNat ∧ address.toNat < 4096 + bytes.length
      then bytes[address.toNat - 4096]? else data address
    executable := fun address => decide (4096 ≤ address.toNat ∧ address.toNat < 4096 + bytes.length)
    writable := fun _ => false }

private def observe (state : State) (registers : List Register := [.rax,.rcx,.r8]) (af : Bool := false) :
    Except Error (List Word × Word × Word × List Read) := do
  let observation ← Sequential.step af state
  match observation.result with
  | .next final => return (registers.map final.registers, final.flags, final.rip, observation.reads)
  | _ => throw .unexpectedReturn

private def oneByte (address : Word) (value : Byte) : Word → Option Byte :=
  fun query => if query = address then some value else none

/-- Actual frozen instructions and independently selected R/X/B and opcode
directions. In particular byte register fields use the prefix-dependent bank. -/
theorem decoded_forms :
    ([[0x0f,0xb6,0x0c,7], [0x0f,0xb6,4,0x0f], [0x44,0x0f,0xb6,4,6],
      [0x44,0x0f,0xb6,4,0x0e], [0x0f,0xb6,0xc1], [0x47,0x0f,0xb6,4,0xa6],
      [0x41,0x0f,0xb6,0xd7], [0x40,0x0f,0xb6,0xc4],
      [0x44,0x38,0xc1], [0x44,0x38,0xc0], [0x45,0x38,0xef], [0x40,0x38,0xe4],
      [0x3a,0xcb], [0x44,0x29,0xc0], [0x45,0x2b,0xcf], [0x29,0xc0]] : List (List Byte)).map
      (fun bytes => Sequential.decodeAt (entry bytes)) =
    [.ok (.movzxMem8 .rcx (.indexed .rdi .rax 0) false),
     .ok (.movzxMem8 .rax (.indexed .rdi .rcx 0) false),
     .ok (.movzxMem8 .r8 (.indexed .rsi .rax 0) true),
     .ok (.movzxMem8 .r8 (.indexed .rsi .rcx 0) true),
     .ok (.movzxReg8 .rax .rcx false), .ok (.movzxMem8 .r8 (.indexed .r14 .r12 2) true),
     .ok (.movzxReg8 .rdx .r15 true), .ok (.movzxReg8 .rax .rsp true),
     .ok (.cmpReg8 .rcx .r8 true), .ok (.cmpReg8 .rax .r8 true),
     .ok (.cmpReg8 .r15 .r13 true), .ok (.cmpReg8 .rsp .rsp true),
     .ok (.cmpReg8 .rcx .rbx false), .ok (.subReg32 .rax .r8 true),
     .ok (.subReg32 .r9 .r15 true), .ok (.subReg32 .rax .rax false)] := by rfl

/-- A sole readable byte at the final low canonical address forces DATA1.
Zero extension must clear every old high bit, while source/address aliases
must use the old address. No DATA execute/write permission is available. -/
theorem movzx_one_byte_and_alias (af : Bool) :
    observe (entry [0x0f,0xb6,0] (fun _ => 0x7fffffffffff)
      (oneByte 0x7fffffffffff 0x80)) [.rax,.rcx] af =
      .ok ([0x80,0x7fffffffffff],0x602,4099,[⟨.data,0x7fffffffffff,1⟩]) ∧
    observe (entry [0x0f,0xb6,4,0] (fun _ => 0x100000001)
      (oneByte 0x200000002 0xff)) [.rax,.rdi] af =
      .ok ([0xff,0x100000001],0x602,4100,[⟨.data,0x200000002,1⟩]) := by exact ⟨rfl,rfl⟩

/-- All three extension bits participate in a full64 scaled address. R8 is
the destination; the low-byte source is memory, not a register or a DATA4 load. -/
theorem movzx_full64_rex_address :
    observe (entry [0x47,0x0f,0xb6,4,0xa6] (fun register => match register with
      | .r14 => 0x200000001 | .r12 => 0x100000002 | _ => 0xffffffffffffffff)
      (oneByte 0x600000009 0xa5)) [.r8,.r12,.r14] =
      .ok ([0xa5,0x100000002,0x200000001],0x602,4101,[⟨.data,0x600000009,1⟩]) := by rfl

/-- The prefixed low bank must read SPL/BPL/SIL/DIL, not AH/CH/DH/BH.
Self-MOVZX reads the original byte, clears upper bits and leaves flags alone. -/
theorem movzx_register_banks :
    ([[0x40,0x0f,0xb6,0xc4], [0x40,0x0f,0xb6,0xc5],
      [0x40,0x0f,0xb6,0xc6], [0x40,0x0f,0xb6,0xc7],
      [0x0f,0xb6,0xc0], [0x45,0x0f,0xb6,0xc9]] : List (List Byte)).map
      (fun bytes => observe (entry bytes (fun register => match register with
        | .rax => 0xfedcba987654ab80 | .rsp => 0xffffffffffffff11
        | .rbp => 0xffffffffffffff22 | .rsi => 0xffffffffffffff33
        | .rdi => 0xffffffffffffff44 | .r9 => 0xffffffffffffffe7 | _ => 0)) [.rax,.r9]) =
    [.ok ([0x11,0xffffffffffffffe7],0x602,4100,[]),
     .ok ([0x22,0xffffffffffffffe7],0x602,4100,[]),
     .ok ([0x33,0xffffffffffffffe7],0x602,4100,[]),
     .ok ([0x44,0xffffffffffffffe7],0x602,4100,[]),
     .ok ([0x80,0xffffffffffffffe7],0x602,4099,[]),
     .ok ([0xfedcba987654ab80,0xe7],0x602,4100,[])] := by rfl

/-- Fixed architectural flag vectors distinguish width8, subtraction order,
overflow, auxiliary borrow, parity and high-half contamination. -/
theorem cmp8_flag_vectors (af : Bool) :
    ([(0,0x123456789abcde01), (0x80,0x100000001), (0x7f,0x12345678000000ff),
      (0xff,0x80000000000000ff), (0,0x8000000000000080), (0x10,0x100000001)] :
      List (Word × Word)).map (fun (left,right) =>
        observe (entry [0x44,0x38,0xc1] (fun register => match register with
          | .rcx => left | .r8 => right | _ => 0xdeadbeef)) [] af) =
    [.ok ([],0x697,4099,[]), .ok ([],0xe12,4099,[]), .ok ([],0xe83,4099,[]),
     .ok ([],0x646,4099,[]), .ok ([],0xe83,4099,[]), .ok ([],0x616,4099,[])] := by rfl

/-- The opposite opcode direction, REX.B/R byte banks and self aliasing all
reach real register CMP. Neither operand consults inaccessible DATA memory. -/
theorem cmp8_directions_and_alias :
    observe (entry [0x38,0xd0] (fun register => if register = .rax then 1 else 2)) [] =
      .ok ([],0x697,4098,[]) ∧
    observe (entry [0x3a,0xd0] (fun register => if register = .rax then 1 else 2)) [] =
      .ok ([],0x602,4098,[]) ∧
    observe (entry [0x45,0x38,0xef] (fun register => if register = .r15 then 0x80 else 1)) [] =
      .ok ([],0xe12,4099,[]) ∧
    observe (entry [0x40,0x38,0xe4] (fun _ => 0xffffffffffffffff)) [] =
      .ok ([],0x646,4099,[]) := by exact ⟨rfl,rfl,rfl,rfl⟩

/-- SUB produces a zero-extended low32 result and all six flags. These values
also separate width32 from width8/64, and exercise both signed overflow edges. -/
theorem sub32_flag_and_value_vectors (af : Bool) :
    ([(0xabcdef0100000000,0x100000001), (0x1111111180000000,0x2222222200000001),
      (0x123456787fffffff,0xabcdef01ffffffff), (0x1234567812345678,0xfedcba9812345678),
      (0,0x100000080), (0xdeadbeef00000010,0x100000001)] : List (Word × Word)).map
      (fun (left,right) => observe (entry [0x44,0x29,0xc0] (fun (register : Register) =>
        if register = Register.rax then left else if register = Register.r8 then right else 0)) [.rax] af) =
    [.ok ([0xffffffff],0x697,4099,[]), .ok ([0x7fffffff],0xe16,4099,[]),
     .ok ([0x80000000],0xe87,4099,[]), .ok ([0],0x646,4099,[]),
     .ok ([0xffffff80],0x683,4099,[]), .ok ([0xf],0x616,4099,[])] := by rfl

theorem sub32_reverse_direction_and_alias :
    observe (entry [0x45,0x2b,0xcf] (fun register =>
      if register = .r9 then 0xffffffff00000007 else 0x100000003)) [.r9,.r15] =
      .ok ([4,0x100000003],0x602,4099,[]) ∧
    observe (entry [0x29,0xc0] (fun _ => 0xffffffffffffffff)) [.rax,.rsp] =
      .ok ([0,0xffffffffffffffff],0x646,4098,[]) := by exact ⟨rfl,rfl⟩

/-- Universal frame proofs instantiate actual production step at relocated
current code, including arbitrary GPRs, memory maps, nonarithmetic flags and AF. -/
theorem cmp_current_frames (state : State) (af : Bool)
    (code : CodeAt state.memory state.rip [0x44,0x38,0xc1]) :
    ∃ final, Sequential.step af state = .ok ⟨.next final, []⟩ ∧
      final.registers = state.registers ∧ final.memory = state.memory ∧
      final.flags &&& ~~~arithmeticFlagMask = state.flags &&& ~~~arithmeticFlagMask := by
  rw [step_code_eq_execute code (by decide) (offset := 0) (by decide) state rfl
    (by simp) (by rfl : Sequential.decodeAt (codeState [0x44,0x38,0xc1] 0) =
      .ok (.cmpReg8 .rcx .r8 true)) af]
  obtain ⟨final, actual, registers, memory, _, flags, _⟩ := execute_cmpReg8_context state .rcx .r8 true af
  exact ⟨final, actual, registers, memory, flags⟩

theorem movzx_current_frames (state : State) (af : Bool) (value : Byte)
    (code : CodeAt state.memory state.rip [0x44,0x0f,0xb6,4,6])
    (loaded : readDataByte state.memory (state.registers .rsi + state.registers .rax) = .ok value) :
    ∃ final, Sequential.step af state =
        .ok ⟨.next final, [⟨.data,state.registers .rsi + state.registers .rax,1⟩]⟩ ∧
      (final.registers .r8).toNat = value.toNat ∧
      (∀ register, register ≠ .r8 → final.registers register = state.registers register) ∧
      final.memory = state.memory ∧ final.flags = state.flags := by
  rw [step_code_eq_execute code (by decide) (offset := 0) (by decide) state rfl
    (by simp) (by rfl : Sequential.decodeAt (codeState [0x44,0x0f,0xb6,4,6] 0) =
      .ok (.movzxMem8 .r8 (.indexed .rsi .rax 0) true)) af]
  have read : readDataByte state.memory ((Address.indexed .rsi .rax 0).eval state) = .ok value := by
    simpa [Address.eval] using loaded
  rw [execute_movzxMem8, read]
  refine ⟨{ state.writeRegister .r8 ((value.setWidth 32).setWidth 64) with rip := state.rip + 5 },
    ?_, ?_, ?_, rfl, rfl⟩
  · simp only [ok_bind, pure_ok, Address.eval, show (0 : Fin 4).val = 0 from rfl,
      BitVec.shiftLeft_zero, Instruction.length, ↓reduceIte]
    rfl
  · simp only [State.writeRegister, ↓reduceIte]
    rw [BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64),
      BitVec.toNat_setWidth_of_le (by decide : 8 ≤ 32)]
  · intro register other
    simp [State.writeRegister, other]

theorem missing_and_nonexecutable_fetches :
    ([[0x0f], [0x0f,0xb6], [0x0f,0xb6,4], [0x44], [0x44,0x0f],
      [0x44,0x0f,0xb6], [0x44,0x0f,0xb6,4], [0x44,0x38], [0x44,0x29]] : List (List Byte)).map
      (fun bytes => Sequential.decodeAt (entry bytes)) =
    [.error (.inaccessibleInstruction 4097), .error (.inaccessibleInstruction 4098),
     .error (.inaccessibleInstruction 4099), .error (.inaccessibleInstruction 4097),
     .error (.inaccessibleInstruction 4098), .error (.inaccessibleInstruction 4099),
     .error (.inaccessibleInstruction 4100), .error (.inaccessibleInstruction 4098),
     .error (.inaccessibleInstruction 4098)] ∧
    (List.range 5).map (fun offset =>
      let state := entry [0x47,0x0f,0xb6,4,0xa6]
      Sequential.decodeAt { state with memory := { state.memory with
        executable := fun address => address != 4096 + BitVec.ofNat 64 offset } }) =
      [.error (.inaccessibleInstruction 4096), .error (.inaccessibleInstruction 4097),
       .error (.inaccessibleInstruction 4098), .error (.inaccessibleInstruction 4099),
       .error (.inaccessibleInstruction 4100)] := by exact ⟨rfl,rfl⟩

/-- Missing/noncanonical DATA faults produce no next state or fabricated
read observation. Register instructions require no DATA access at all. -/
theorem operand_faults_and_fetch_boundary :
    observe (entry [0x0f,0xb6,7]) = .error (.inaccessibleData 8192) ∧
    observe (entry [0x0f,0xb6,7] (fun _ => 0x800000000000) (fun _ => some 0)) =
      .error (.inaccessibleData 0x800000000000) ∧
    observe (entry [0x0f,0xb6,7] (fun _ => 0xffffffffffffffff) (oneByte 0xffffffffffffffff 0xff)) [.rax] =
      .ok ([0xff],0x602,4099,[⟨.data,0xffffffffffffffff,1⟩]) ∧
    observe (entry [0x0f,0xb6,0xc1] (fun _ => 0xffffffffffffffff)) [.rax] =
      .ok ([0xff],0x602,4099,[]) := by exact ⟨rfl,rfl,rfl,rfl⟩

/-- Unsupported widths, high-byte registers, memory SUB, displacement and
missing-base/index encodings cannot be accepted with a weaker interpretation. -/
theorem unsupported_forms :
    ([[0x0f,0xb6,0xc4], [0x0f,0xb6,0xc5], [0x0f,0xb6,0xc6], [0x0f,0xb6,0xc7],
      [0x38,0xc4], [0x38,0xe0], [0x3a,0xf8],
      [0x48,0x0f,0xb6,0xc0], [0x4f,0x0f,0xb6,0], [0x48,0x38,0xc0], [0x48,0x29,0xc0],
      [0x66,0x0f,0xb6,0], [0x67,0x0f,0xb6,0], [0x40,0x40,0x0f,0xb6,0],
      [0x0f,0xb6,0x40,0], [0x44,0x0f,0xb6,0x84,0,0,0,0,0],
      [0x0f,0xb6,5,0,0,0,0], [0x41,0x0f,0xb6,5,0,0,0,0],
      [0x0f,0xb6,4,0x20], [0x41,0x0f,0xb6,4,5],
      [0x29,7], [0x2b,7], [0x44,0x29,7], [0x44,0x38,7], [0x3a,7]] : List (List Byte)).all
      (fun bytes => (Sequential.decodeAt (entry bytes)).isOk = false) = true := by rfl

theorem same_constructor_encodings :
    ([.movzxMem8 .rcx (.indexed .rdi .rax 0) false,
      .movzxMem8 .r8 (.indexed .rsi .rcx 0) true, .movzxMem8 .r8 (.indexed .r14 .r12 2) true,
      .movzxReg8 .rax .rcx false, .movzxReg8 .rax .rsp true,
      .cmpReg8 .rcx .r8 true, .cmpReg8 .rax .rdx false,
      .subReg32 .rax .r8 true, .subReg32 .rax .rax false] : List Sequential.Instruction).map
      Literals.byteOrderEncoding =
    [some [0x0f,0xb6,0x0c,7], some [0x44,0x0f,0xb6,4,0x0e], some [0x47,0x0f,0xb6,4,0xa6],
     some [0x0f,0xb6,0xc1], some [0x40,0x0f,0xb6,0xc4], some [0x44,0x38,0xc1],
     some [0x38,0xd0], some [0x44,0x29,0xc0], some [0x29,0xc0]] ∧
    ([.movzxReg8 .rax .rsp false, .movzxReg8 .r8 .rax false,
      .cmpReg8 .rsp .rax false, .cmpReg8 .rax .r8 false, .subReg32 .rax .r8 false,
      .movzxMem8 .rax (.base .rbp) false, .movzxMem8 .rax (.base .r12) true,
      .movzxMem8 .rax (.indexed .rdi .rsp 0) true,
      .movzxMem8 .rax (.indexed .r13 .rcx 0) true] : List Sequential.Instruction).map
      Literals.byteOrderEncoding = List.replicate 9 none := by exact ⟨rfl,rfl⟩

/-- Entire exact manifest/ELF slices, including unreachable padding. These
diagnostics establish CFG admission only, with no function-correctness credit. -/
def gccBytes : List Byte :=
  [0xf3,0x0f,0x1e,0xfa,0x48,0x85,0xd2,0x74,0x27,0x31,0xc0,0xeb,0x0c,0x0f,0x1f,0,
   0x48,0x83,0xc0,1,0x48,0x39,0xc2,0x74,0x17,0x0f,0xb6,0x0c,7,0x44,0x0f,0xb6,4,6,
   0x44,0x38,0xc1,0x74,0xe9,0x0f,0xb6,0xc1,0x44,0x29,0xc0,0xc3,0x66,0x90,0x31,0xc0,0xc3]

def clangBytes : List Byte :=
  [0x48,0x85,0xd2,0x74,0x21,0x31,0xc9,0x66,0x0f,0x1f,0x84,0,0,0,0,0,
   0x0f,0xb6,4,0x0f,0x44,0x0f,0xb6,4,0x0e,0x44,0x38,0xc0,0x75,0x0b,
   0x48,0xff,0xc1,0x48,0x39,0xca,0x75,0xea,0x31,0xc0,0xc3,0x44,0x29,0xc0,0xc3]

theorem frozen_cfg_acceptance :
    [gccBytes,clangBytes].map (fun bytes => (CFG.analyze bytes).map (fun graph =>
      (bytes.length, graph.nodes.map (·.offset), CFG.check bytes graph))) =
    [.ok (51,[0,4,7,9,11,13,16,20,23,25,29,34,37,39,42,45,46,48,50],true),
     .ok (45,[0,3,5,7,16,20,25,28,30,33,36,38,40,41,44],true)] := by rfl

private def guardInput (bytes : List Byte) : State :=
  entry bytes (fun register => match register with
    | .rdx => 0 | .rsp => 8192 | _ => 0x800000000000)
    (fun address => if 8192 ≤ address.toNat then
      ([0,0,2,0,0,0,0,0] : List Byte)[address.toNat - 8192]? else none)

/-- Concrete production executions of the frozen zero-length paths. Neither
input pointer is canonical or mapped; the sole operand access is actual RET's
stack read. This is a guard regression, not a universal memcmp certificate. -/
theorem zero_length_guard (af : Bool) :
    [gccBytes,clangBytes].map (fun bytes =>
      (Sequential.run (fun _ => af) 5 (guardInput bytes)).map (fun result =>
        (result.state.registers .rax, result.state.registers .rsp, result.state.rip,
          result.instructions, result.reads))) =
    [.ok (0,8200,0x20000,5,[⟨.stack,8192,8⟩]),
     .ok (0,8200,0x20000,4,[⟨.stack,8192,8⟩])] := by cases af <;> rfl

/-- Even unreachable padding and exact instruction lengths stay authenticated.
Branches into SIB/ModRM bytes, unmodeled suffixes and oversized graphs reject. -/
theorem cfg_rejects_changed_padding_and_edges :
    (CFG.analyze (gccBytes.set 47 0x91)).isOk = false ∧
    (CFG.analyze (gccBytes.set 12 13)).isOk = false ∧
    (CFG.analyze (gccBytes ++ [0x0f])).isOk = false ∧
    (CFG.analyze (List.replicate 33 0x90 ++ [0xc3])).isOk = false ∧
    (CFG.analyze (List.replicate 65 0x90)).isOk = false := by
  exact ⟨by decide, by decide, by decide, by decide +kernel, by decide⟩

end EDSL.Tests.SequentialByteOrderISA

#audit_edsl
