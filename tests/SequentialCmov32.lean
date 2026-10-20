/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.Core
import EDSL.X86.Sequential.ConditionFlags
import EDSL.X86.Sequential.Literals
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.SequentialCmov32
open X86

private def entry (code : List Byte) (registers : Register → Word := fun _ => 0)
    (flags : Word := 0x202) : State where
  registers := registers
  flags := flags
  rip := 4096
  memory := {
    read := fun address => if 4096 ≤ address.toNat ∧ address.toNat < 4096 + code.length
      then code[address.toNat - 4096]? else none
    executable := fun address =>
      decide (4096 ≤ address.toNat ∧ address.toNat < 4096 + code.length) }

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

/-- Independent architecture vectors detect retaining the high half on false
or transferring full64 on true. Both AF choices yield the same result. -/
theorem false_and_true_zero_extend (af : Bool) :
    ([0x202,0x242] : List Word).map (fun flags =>
      nextView af (entry [0x0f,0x44,0xc7] registers flags)
        (fun final reads => (final.registers .rax,final.registers .rdi,final.flags,final.rip,reads))) =
    [.ok (0x12345678,0x8765432100000001,0x202,4099,[]),
      .ok (1,0x8765432100000001,0x242,4099,[])] := by rfl

/-- R/B have different roles, X has none; self-aliases still zero upper bits,
and an RSP destination has no special exemption on a false condition. -/
theorem rex_banks_alias_rsp (af : Bool) :
    ([([0x40,0x0f,0x44,0xc1],.rax),([0x41,0x0f,0x44,0xc1],.rax),
      ([0x42,0x0f,0x44,0xc1],.rax),([0x43,0x0f,0x44,0xc1],.rax),
      ([0x44,0x0f,0x44,0xc1],.r8),([0x45,0x0f,0x44,0xc1],.r8),
      ([0x46,0x0f,0x44,0xc1],.r8),([0x47,0x0f,0x44,0xc1],.r8),
      ([0x47,0x0f,0x44,0xe4],.r12),([0x0f,0x44,0xe7],.rsp)] :
      List (List Byte × Register)).map (fun (bytes,destination) =>
        nextView af (entry bytes registers 0x242)
          (fun final reads => (final.registers destination,final.flags,final.rip,reads))) =
    [.ok (0x33334444,0x242,4100,[]),.ok (0x44332211,0x242,4100,[]),
      .ok (0x33334444,0x242,4100,[]),.ok (0x44332211,0x242,4100,[]),
      .ok (0x33334444,0x242,4100,[]),.ok (0x44332211,0x242,4100,[]),
      .ok (0x33334444,0x242,4100,[]),.ok (0x44332211,0x242,4100,[]),
      .ok (0x87654321,0x242,4100,[]),.ok (1,0x242,4099,[])] := by rfl

theorem false_alias_and_rsp (af : Bool) :
    (nextView af (entry [0x47,0x0f,0x44,0xe4] registers)
      (fun final _ => final.registers .r12),
     nextView af (entry [0x0f,0x44,0xe7] registers)
      (fun final _ => final.registers .rsp)) =
    (.ok 0x87654321,.ok 0xfffffff0) := by rfl

/-- The opcodes specify the architectural condition order, independently of
Condition.ofNibble's implementation or the executable condition predicates. -/
theorem sixteen_conditions_decode :
    ([0x40,0x41,0x42,0x43,0x44,0x45,0x46,0x47,
      0x48,0x49,0x4a,0x4b,0x4c,0x4d,0x4e,0x4f] : List Byte).map
      (fun opcode => Sequential.decodeAt (entry [0x0f,opcode,0xc7])) =
    [.ok (.cmovReg32 .overflow .rax .rdi false),
      .ok (.cmovReg32 .notOverflow .rax .rdi false),
      .ok (.cmovReg32 .below .rax .rdi false),
      .ok (.cmovReg32 .aboveEqual .rax .rdi false),
      .ok (.cmovReg32 .equal .rax .rdi false),
      .ok (.cmovReg32 .notEqual .rax .rdi false),
      .ok (.cmovReg32 .belowEqual .rax .rdi false),
      .ok (.cmovReg32 .above .rax .rdi false),
      .ok (.cmovReg32 .sign .rax .rdi false),
      .ok (.cmovReg32 .notSign .rax .rdi false),
      .ok (.cmovReg32 .parity .rax .rdi false),
      .ok (.cmovReg32 .notParity .rax .rdi false),
      .ok (.cmovReg32 .less .rax .rdi false),
      .ok (.cmovReg32 .greaterEqual .rax .rdi false),
      .ok (.cmovReg32 .lessEqual .rax .rdi false),
      .ok (.cmovReg32 .greater .rax .rdi false)] := by rfl

/-- Signed overflow and unsigned borrow must differ at the 32-bit boundary. -/
theorem signed_and_unsigned_boundary :
    (Sequential.Condition.holds .less (Sequential.cmpFlags32 0x202 0x80000000 1),
      Sequential.Condition.holds .below (Sequential.cmpFlags32 0x202 0x80000000 1),
      Sequential.Condition.holds .greater (Sequential.cmpFlags32 0x202 0x7fffffff 0xffffffff),
      Sequential.Condition.holds .below (Sequential.cmpFlags32 0x202 0x7fffffff 0xffffffff)) =
    (true,false,true,true) := by rfl

/-- No memory CMOV, operand16, address override, repetition or inner prefix
may fall through to a weaker supported operation. -/
theorem unsupported_forms :
    ([[0x0f,0x44,0x07],[0x47,0x0f,0x44,0x44],[0x0f,0x44,0x87],
      [0x40,0x40,0x0f,0x44,0xc7],[0x40,0x66,0x0f,0x44,0xc7],
      [0x0f,0x3f,0xc7],[0x0f,0x50,0xc7],
      [0x66,0x0f,0x44,0xc7],[0x67,0x0f,0x44,0xc7]] : List (List Byte)).map
      (fun bytes => Sequential.decodeAt (entry bytes)) =
    [.error .unsupportedEncoding,.error .unsupportedEncoding,.error .unsupportedEncoding,
      .error .unsupportedEncoding,.error .unsupportedEncoding,.error .unsupportedEncoding,
      .error .unsupportedEncoding,.error .unsupportedEncoding,
      .error (.unsupportedOpcode 0x67)] := by rfl

theorem final_modrm_fetch_required (af : Bool) :
    ((Sequential.step af (entry [0x0f,0x44])).map (fun _ => ()),
     (Sequential.step af (entry [0x47,0x0f,0x44])).map (fun _ => ()),
     (Sequential.step af { entry [0x47,0x0f,0x44,0xc7] with
       memory := { (entry [0x47,0x0f,0x44,0xc7]).memory with
         executable := fun address => decide (address ≠ 4099) } }).map (fun _ => ())) =
    (.error (.inaccessibleInstruction 4098),.error (.inaccessibleInstruction 4099),
      .error (.inaccessibleInstruction 4099)) := by rfl

theorem cfg_admission :
    (Sequential.CFG.analyze [0x39,0xf7,0x89,0xf0,0x0f,0x43,0xc7,0xc3]).map
      (fun graph => graph.nodes.map (fun node =>
        (node.offset,node.instruction,node.instruction.length))) =
    .ok [(0,.cmp32 .rdi .rsi false,2),(2,.legacy .movEaxEsi,2),
      (4,.cmovReg32 .aboveEqual .rax .rdi false,3),(7,.legacy .ret,1)] := by rfl

private def graph : Sequential.CFG.Graph :=
  ⟨[⟨0,.cmovReg32 .equal .rax .rdi false,true,2⟩,⟨3,.legacy .ret,false,1⟩],2⟩

/-- Check the exact bytes. Mutating the condition or claiming REX length for
an unprefixed instruction cannot preserve the same graph certificate. -/
example : Sequential.CFG.check [0x0f,0x44,0xc7,0xc3] graph = true := by decide
example : Sequential.CFG.check [0x0f,0x45,0xc7,0xc3] graph = false := by decide
example : Sequential.CFG.check [0x40,0x0f,0x44,0xc7,0xc3] graph = false := by decide

/-- The shared VCG composes CMOV32 with actual RET. Its independent arithmetic
postcondition requests truncation modulo 2^32 and the exact two retired
instructions; it does not restate the instruction transition. -/
theorem generated_false_zero_extension (initial : State) (target : Word)
    (untaken : initial.flags.getLsbD 6 = false)
    (stack : readWord initial.memory (initial.registers .rsp) = .ok target)
    (targetCanonical : canonical target = true) :
    X86.VCGen.wp graph initial.rip (fun _ _ => True) 2 ⟨0,by decide⟩ initial
      (fun result => (result.state.registers .rax).toNat =
        (initial.registers .rax).toNat % 2^32 ∧ result.instructions = 2) := by
  rw [X86.VCGen.wp]
  intro af
  simp only [graph,Sequential.CFG.Graph.node,List.getElem_cons_zero,
    Sequential.execute,Sequential.Instruction.operandReads,
    Sequential.Instruction.length,Sequential.Condition.holds,untaken,
    Bool.false_eq_true,↓reduceIte,pure_ok]
  refine ⟨by simp,⟨1,by decide⟩,?_,?_⟩
  · rfl
  · rw [X86.VCGen.wp]
    intro afRet
    simp [Sequential.CFG.Graph.node,Sequential.execute,
      Sequential.Instruction.operandReads,X86.executeInstruction,executeRet,
      State.writeRegister,stack,targetCanonical,Sequential.Result.prepend,
      BitVec.toNat_setWidth]
    have bound : (initial.registers .rax).toNat % 2^32 < 2^64 :=
      Nat.lt_trans (Nat.mod_lt _ (by decide : 0 < 2^32))
        (by decide : 2^32 < 2^64)
    exact bound

end EDSL.Tests.SequentialCmov32

#audit_edsl
