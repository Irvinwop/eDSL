/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.ParityISA
import EDSL.X86.Sequential.CFGDiscovery
import EDSL.X86.Sequential.Return
import EDSL.X86.Sequential.Literals
import EDSL.X86.CallReturn.DecodeTransport
import EDSL.X86.VCGen.Core
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.SequentialParityISA
open X86 X86.Sequential

private def entry (code : List Byte) (registers : Register → Word := fun _ => 0)
    (flags : Word := 0xed7) : State where
  registers := registers
  rip := 4096
  flags := flags
  memory := {
    read := fun address => code[(address - 4096).toNat]?
    executable := fun address => decide ((address - 4096).toNat < code.length)
    writable := fun address => address.getLsbD 7 }

private def nextView {α : Type} (af : Bool) (state : State)
    (view : State → List Read → α) : Except Error α := do
  let observation ← Sequential.step af state
  match observation.result with
  | .next final => return view final observation.reads
  | _ => throw .unexpectedReturn

private def banks : Register → Word
  | .rax => 0x10000000f | .rbx => 0x2000000cc
  | .r8 => 0x4000000aa | .r11 => 0x800000055
  | _ => 0xfeedface12345678

/-- Literal outputs distinguish R/B, ignored X, operand direction and width.
The source's entire high half must survive while the destination is cleared. -/
theorem xor_banks_and_directions (af : Bool) :
    ([0x40,0x41,0x42,0x43,0x44,0x45,0x46,0x47] : List Byte).map
      (fun rex => (nextView af (entry [rex,0x31,0xd8] banks)
          (fun s reads => (s.registers .rax,s.registers .rbx,s.registers .r8,s.registers .r11,s.rip,reads)),
        nextView af (entry [rex,0x33,0xd8] banks)
          (fun s reads => (s.registers .rax,s.registers .rbx,s.registers .r8,s.registers .r11,s.rip,reads)))) =
    [(.ok (0xc3,0x2000000cc,0x4000000aa,0x800000055,4099,[]),
       .ok (0x10000000f,0xc3,0x4000000aa,0x800000055,4099,[])),
     (.ok (0x10000000f,0x2000000cc,0x66,0x800000055,4099,[]),
       .ok (0x10000000f,0x66,0x4000000aa,0x800000055,4099,[])),
     (.ok (0xc3,0x2000000cc,0x4000000aa,0x800000055,4099,[]),
       .ok (0x10000000f,0xc3,0x4000000aa,0x800000055,4099,[])),
     (.ok (0x10000000f,0x2000000cc,0x66,0x800000055,4099,[]),
       .ok (0x10000000f,0x66,0x4000000aa,0x800000055,4099,[])),
     (.ok (0x5a,0x2000000cc,0x4000000aa,0x800000055,4099,[]),
       .ok (0x10000000f,0x2000000cc,0x4000000aa,0x5a,4099,[])),
     (.ok (0x10000000f,0x2000000cc,0xff,0x800000055,4099,[]),
       .ok (0x10000000f,0x2000000cc,0x4000000aa,0xff,4099,[])),
     (.ok (0x5a,0x2000000cc,0x4000000aa,0x800000055,4099,[]),
       .ok (0x10000000f,0x2000000cc,0x4000000aa,0x5a,4099,[])),
     (.ok (0x10000000f,0x2000000cc,0xff,0x800000055,4099,[]),
       .ok (0x10000000f,0x2000000cc,0x4000000aa,0xff,4099,[]))] := by rfl

/-- All sixteen self aliases include RSP and both banks. A post-write source
read would incorrectly leave each old low32 value instead of producing zero. -/
theorem xor_self_aliases (af : Bool) :
    ([(0x40,0xc0,.rax),(0x40,0xc9,.rcx),(0x40,0xd2,.rdx),(0x40,0xdb,.rbx),
      (0x40,0xe4,.rsp),(0x40,0xed,.rbp),(0x40,0xf6,.rsi),(0x40,0xff,.rdi),
      (0x45,0xc0,.r8),(0x45,0xc9,.r9),(0x45,0xd2,.r10),(0x45,0xdb,.r11),
      (0x45,0xe4,.r12),(0x45,0xed,.r13),(0x45,0xf6,.r14),(0x45,0xff,.r15)] :
      List (Byte × Byte × Register)).map (fun (rex,modrm,destination) =>
        nextView af (entry [rex,0x33,modrm] (fun _ => 0xdeadbeef800000ff))
          (fun s reads => (s.registers destination,s.flags &&& ~~~(0x10 : Word),
            s.flags.getLsbD 4,s.rip,reads))) =
    List.replicate 16 (.ok (0,0x646,af,4099,[])) := by cases af <;> rfl

theorem xor_low32_flags (af : Bool) :
    ([(0x800000ff,0xf,0x800000f0,0x686), (0x100000000,0,0,0x646),
      (0x1234567800000000,0x8765432100000100,0x100,0x606),
      (0xffffffff,0x7fffffff,0x80000000,0x686), (1,3,2,0x602)] :
      List (Word × Word × Word × Word)).all (fun (left,right,result,flags) =>
        (nextView af (entry [0x31,0xd0]
          (fun r => if r = .rax then left else if r = .rdx then right else 9))
          (fun s reads => (s.registers .rax == result &&
            s.flags &&& ~~~(0x10 : Word) == flags && s.flags.getLsbD 4 == af &&
            s.rip == 4098 && reads == []))).toOption == some true) = true := by
  cases af <;> decide +kernel

/-- Signed immediates 80/FF must retain bits 8..31; the full destination
still clears bits 32..63. Literal flags include parity and sign at width32. -/
theorem and_signed_immediate (af : Bool) :
    ([(0x01,0xffff000080000003,1,0x602), (0x80,0xffff0000800000ff,0x80000080,0x682),
      (0xff,0xffff000080000003,0x80000003,0x686), (0,0xffffffffffffffff,0,0x646),
      (0x7f,0xffff0000800000ff,0x7f,0x602)] :
      List (Byte × Word × Word × Word)).all (fun (imm,input,result,flags) =>
        (nextView af (entry [0x83,0xe2,imm] (fun _ => input))
          (fun s reads => s.registers .rdx == result &&
            s.flags &&& ~~~(0x10 : Word) == flags && s.flags.getLsbD 4 == af &&
            s.rip == 4099 && reads == [])).toOption == some true) = true := by
  cases af <;> decide +kernel

theorem and_extended_rsp_bank (af : Bool) :
    nextView af (entry [0x41,0x83,0xe4,0x80] (fun _ => 0xfeedface800000ff))
      (fun s reads => (s.registers .r12,s.registers .rsp,s.rip,reads)) =
    .ok (0x80000080,0xfeedface800000ff,4100,[]) := by rfl

private def lowGroupForms : List (Byte × Byte × Register) :=
  [(0xe0,0xf8,.rax),(0xe1,0xf9,.rcx),(0xe2,0xfa,.rdx),(0xe3,0xfb,.rbx),
   (0xe4,0xfc,.rsp),(0xe5,0xfd,.rbp),(0xe6,0xfe,.rsi),(0xe7,0xff,.rdi)]

private def highGroupForms : List (Byte × Byte × Register) :=
  [(0xe0,0xf8,.r8),(0xe1,0xf9,.r9),(0xe2,0xfa,.r10),(0xe3,0xfb,.r11),
   (0xe4,0xfc,.r12),(0xe5,0xfd,.r13),(0xe6,0xfe,.r14),(0xe7,0xff,.r15)]

theorem group_register_banks :
    lowGroupForms.all (fun (andByte,cmpByte,reg) =>
      (Sequential.decodeAt (entry [0x83,andByte,0x80])).toOption ==
        some (.logicalImm32 .band reg 0x80 false) &&
      (Sequential.decodeAt (entry [0x40,0x83,andByte,0xff])).toOption ==
        some (.logicalImm32 .band reg 0xff true) &&
      (Sequential.decodeAt (entry [0x48,0x83,cmpByte,0x80])).toOption == some (.cmpImm64 reg 0x80)) = true ∧
    highGroupForms.all (fun (andByte,cmpByte,reg) =>
      (Sequential.decodeAt (entry [0x41,0x83,andByte,0xff])).toOption ==
        some (.logicalImm32 .band reg 0xff true) &&
      (Sequential.decodeAt (entry [0x49,0x83,cmpByte,0x80])).toOption == some (.cmpImm64 reg 0x80)) = true := by
  exact ⟨by decide +kernel, by decide +kernel⟩

/-- CMP's literal status words distinguish operand order, sign extension,
CF, AF, overflow, high halves and equality. The AF input has no effect. -/
theorem cmp_signed_immediate_flags (af : Bool) :
    ([(0,1,0x697), (1,1,0x646), (2,1,0x602), (0x100000000,1,0x616),
      (0,0xff,0x613), (0xffffffffffffffff,0xff,0x646),
      (0x8000000000000000,1,0xe16), (0x7fffffffffffffff,0xff,0xe87),
      (0xffffffffffffff80,0x80,0x646), (0,0x80,0x603)] :
      List (Word × Byte × Word)).all (fun (input,imm,flags) =>
        (nextView af (entry [0x49,0x83,0xfc,imm] (fun _ => input))
          (fun s reads => s.registers .r12 == input && s.registers .rsp == input &&
            s.flags == flags && s.rip == 4100 && reads == [])).toOption == some true) = true := by
  cases af <;> decide +kernel

theorem old_self_xor_api (af : Bool) :
    (Sequential.decodeAt (entry [0x31,0xc0]),
      nextView af (entry [0x31,0xc0] (fun _ => 0x80000001000000ff))
        (fun s reads => (s.registers .rax,s.rip,reads))) =
    (.ok (.xorSelf32 .rax),.ok (0,4098,[])) := by rfl

theorem lifted_decoder_and_typed_rendering :
    (CallReturn.decodeAt (entry [0x31,0xd0]),
      CallReturn.decodeAt (entry [0x83,0xe2,1]),
      CallReturn.decodeAt (entry [0x48,0x83,0xff,1]),
      CallReturn.decodeAt (entry [0x66,0x0f,0x1f,0x44,0,0]),
      Literals.instruction (.logicalReg32 .bxor .rax .rdx false),
      Literals.instruction (.logicalImm32 .band .rdx 0x80 false),
      Literals.instruction (.cmpImm64 .r15 0xff), Literals.instruction (.nop .six)) =
    (.ok (.sequential (.logicalReg32 .bxor .rax .rdx false)),
      .ok (.sequential (.logicalImm32 .band .rdx 1 false)),
      .ok (.sequential (.cmpImm64 .rdi 1)), .ok (.sequential (.nop .six)),
      "(.logicalReg32 .bxor .rax .rdx false)","(.logicalImm32 .band .rdx 128 false)",
      "(.cmpImm64 .r15 255)","(.nop .six)") := by rfl

private def rejects (bytes : List Byte) : Bool :=
  match Sequential.decodeAt (entry bytes) with
  | .error .unsupportedEncoding => true
  | _ => false

/-- Wrong width, selector, operand mode or prefix never gains a weaker
register interpretation. Imm32 and accumulator-special forms stay unsupported. -/
theorem unsupported_forms :
    ([[0x31,0x10],[0x33,0x10],[0x47,0x31,0x50,0],
      [0x66,0x31,0xd0],[0x40,0x40,0x31,0xd0],[0xf0,0x31,0xd0],
      [0x83,0x22,1],[0x83,0xd0,1],[0x83,0xc8,1],[0x83,0xf0,1],
      [0x42,0x83,0xe0,1],[0x44,0x83,0xe0,1],[0x48,0x83,0xe0,1],
      [0x41,0x81,0xe0,1,0,0,0],[0x40,0x25,1,0,0,0],
      [0x48,0x83,0x3f,1],[0x49,0x83,0x7c,0,1],
      [0x4a,0x83,0xff,1],[0x4c,0x83,0xff,1],
      [0x48,0x81,0xff,1,0,0,0],[0x48,0x3d,1,0,0,0],
      [0x66,0x0f,0x1f,0x44,1,0],[0x66,0x0f,0x1f,0x44,0,1],
      [0x66,0x0f,0x1f,0x4c,0,0],[0x66,0x66,0x0f,0x1f,0x44,0,0]] :
      List (List Byte)).all rejects = true := by decide +kernel

private def faultAt (bytes : List Byte) (offset : Nat) : Bool :=
  match Sequential.decodeAt (entry bytes) with
  | .error (.inaccessibleInstruction address) => address == 4096 + BitVec.ofNat 64 offset
  | _ => false

/-- Every required suffix byte must be executable. No fetch past a complete
instruction is required, and a missing suffix cannot become an unsupported error. -/
theorem exact_fetch_boundaries :
    ([([0x31],1),([0x33],1),([0x47,0x31],2),
      ([0x83,0xe2],2),([0x41,0x83,0xe4],3),([0x48,0x83,0xff],3),
      ([0x49,0x83,0xfc],3),([0x66],1),([0x66,0x0f],2),
      ([0x66,0x0f,0x1f],3),([0x66,0x0f,0x1f,0x44],4),
      ([0x66,0x0f,0x1f,0x44,0],5)] : List (List Byte × Nat)).all
      (fun (bytes,offset) => faultAt bytes offset) = true := by decide +kernel

theorem readable_nonexecutable_suffix :
    (Sequential.decodeAt { entry [0x48,0x83,0xff,1] with memory := {
      (entry [0x48,0x83,0xff,1]).memory with
        executable := fun address => decide (address ≠ 4099) } }).map (fun _ => ()) =
      .error (.inaccessibleInstruction 4099) ∧
    (Sequential.decodeAt { entry [0x66,0x0f,0x1f,0x44,0,0] with memory := {
      (entry [0x66,0x0f,0x1f,0x44,0,0]).memory with
        executable := fun address => decide (address ≠ 4101) } }).map (fun _ => ()) =
      .error (.inaccessibleInstruction 4101) := by exact ⟨rfl,rfl⟩

/-- No premise restricts the apparent NOP address: it may be noncanonical
and unmapped. Complete equality includes flags and all permission functions. -/
theorem nop6_complete_frame (registers : Register → Word) (flags : Word) (af : Bool) :
    let initial := entry [0x66,0x0f,0x1f,0x44,0,0] registers flags
    ∃ final, Sequential.step af initial = .ok ⟨.next final, []⟩ ∧
      final = { initial with rip := 4102 } := by
  dsimp only
  refine ⟨_, ?_, rfl⟩
  have decoded : Sequential.decodeAt
      (entry [0x66,0x0f,0x1f,0x44,0,0] registers flags) = .ok (.nop .six) :=
    decodeAt_transport (source := entry [0x66,0x0f,0x1f,0x44,0,0])
      (fun _ _ _ fetched => fetched) (by rfl)
  rw [step_eq_execute af decoded]
  rfl

private def vcBytes : List Byte := [0x83,0xe2,0x80,0xc3]

private def vcGraph : CFG.Graph :=
  ⟨[⟨0,.logicalImm32 .band .rdx 0x80 false,true,2⟩,
    ⟨3,.legacy .ret,false,1⟩],2⟩

private def vcEntry : vcGraph.Index := ⟨0,by decide⟩

private def vcInitial : State :=
  let initial := entry vcBytes
    (fun register => if register = .rsp then 8192 else 0xfeedface800000ff) 0xec7
  { initial with
    memory := { initial.memory with
      read := fun address =>
        if address = 8193 then some 0x30
        else if 8192 ≤ address.toNat ∧ address.toNat < 8200 then some 0
        else initial.memory.read address } }

private def vcPermit (_ : State) (read : Read) : Prop := read = ⟨.stack,8192,8⟩

private instance (post : X86.VCGen.Contract) [DecidablePred post] :
    Decidable (X86.VCGen.wp vcGraph 4096 vcPermit 2 vcEntry vcInitial post) :=
  X86.VCGen.decidableWP vcGraph 4096 vcPermit
    (fun _ read => inferInstanceAs (Decidable (read = ⟨.stack,8192,8⟩)))
    2 vcEntry vcInitial post (fun _ => inferInstance)

/-- The generic VCG checks real bytes, real RET, the independent caller loan,
low32 clearing, count and exact trace. The read policy permits only the return
stack slot, independently of which bytes are readable in memory. -/
theorem generic_vcg_signed_and :
    X86.VCGen.certify vcBytes vcGraph 4096 vcPermit 2 vcEntry vcInitial
      (fun result => result.state.registers .rdx = 0x80000080 ∧
        result.state.registers .rax = 0xfeedface800000ff ∧
        result.state.registers .rsp = 8200 ∧ result.state.rip = 12288 ∧
        result.instructions = 2 ∧ result.reads = [⟨.stack,8192,8⟩]) = true := by
  decide +kernel

/-- An all-choice VC cannot promise AF=false after AND. This catches a VCG
which checks only its convenient AF branch or treats the flag as preserved. -/
theorem generic_vcg_rejects_fixed_af :
    X86.VCGen.certify vcBytes vcGraph 4096 vcPermit 2 vcEntry vcInitial
      (fun result => result.state.flags.getLsbD 4 = false) = false := by
  decide +kernel

/-- A same-length immediate mutation keeps the graph shape but must lose its
certificate. The graph cannot supply its original operand instead of the byte. -/
theorem generic_vcg_rejects_changed_immediate :
    X86.VCGen.certify (vcBytes.set 2 0x7f) vcGraph 4096 vcPermit 2 vcEntry vcInitial
      (fun _ => True) = false := by
  decide +kernel

/-- These literal windows are the unchanged final ELF row12 symbols. The
scoped runner checks them against manifests and actual ELF file offsets. -/
def gccBytes : List Byte :=
  [0xf3,0x0f,0x1e,0xfa,0x31,0xc0,0x48,0x85,0xff,0x74,0x15,0x0f,0x1f,0x44,0,0,
   0x89,0xfa,0x83,0xe2,1,0x31,0xd0,0x48,0xd1,0xef,0x75,0xf4,0xc3,0x0f,0x1f,0,0xc3]

def clangBytes : List Byte :=
  [0x31,0xc0,0x48,0x85,0xff,0x74,0x1c,0x48,0x89,0xf9,0x66,0x0f,0x1f,0x44,0,0,
   0x89,0xfa,0x83,0xe2,1,0x31,0xd0,0x48,0xd1,0xe9,0x48,0x83,0xff,1,
   0x48,0x89,0xcf,0x77,0xed,0xc3]

theorem gcc_cfg_admission :
    (CFG.analyze gccBytes).map (fun graph => graph.nodes.map
      (fun node => (node.offset,node.instruction,node.instruction.length,node.successors))) =
    .ok [(0,.endbr64IbtDisabled,4,[4]),(4,.xorSelf32 .rax,2,[6]),
      (6,.test64 .rdi .rdi,3,[9]),(9,.je 0x15,2,[11,32]),(11,.nop .five,5,[16]),
      (16,.movReg32 .rdx .rdi,2,[18]),(18,.logicalImm32 .band .rdx 1 false,3,[21]),
      (21,.logicalReg32 .bxor .rax .rdx false,2,[23]),(23,.shrOne64 .rdi,3,[26]),
      (26,.legacy (.jnz 0xf4),2,[28,16]),(28,.legacy .ret,1,[]),
      (29,.nop .three,3,[32]),(32,.legacy .ret,1,[])] := by rfl

theorem clang_cfg_admission :
    (CFG.analyze clangBytes).map (fun graph => graph.nodes.map
      (fun node => (node.offset,node.instruction,node.instruction.length,node.successors))) =
    .ok [(0,.xorSelf32 .rax,2,[2]),(2,.test64 .rdi .rdi,3,[5]),(5,.je 0x1c,2,[7,35]),
      (7,.movReg64 .rcx .rdi,3,[10]),(10,.nop .six,6,[16]),
      (16,.movReg32 .rdx .rdi,2,[18]),(18,.logicalImm32 .band .rdx 1 false,3,[21]),
      (21,.logicalReg32 .bxor .rax .rdx false,2,[23]),(23,.shrOne64 .rcx,3,[26]),
      (26,.cmpImm64 .rdi 1,4,[30]),(30,.movReg64 .rdi .rcx,3,[33]),
      (33,.jcc .above 0xed,2,[35,16]),(35,.legacy .ret,1,[])] := by rfl

end EDSL.Tests.SequentialParityISA

#print axioms EDSL.Tests.SequentialParityISA.xor_banks_and_directions
#print axioms EDSL.Tests.SequentialParityISA.cmp_signed_immediate_flags
#print axioms EDSL.Tests.SequentialParityISA.generic_vcg_signed_and
#print axioms EDSL.Tests.SequentialParityISA.generic_vcg_rejects_fixed_af
#print axioms EDSL.Tests.SequentialParityISA.gcc_cfg_admission
#print axioms EDSL.Tests.SequentialParityISA.clang_cfg_admission
#audit_edsl
