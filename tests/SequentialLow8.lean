/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Low8
import EDSL.X86.Sequential.Literals
import EDSL.X86.CallReturn.DecodeTransport
import EDSL.X86.VCGen.Frame

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.SequentialLow8
open X86 X86.Sequential

private def registers : Register → Word
  | .rax => 0x11223344556677fe | .rcx => 0x21324354657687fd
  | .rdx => 0x31425364758697fc | .rbx => 0x415263748596a7fb
  | .rsp => 0x2000 | .rbp => 0x61728394a5b6c7f9
  | .rsi => 0x718293a4b5c6d7f8 | .rdi => 0x8192a3b4c5d6e7f7
  | .r8 => 0x91a2b3c4d5e6f7f6 | .r9 => 0xa1b2c3d4e5f607f5
  | .r10 => 0xb1c2d3e4f50617f4 | .r11 => 0xc1d2e3f4051627f3
  | .r12 => 0xd1e2f304152637f2 | .r13 => 0xe1f20314253647f1
  | .r14 => 0xf1021324354657f0 | .r15 => 0x0123456789abcdef

/-- Finite executable code, a separate read-only caller word, writable DATA,
and an inaccessible hole. Permission functions deliberately differ. -/
private def entry (bytes : List Byte) (flags : Word := 0xdeadbeef00000612)
    (input : Register → Word := registers) : State where
  registers := input
  rip := 4096
  flags := flags
  memory := {
    read := fun address =>
      if 4096 ≤ address.toNat ∧ address.toNat < 4096 + bytes.length then
        bytes[address.toNat - 4096]?
      else if address = 8193 then some 0x30
      else if 8192 ≤ address.toNat ∧ address.toNat < 8200 then some 0
      else if address = 0x4000 then some 0xa5
      else none
    executable := fun address => decide (4096 ≤ address.toNat ∧ address.toNat < 4096 + bytes.length)
    writable := fun address => decide (address = 0x4000) }

private def nextView {α : Type} (af : Bool) (before : State)
    (view : State → List Read → α) : Except Error α := do
  let observation ← Sequential.step af before
  match observation.result with
  | .next after => return view after observation.reads
  | _ => throw .unexpectedReturn

private def view (destination : Register) (af : Bool) (before : State) :=
  nextView af before (fun after reads => (after.registers destination, after.flags, after.rip, reads))

/-- Each row independently names an architectural condition and literal flag
words that make it true/false. SF and OF agree in several signed cases. -/
private def conditions : List (Byte × Condition × Word × Word) :=
  [(0x90,.overflow,0xdeadbeef00000e12,0xdeadbeef00000612),
   (0x91,.notOverflow,0xdeadbeef00000612,0xdeadbeef00000e12),
   (0x92,.below,0xdeadbeef00000613,0xdeadbeef00000612),
   (0x93,.aboveEqual,0xdeadbeef00000612,0xdeadbeef00000613),
   (0x94,.equal,0xdeadbeef00000652,0xdeadbeef00000612),
   (0x95,.notEqual,0xdeadbeef00000612,0xdeadbeef00000652),
   (0x96,.belowEqual,0xdeadbeef00000653,0xdeadbeef00000612),
   (0x97,.above,0xdeadbeef00000612,0xdeadbeef00000652),
   (0x98,.sign,0xdeadbeef00000692,0xdeadbeef00000612),
   (0x99,.notSign,0xdeadbeef00000612,0xdeadbeef00000692),
   (0x9a,.parity,0xdeadbeef00000616,0xdeadbeef00000612),
   (0x9b,.notParity,0xdeadbeef00000612,0xdeadbeef00000616),
   (0x9c,.less,0xdeadbeef00000692,0xdeadbeef00000e92),
   (0x9d,.greaterEqual,0xdeadbeef00000e92,0xdeadbeef00000e12),
   (0x9e,.lessEqual,0xdeadbeef00000e12,0xdeadbeef00000e92),
   (0x9f,.greater,0xdeadbeef00000e92,0xdeadbeef00000ed2)]

theorem all_conditions (af : Bool) :
    conditions.all (fun (opcode,condition,trueFlags,falseFlags) =>
      (Sequential.decodeAt (entry [0x0f,opcode,0xc0])).toOption ==
        some (.setcc condition .rax false) &&
      (view .rax af (entry [0x0f,opcode,0xc0] trueFlags)).toOption ==
        some (0x1122334455667701,trueFlags,4099,[]) &&
      (view .rax af (entry [0x0f,opcode,0xc0] falseFlags)).toOption ==
        some (0x1122334455667700,falseFlags,4099,[])) = true := by
  cases af <;> decide +kernel

/-- Literal opcode/ModRM register vectors; unprefixed 4..7 are deliberately
absent. Distinct dirty GPR values catch bank and destination mistakes. -/
private def banks : List (List Byte × List Byte × Register × Word × Word × Word × Word) :=
  [([0x0f,0x93,0xc0],[0xb0,0x80],.rax,0x1122334455667701,0x1122334455667780,4099,4098),
   ([0x0f,0x93,0xc1],[0xb1,0x80],.rcx,0x2132435465768701,0x2132435465768780,4099,4098),
   ([0x0f,0x93,0xc2],[0xb2,0x80],.rdx,0x3142536475869701,0x3142536475869780,4099,4098),
   ([0x0f,0x93,0xc3],[0xb3,0x80],.rbx,0x415263748596a701,0x415263748596a780,4099,4098),
   ([0x40,0x0f,0x93,0xc0],[0x40,0xb0,0x80],.rax,0x1122334455667701,0x1122334455667780,4100,4099),
   ([0x40,0x0f,0x93,0xc1],[0x40,0xb1,0x80],.rcx,0x2132435465768701,0x2132435465768780,4100,4099),
   ([0x40,0x0f,0x93,0xc2],[0x40,0xb2,0x80],.rdx,0x3142536475869701,0x3142536475869780,4100,4099),
   ([0x40,0x0f,0x93,0xc3],[0x40,0xb3,0x80],.rbx,0x415263748596a701,0x415263748596a780,4100,4099),
   ([0x40,0x0f,0x93,0xc4],[0x40,0xb4,0x80],.rsp,0x2001,0x2080,4100,4099),
   ([0x40,0x0f,0x93,0xc5],[0x40,0xb5,0x80],.rbp,0x61728394a5b6c701,0x61728394a5b6c780,4100,4099),
   ([0x40,0x0f,0x93,0xc6],[0x40,0xb6,0x80],.rsi,0x718293a4b5c6d701,0x718293a4b5c6d780,4100,4099),
   ([0x40,0x0f,0x93,0xc7],[0x40,0xb7,0x80],.rdi,0x8192a3b4c5d6e701,0x8192a3b4c5d6e780,4100,4099),
   ([0x41,0x0f,0x93,0xc0],[0x41,0xb0,0x80],.r8,0x91a2b3c4d5e6f701,0x91a2b3c4d5e6f780,4100,4099),
   ([0x41,0x0f,0x93,0xc1],[0x41,0xb1,0x80],.r9,0xa1b2c3d4e5f60701,0xa1b2c3d4e5f60780,4100,4099),
   ([0x41,0x0f,0x93,0xc2],[0x41,0xb2,0x80],.r10,0xb1c2d3e4f5061701,0xb1c2d3e4f5061780,4100,4099),
   ([0x41,0x0f,0x93,0xc3],[0x41,0xb3,0x80],.r11,0xc1d2e3f405162701,0xc1d2e3f405162780,4100,4099),
   ([0x41,0x0f,0x93,0xc4],[0x41,0xb4,0x80],.r12,0xd1e2f30415263701,0xd1e2f30415263780,4100,4099),
   ([0x41,0x0f,0x93,0xc5],[0x41,0xb5,0x80],.r13,0xe1f2031425364701,0xe1f2031425364780,4100,4099),
   ([0x41,0x0f,0x93,0xc6],[0x41,0xb6,0x80],.r14,0xf102132435465701,0xf102132435465780,4100,4099),
   ([0x41,0x0f,0x93,0xc7],[0x41,0xb7,0x80],.r15,0x0123456789abcd01,0x0123456789abcd80,4100,4099)]

theorem all_banks (af : Bool) :
    banks.all (fun (setBytes,movBytes,destination,setWord,movWord,setPC,movPC) =>
      (view destination af (entry setBytes)).toOption == some (setWord,0xdeadbeef00000612,setPC,[]) &&
      (view destination af (entry movBytes)).toOption == some (movWord,0xdeadbeef00000612,movPC,[])) = true := by
  cases af <;> decide +kernel

theorem actual_context_frame (af : Bool) :
    nextView af (entry [0x0f,0x9f,0xc3]) (fun after reads =>
      (([.rax,.rcx,.rdx,.rbx,.rsp,.rbp,.rsi,.rdi,.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15] :
        List Register).map after.registers,
       ([4096,0x2000,0x4000,0x5000] : List Word).map (fun address =>
         (after.memory.read address,after.memory.executable address,after.memory.writable address)),
       after.flags,after.rip,reads)) =
    .ok ([0x11223344556677fe,0x21324354657687fd,0x31425364758697fc,0x415263748596a701,
          0x2000,0x61728394a5b6c7f9,0x718293a4b5c6d7f8,0x8192a3b4c5d6e7f7,
          0x91a2b3c4d5e6f7f6,0xa1b2c3d4e5f607f5,0xb1c2d3e4f50617f4,0xc1d2e3f4051627f3,
          0xd1e2f304152637f2,0xe1f20314253647f1,0xf1021324354657f0,0x0123456789abcdef],
         [(some 0x0f,true,false),(some 0,false,false),(some 0xa5,false,true),(none,false,false)],
         0xdeadbeef00000612,4099,[]) := by cases af <;> rfl

/-- Full literal-byte replacement, including both endpoints and bit7. -/
theorem immediate_width (af : Bool) :
    ([0,1,0x7f,0x80,0xff] : List Byte).map (fun byte =>
      view .rax af (entry [0xb0,byte])) =
    [.ok (0x1122334455667700,0xdeadbeef00000612,4098,[]),
     .ok (0x1122334455667701,0xdeadbeef00000612,4098,[]),
     .ok (0x112233445566777f,0xdeadbeef00000612,4098,[]),
     .ok (0x1122334455667780,0xdeadbeef00000612,4098,[]),
     .ok (0x11223344556677ff,0xdeadbeef00000612,4098,[])] := by cases af <;> rfl

/-- Compare then SETcc then ordinary RET, through the production runner.
Overflow makes sign alone disagree with signed order; unsigned order differs. -/
theorem compare_setcc_interaction (af : Bool) :
    ([([0x3a,0xc1,0x0f,0x9f,0xc0,0xc3],0x1122334455667780,0x2132435465768701),
      ([0x3a,0xc1,0x0f,0x93,0xc0,0xc3],0x1122334455667780,0x2132435465768701),
      ([0x3a,0xc1,0x0f,0x9f,0xc0,0xc3],0x112233445566777f,0x21324354657687ff),
      ([0x3a,0xc1,0x0f,0x93,0xc0,0xc3],0x112233445566777f,0x21324354657687ff)] :
      List (List Byte × Word × Word)).map (fun (bytes,rax,rcx) =>
        (Sequential.run (fun _ => af) 3 (entry bytes 0xdeadbeef00000612
          (fun r : Register => if r = Register.rax then rax else if r = Register.rcx then rcx else registers r))).map
          (fun result : Result => (result.state.registers .rax,result.state.flags,result.state.rip,
            result.state.registers .rsp,result.instructions,result.reads))) =
    [.ok (0x1122334455667700,0xdeadbeef00000e12,0x3000,0x2008,3,[⟨.stack,0x2000,8⟩]),
     .ok (0x1122334455667701,0xdeadbeef00000e12,0x3000,0x2008,3,[⟨.stack,0x2000,8⟩]),
     .ok (0x1122334455667701,0xdeadbeef00000e83,0x3000,0x2008,3,[⟨.stack,0x2000,8⟩]),
     .ok (0x1122334455667700,0xdeadbeef00000e83,0x3000,0x2008,3,[⟨.stack,0x2000,8⟩])] := by
  cases af <;> rfl

/-- MOV and successive SETcc must retain the incoming flags. An old AL of
one is overwritten even by a false condition. Only RET contributes a read. -/
theorem successive_results (af : Bool) :
    ([0xdeadbeef00000612,0xdeadbeef00000652] : List Word).map (fun flags =>
      (Sequential.run (fun _ => af) 4 (entry [0xb0,1,0x0f,0x95,0xc0,0x0f,0x94,0xc0,0xc3] flags)).map
        (fun result => (result.state.registers .rax,result.state.flags,result.instructions,result.reads))) =
    [.ok (0x1122334455667700,0xdeadbeef00000612,4,[⟨.stack,0x2000,8⟩]),
     .ok (0x1122334455667701,0xdeadbeef00000652,4,[⟨.stack,0x2000,8⟩])] := by cases af <;> rfl

private def rejects (bytes : List Byte) : Bool :=
  (Sequential.decodeAt (entry bytes)).toOption.isNone

theorem unsupported_forms :
    ([[0x0f,0x93,0x00],[0x0f,0x93,0x40,0],[0x0f,0x93,0x80,0,0,0,0],
      [0x40,0x0f,0x93,0x04,0x24],[0x41,0x0f,0x93,0x45,0],
      [0x0f,0x93,0xc8],[0x0f,0x93,0xf8],[0x40,0x0f,0x93,0xcf],
      [0x0f,0x93,0xc4],[0x0f,0x93,0xc5],[0x0f,0x93,0xc6],[0x0f,0x93,0xc7],
      [0xb4,1],[0xb5,1],[0xb6,1],[0xb7,1],
      [0x42,0x0f,0x93,0xc0],[0x44,0x0f,0x93,0xc0],[0x48,0x0f,0x93,0xc0],
      [0x4f,0x0f,0x93,0xc0],[0x42,0xb0,1],[0x44,0xb0,1],[0x48,0xb0,1],
      [0x66,0x0f,0x93,0xc0],[0xf0,0x0f,0x93,0xc0],[0xf3,0x0f,0x93,0xc0],
      [0x67,0xb0,1],[0x66,0xb0,1],[0xf0,0xb0,1],[0x40,0x41,0xb0,1],
      [0x40,0x40,0x0f,0x93,0xc0],[0x0f,0x8f,0xc0],[0x0f,0xa0,0xc0],
      [0xc6,0xc0,1]] : List (List Byte)).all rejects = true := by decide +kernel

theorem unreviewed_rex_aliases :
    ([0x42,0x43,0x44,0x45,0x46,0x47,0x48,0x49,0x4a,0x4b,0x4c,0x4d,0x4e,0x4f] :
      List Byte).all (fun rex => rejects [rex,0x0f,0x93,0xc0] && rejects [rex,0xb0,1]) = true :=
  by decide +kernel

theorem exact_missing_suffixes :
    ([([0x0f],1),([0x0f,0x93],2),([0x40],1),([0x40,0x0f],2),
      ([0x40,0x0f,0x93],3),([0x41,0x0f,0x95],3),([0xb0],1),([0xb3],1),
      ([0x40,0xb4],2),([0x41,0xb7],2)] : List (List Byte × Nat)).all
      (fun (bytes,offset) => match Sequential.decodeAt (entry bytes) with
        | .error (.inaccessibleInstruction address) => address == 4096 + BitVec.ofNat 64 offset
        | _ => false) = true := by decide +kernel

/-- Existing but nonexecutable suffixes fault exactly where truncated ones do.
Each complete form succeeds without fetching the absent following byte. -/
theorem execute_permissions_and_length (af : Bool) :
    ([([0x0f,0x93,0xc0],2),([0x40,0x0f,0x93,0xc4],3),
      ([0x41,0x0f,0x93,0xc7],3),([0xb0,0xff],1),([0x40,0xb4,0xff],2),
      ([0x41,0xb7,0xff],2)] : List (List Byte × Nat)).all (fun (bytes,offset) =>
        let before := entry bytes
        let denied := { before with memory := { before.memory with
          executable := fun address => before.memory.executable address &&
            address != 4096 + BitVec.ofNat 64 offset } }
        (match Sequential.step af before with | .ok _ => true | _ => false) &&
        (match Sequential.decodeAt denied with
          | .error (.inaccessibleInstruction address) => address == 4096 + BitVec.ofNat 64 offset
          | _ => false)) = true := by cases af <;> decide +kernel

/-- ModRM changes select the actual destination; an immediate change replaces
the byte. Neither stale CFG annotations nor a prefix can hide these changes. -/
theorem changed_suffixes (af : Bool) :
    (view .rcx af (entry [0x0f,0x93,0xc1]),view .rax af (entry [0xb0,0xff]),
      view .r8 af (entry [0x41,0x0f,0x93,0xc0])) =
    (.ok (0x2132435465768701,0xdeadbeef00000612,4099,[]),
      .ok (0x11223344556677ff,0xdeadbeef00000612,4098,[]),
      .ok (0x91a2b3c4d5e6f701,0xdeadbeef00000612,4100,[])) := by cases af <;> rfl

/-- A partial RSP write executes, then raw RET faults at its real new slot.
The original read-only caller word does not supply the missing ninth byte. -/
theorem changed_rsp_ret (af : Bool) :
    (Sequential.run (fun _ => af) 2 (entry [0x40,0xb4,1,0xc3])).map (fun _ => ()) =
      .error (.inaccessibleStack 8200) ∧
    (Sequential.run (fun _ => af) 2 (entry [0x40,0x0f,0x93,0xc4,0xc3])).map (fun _ => ()) =
      .error (.inaccessibleStack 8200) := by cases af <;> exact ⟨rfl,rfl⟩

private def program : List Byte := [0xb0,0xff,0x0f,0x95,0xc0,0xc3]
private def graph : CFG.Graph :=
  ⟨[⟨0,.movImm8 .rax 0xff false,true,3⟩,
    ⟨2,.setcc .notEqual .rax false,false,2⟩,⟨5,.legacy .ret,false,1⟩],3⟩

theorem checked_graph : CFG.Valid program graph := CFG.check_sound (by decide +kernel)

theorem discovered_graph : CFG.analyze program = .ok graph := by rfl

theorem changed_graph_rejected :
    CFG.check [0xb0,0x80,0x0f,0x95,0xc0,0xc3] graph = false ∧
    CFG.check [0xb0,0xff,0x0f,0x94,0xc0,0xc3] graph = false ∧
    CFG.check [0xb0,0xff,0x0f,0x95,0xc1,0xc3] graph = false ∧
    CFG.check [0xb0,0xff,0x0f,0x95] graph = false := by decide +kernel

/-- A callee-saved destination is real instruction behavior. Ordinary byte
execution and read-only CFG admission do not promise the old RBX value. -/
theorem callee_saved_write (af : Bool) :
    (Sequential.run (fun _ => af) 2 (entry [0x0f,0x93,0xc3,0xc3])).map
      (fun result => (result.state.registers .rbx,result.state.registers .rsp,
        result.state.rip,result.reads)) =
      .ok (0x415263748596a701,0x2008,0x3000,[⟨.stack,0x2000,8⟩]) := by cases af <;> rfl

theorem callee_saved_vc_rejected :
    let savedGraph : CFG.Graph :=
      ⟨[⟨0,.setcc .aboveEqual .rbx false,true,2⟩,⟨3,.legacy .ret,false,1⟩],2⟩
    ¬ VCGen.wp savedGraph 4096 (fun _ _ => True) 2 ⟨0,by decide⟩
      (entry [0x0f,0x93,0xc3,0xc3])
      (fun result => result.state.registers .rbx = 0x415263748596a7fb) := by
  let savedGraph : CFG.Graph :=
    ⟨[⟨0,.setcc .aboveEqual .rbx false,true,2⟩,⟨3,.legacy .ret,false,1⟩],2⟩
  change ¬ VCGen.wp savedGraph 4096 (fun _ _ => True) 2 ⟨0,by decide⟩
    (entry [0x0f,0x93,0xc3,0xc3]) _
  letI := VCGen.decidableWP savedGraph 4096 (fun _ _ => True) (fun _ _ => inferInstance)
    2 ⟨0,by decide⟩ (entry [0x0f,0x93,0xc3,0xc3])
    (fun result => result.state.registers .rbx = 0x415263748596a7fb)
    (fun _ => inferInstance)
  decide

private def allowed (_ : State) (read : Read) : Prop := read = ⟨.stack,0x2000,8⟩
private def post (result : Result) : Prop :=
  result.state.registers .rax = 0x1122334455667701 ∧
  result.state.registers .rsp = 0x2008 ∧ result.state.rip = 0x3000 ∧
  result.state.flags = 0xdeadbeef00000612 ∧ result.instructions = 3 ∧
  result.reads = [⟨.stack,0x2000,8⟩]

/-- Production VCG for an independent literal contract; both undefined choices
are quantified by wp. No data-read permission is supplied. -/
theorem generated_vc : VCGen.wp graph 4096 allowed 3 ⟨0,by decide⟩ (entry program) post := by
  letI := VCGen.decidableWP graph 4096 allowed (fun _ _ => by unfold allowed; infer_instance)
    3 ⟨0,by decide⟩ (entry program) post (fun _ => by unfold post; infer_instance)
  decide

/-- Actual checked-byte transport and production execution, with whole-memory
framing. This checks the bridge beyond direct execute or static graph checks. -/
theorem generated_vc_runs (choices : Choices) :
    ∃ result, Sequential.run choices 3 (entry program) = .ok result ∧ post result ∧
      result.state.memory = (entry program).memory ∧ result.instructions ≤ 3 ∧
      VCGen.CheckedTrace allowed choices (entry program) result := by
  apply VCGen.run_sound_frame checked_graph (node := ⟨0,by decide⟩)
    (base := 4096) (code := ?_) (pc := rfl) generated_vc choices
  constructor
  · decide
  · intro offset byte present
    have inside : offset < 6 := by
      obtain ⟨bound,_⟩ := List.getElem?_eq_some_iff.mp present
      simpa [program] using bound
    have : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 ∨ offset = 4 ∨ offset = 5 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [program] at present <;> subst byte <;> rfl

theorem lifted_production (af : Bool) :
    (CallReturn.decodeAt (entry [0x0f,0x9f,0xc0]),
      CallReturn.decodeAt (entry [0x41,0xb7,0x80]),
      (CallReturn.rawStep af (entry [0x41,0xb7,0x80])).map (fun observation =>
        observation.reads),
      Literals.instruction (.setcc .greater .rax false),
      Literals.instruction (.movImm8 .r15 0x80 true)) =
    (.ok (.sequential (.setcc .greater .rax false)),
      .ok (.sequential (.movImm8 .r15 0x80 true)),.ok [],
      "(.setcc .greater .rax false)","(.movImm8 .r15 128 true)") := by cases af <;> rfl

/-- Transport current code into the actual resource-coupled machine, then
retain the SAME complete world and original caller slot after changing RSP. -/
theorem current_rsp_keeps_original_authority {call : OS.CallResources.Call}
    {shared : OS.CallResources.Shared} {before : State}
    (current : OS.CallResources.Current call shared before)
    (bytes : call.bytes = [0x40,0xb4,1,0xc3]) (pc : before.rip = call.code)
    (slotLow : (call.stack).setWidth 8 = 0) :
    ∃ after, (∀ af, Sequential.step af before = .ok ⟨.next after,[]⟩) ∧
      OS.CallResources.Current call shared after ∧
      OS.Threads.HasLoan shared call.worker call.stackLoan ⟨call.stack,8⟩ ∧
      readWord after.memory call.stack = .ok call.returnAddress ∧
      ¬ OS.CallResources.ReadAllowed call shared ⟨.stack,after.registers .rsp,8⟩ := by
  have code : CodeAt before.memory call.code [0x40,0xb4,1,0xc3] := by
    rw [current.coupled,← bytes]
    exact current.contract.code
  have decoded : Sequential.decodeAt before = .ok (.movImm8 .rsp 1 true) :=
    decodeAt_transport (code_fetch_transport code (by decide) 0 (by decide) before rfl
      (by simpa using pc)) (by rfl)
  obtain ⟨after,step,currentAfter,context⟩ := OS.CallResources.current_movImm8_step current decoded
  refine ⟨after,step,currentAfter,current.contract.stackLoan,?_,?_⟩
  · rw [context.memory,current.coupled]
    exact current.contract.stack
  · intro allowedRead
    have same := congrArg (fun word : Word => word.setWidth 8) allowedRead.2.1
    rw [context.low8,slotLow] at same
    exact (by decide : (1 : Byte) ≠ 0) same

end EDSL.Tests.SequentialLow8
