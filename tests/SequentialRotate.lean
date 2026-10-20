/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Rotate
import EDSL.X86.Sequential.CFGDiscovery
import EDSL.X86.Sequential.Literals
import EDSL.X86.CallReturn.DecodeTransport
import EDSL.X86.VCGen.Frame
import EDSL.X86.VCGen.PureCall
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.SequentialRotate
open X86 X86.Sequential

private def allRegisters : List Register :=
  [.rax,.rcx,.rdx,.rbx,.rsp,.rbp,.rsi,.rdi,.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15]

private def canary : Register → Word
  | .rax => 0x8000000100000001 | .rcx => 0x8000000100000002
  | .rdx => 0x8000000100000003 | .rbx => 0x8000000100000004
  | .rsp => 0x8000000100000005 | .rbp => 0x8000000100000006
  | .rsi => 0x8000000100000007 | .rdi => 0x8000000100000008
  | .r8 => 0x8000000100000009 | .r9 => 0x800000010000000a
  | .r10 => 0x800000010000000b | .r11 => 0x800000010000000c
  | .r12 => 0x800000010000000d | .r13 => 0x800000010000000e
  | .r14 => 0x800000010000000f | .r15 => 0x8000000100000010

/-- Only the instruction is mapped; there is no DATA or stack access available.
Destination precedence makes RCX alias cases use its actual old value. -/
private def entry (code : List Byte) (destination : Register := .rax)
    (input : Word := 0x8000000000000001) (count : Word := 2)
    (flags : Word := 0x6d7) (rip : Word := 4096) : State where
  registers r := if r = destination then input else if r = .rcx then count else canary r
  flags := flags
  rip := rip
  memory := {
    read := fun address => code[(address - rip).toNat]?
    executable := fun address => decide ((address - rip).toNat < code.length)
    writable := fun address => address.getLsbD 4 }

/- Independent literal encodings, not generated with a model encoder. -/
private def lowForms : List (Byte × Register) :=
  [(0xc0,.rax),(0xc1,.rcx),(0xc2,.rdx),(0xc3,.rbx),
   (0xc4,.rsp),(0xc5,.rbp),(0xc6,.rsi),(0xc7,.rdi)]
private def highForms : List (Byte × Register) :=
  [(0xc0,.r8),(0xc1,.r9),(0xc2,.r10),(0xc3,.r11),
   (0xc4,.r12),(0xc5,.r13),(0xc6,.r14),(0xc7,.r15)]

private def decoded (rex : Byte) (form : Byte × Register) : Bool :=
  let state := entry [rex,0xd3,form.1] form.2 0x8000000000000002
  match Sequential.decodeAt state, X86.decodeAt state, CallReturn.decodeAt state with
  | .ok actual, .error _, .ok lifted =>
    decide (actual = .rolCL64 form.2) && actual.length == 3 && actual.isNew &&
    !actual.choosesAF && actual.choiceFlag state == some .of && !actual.isLocked &&
    actual.operandReads state == [] && actual.storeIntent state == none &&
    actual.storeIntent64 state == none && decide (lifted = .sequential (.rolCL64 form.2))
  | _, _, _ => false

theorem decode_both_banks :
    lowForms.all (decoded 0x48) = true ∧ highForms.all (decoded 0x49) = true := by
  exact ⟨by decide +kernel, by decide +kernel⟩

private def outcome (code : List Byte) (destination : Register) (input count expected : Word)
    (oldFlags flagsFalse flagsTrue : Word) (rip : Word := 4096) : Bool :=
  let initial := entry code destination input count oldFlags rip
  [false,true].all fun choice =>
    match Sequential.step choice initial with
    | .ok ⟨.next final, reads⟩ =>
      reads == [] && final.rip == rip + 3 && final.registers destination == expected &&
      final.flags == (if choice then flagsTrue else flagsFalse) &&
      allRegisters.all (fun r => if r == destination then true else final.registers r == initial.registers r) &&
      ([0,4096,4098,4099,0x800000000000,0xffffffffffffffff] : List Word).all (fun address =>
        final.memory.read address == initial.memory.read address &&
        final.memory.executable address == initial.memory.executable address &&
        final.memory.writable address == initial.memory.writable address)
    | _ => false

/-- 63 distinguishes the six-bit mask from a five-bit mask; 64/128 retain
ALL flags; 65 defines OF rather than choosing it; 255 uses masked count 63.
The expected hexadecimal results and complete flag words are independent
literals, including preserved AF/PF/ZF/SF despite the nonzero results. -/
theorem count_edges_and_flags :
    ([(0,0x8000000000000001,0x6d7,0x6d7),
      (1,3,0xed7,0xed7), (2,6,0x6d6,0xed6),
      (63,0xc000000000000000,0x6d6,0xed6),
      (64,0x8000000000000001,0x6d7,0x6d7),
      (65,3,0xed7,0xed7), (128,0x8000000000000001,0x6d7,0x6d7),
      (255,0xc000000000000000,0x6d6,0xed6)] : List (Word × Word × Word × Word)).all
      (fun (count,result,f0,f1) => outcome [0x48,0xd3,0xc0] .rax
        0x8000000000000001 count result 0x6d7 f0 f1) = true := by decide +kernel

/-- All sixteen destinations, including RSP without a stack read and RCX
whose old low six bits equal two. R12/R13 must not fetch SIB/displacement. -/
theorem execution_banks :
    lowForms.all (fun (modrm,dest) => outcome [0x48,0xd3,modrm] dest
      0x8000000000000002 2 10 0x6d7 0x6d6 0xed6) = true ∧
    highForms.all (fun (modrm,dest) => outcome [0x49,0xd3,modrm] dest
      0x8000000000000002 2 10 0x6d7 0x6d6 0xed6) = true := by
  exact ⟨by decide +kernel, by decide +kernel⟩

/-- These alias cases fail if the count is read from the new RCX. -/
theorem rcx_alias_uses_old_count :
    outcome [0x48,0xd3,0xc1] .rcx 0x8000000000000041 7 0x83 0x6d7 0xed7 0xed7 = true ∧
    outcome [0x48,0xd3,0xc1] .rcx 0x8000000000000040 7
      0x8000000000000040 0xed7 0xed7 0xed7 = true := by
  exact ⟨by decide +kernel, by decide +kernel⟩

/-- Different high input bits distinguish OF's XOR rule and full-width
wraparound. Zero must not synthesize ZF/PF; AF=0 and AF=1 both survive. -/
theorem high_bits_zero_and_dirty_flags :
    outcome [0x49,0xd3,0xc7] .r15 0x4000000000000000 1
      0x8000000000000000 0x6d7 0xed6 0xed6 = true ∧
    outcome [0x48,0xd3,0xc0] .rax 0xffffffffffffffff 1
      0xffffffffffffffff 0xed7 0x6d7 0x6d7 = true ∧
    outcome [0x48,0xd3,0xc0] .rax 0x8000000000000000 1 1 0 0x801 0x801 = true ∧
    outcome [0x48,0xd3,0xc0] .rax 0 1 0 0x202 0x202 0x202 = true ∧
    outcome [0x48,0xd3,0xc0] .rax 0 2 0 0x202 0x202 0xa02 = true ∧
    outcome [0x48,0xd3,0xc0] .rax 0 2 0 0xffffffffffffffff
      0xfffffffffffff7fe 0xfffffffffffffffe = true ∧
    outcome [0x48,0xd3,0xc0] .rax 1 0xffffffffffffffc1 2 0x6d7 0x6d6 0x6d6 = true := by
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

private def fault {α : Type} (result : Except Error α) (expected : Error) : Bool :=
  match result with | .error actual => actual == expected | .ok _ => false
private def rejects (code : List Byte) (expected : Error := .unsupportedEncoding) : Bool :=
  let state := entry code
  fault (Sequential.decodeAt state) expected &&
    [false,true].all (fun choice => fault (Sequential.step choice state) expected)

theorem group_memory_width_and_prefix_rejection :
    ([[0x48,0xd3,0xc8], [0x48,0xd3,0xd0], [0x48,0xd3,0xd8],
      [0x48,0xd3,0xe0], [0x48,0xd3,0xe8], [0x48,0xd3,0xf0], [0x48,0xd3,0xf8],
      [0x49,0xd3,0x00], [0x48,0xd3,0x04], [0x48,0xd3,0x45], [0x48,0xd3,0x80],
      [0x40,0xd3,0xc0], [0x41,0xd3,0xc0], [0x48,0xd1,0xc0],
      [0x48,0xc1,0xc0,1], [0x48,0xd2,0xc0], [0x48,0xd0,0xc0],
      [0x4a,0xd3], [0x4b,0xd3], [0x4c,0xd3], [0x4d,0xd3], [0x4e,0xd3], [0x4f,0xd3],
      [0x48,0x48,0xd3,0xc0], [0x49,0x48,0xd3,0xc0],
      [0x66,0x48,0xd3,0xc0], [0xf0,0x48,0xd3,0xc0],
      [0xf3,0x48,0xd3,0xc0]] : List (List Byte)).all (fun code => rejects code) = true := by
  decide +kernel

theorem unprefixed_and_unknown_prefix :
    rejects [0xd3,0xc0] (.unsupportedOpcode 0xd3) = true ∧
    rejects [0x67,0x48,0xd3,0xc0] (.unsupportedOpcode 0x67) = true ∧
    rejects [0xf2,0x48,0xd3,0xc0] (.unsupportedOpcode 0xf2) = true := by
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- IMUL cannot be admitted with four undefined flags correlated through one
Bool. This remains outside the single-flag production profile. -/
theorem imul_stays_unsupported :
    rejects [0x48,0x0f,0xaf,0xc1] = true := by decide +kernel

private def fetchFailures (rex : Byte) : Bool :=
  let initial := entry [rex,0xd3,0xc7]
  (List.range 3).all fun i =>
    let address := initial.rip + BitVec.ofNat 64 i
    let missing := { initial with memory := { initial.memory with
      read := fun a => if a = address then none else initial.memory.read a } }
    let denied := { initial with memory := { initial.memory with
      executable := fun a => if a = address then false else initial.memory.executable a } }
    [missing,denied].all fun state =>
      fault (Sequential.decodeAt state) (.inaccessibleInstruction address) &&
      fault (CallReturn.decodeAt state) (.inaccessibleInstruction address) &&
      [false,true].all (fun choice => fault (Sequential.step choice state) (.inaccessibleInstruction address))

theorem every_fetch_authenticated :
    ([0x48,0x49] : List Byte).all fetchFailures = true := by decide +kernel

theorem truncation_and_canonical_boundary :
    rejects [] (.inaccessibleInstruction 4096) = true ∧
    rejects [0x48] (.inaccessibleInstruction 4097) = true ∧
    rejects [0x49,0xd3] (.inaccessibleInstruction 4098) = true ∧
    fault (Sequential.step false (entry [0x48,0xd3,0xc0] .rax 1 2 0 0x7ffffffffffe))
      (.inaccessibleInstruction 0x800000000000) = true ∧
    outcome [0x49,0xd3,0xc4] .r12 0x8000000000000001 2 6 0x6d7 0x6d6 0xed6
      0xfffffffffffffffd = true := by
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

/-- Independent graph inventory, exact generated constructor, shared profile. -/
theorem cfg_and_literal :
    CFG.analyze [0x49,0xd3,0xc0,0xc3] = .ok {
      nodes := [⟨0,.rolCL64 .r8,true,2⟩,⟨3,.legacy .ret,false,1⟩], maxDepth := 2 } ∧
    Literals.instruction (.rolCL64 .r12) = "(.rolCL64 .r12)" := ⟨rfl, rfl⟩

namespace Generated
open VCGen

private def bytes : List Byte := [0x48,0xd3,0xc0,0xc3]
private def graph : CFG.Graph := CFG.annotate
  [⟨0,.rolCL64 .rax,false,0⟩,⟨3,.legacy .ret,false,0⟩]
private def start : graph.Index := ⟨0, by decide⟩
private def memory (actual : List Byte := bytes) : Memory where
  read address := if 4096 ≤ address.toNat ∧ address.toNat < 4100 then
    actual[address.toNat - 4096]? else some 0
  executable address := decide (4096 ≤ address.toNat ∧ address.toNat < 4100)
private def initial (count : Word := 2) : State :=
  ⟨fun r => if r = .rax then 0x8000000000000001 else if r = .rcx then count else 0,
    4096, 0x6d7, memory⟩
private def Allowed (_ : State) (read : Read) : Prop := read = ⟨.stack,0,8⟩
private def Post (result : Result) : Prop :=
  result.state.registers .rax = 6 ∧ result.state.registers .rcx = 2 ∧
  result.state.rip = 0 ∧ result.state.registers .rsp = 8 ∧
  result.state.flags &&& ~~~(0x800 : Word) = 0x6d6 ∧
  result.instructions = 2 ∧ result.reads = [⟨.stack,0,8⟩]

instance (state : State) (read : Read) : Decidable (Allowed state read) :=
  inferInstanceAs (Decidable (_ = _))
instance (result : Result) : Decidable (Post result) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

private def checkPost (state : State) (contract : Contract)
    (decPost : ∀ result, Decidable (contract result)) : Bool :=
  letI := decidableWP graph 4096 Allowed (fun _ _ => inferInstance) 2 start state contract decPost
  check graph 4096 Allowed 2 start state contract
private def certifyPost (state : State) (contract : Contract)
    (decPost : ∀ result, Decidable (contract result)) : Bool :=
  letI := decidableWP graph 4096 Allowed (fun _ _ => inferInstance) 2 start state contract decPost
  certify bytes graph 4096 Allowed 2 start state contract

/-- Real decoded execution, all choices, exact output/accounting and complete
memory frame come from the production generated checker, not an evaluator. -/
theorem accepts_all_choices (choices : Choices) :
    ∃ result, Sequential.run choices 2 initial = .ok result ∧ Post result ∧
      result.state.memory = initial.memory ∧ result.instructions ≤ 2 ∧
      CheckedTrace Allowed choices initial result := by
  letI := decidableWP graph 4096 Allowed (fun _ _ => inferInstance) 2 start initial Post
    (fun _ => inferInstance)
  have accepted : certify bytes graph 4096 Allowed 2 start initial Post = true := by decide +kernel
  exact certify_sound_frame accepted choices

/-- Actual RAM contains a different destination; a good VC about RAX cannot
certify it. This fails if byte authentication is omitted from certification. -/
theorem mutated_ram_refused :
    let stale := { initial with memory := memory [0x48,0xd3,0xc2,0xc3] }
    checkPost stale Post (fun _ => inferInstance) = true ∧
      certifyPost stale Post (fun _ => inferInstance) = false := by decide +kernel

/-- Refuse either fixed value of undefined OF; both model branches matter. -/
theorem fixed_undefined_of_refused :
    ([false,true] : List Bool).all (fun bit =>
      !(checkPost initial (fun result => result.state.flags.getLsbD 11 = bit)
        (fun _ => inferInstance))) = true := by decide +kernel

/-- Definedness uses the MASKED count, with no undefined choice at 64 or 65. -/
theorem masked_defined_of_accepted :
    checkPost (initial 64) (fun result => result.state.flags.getLsbD 11 = false)
      (fun _ => inferInstance) = true ∧
    checkPost (initial 65) (fun result => result.state.flags.getLsbD 11 = true)
      (fun _ => inferInstance) = true := by exact ⟨by decide +kernel, by decide +kernel⟩

/-- Original caller/code loans and all ownership metadata survive every
continuing prefix. The protected original return slot remains the only read. -/
theorem current_resources {call : OS.CallResources.Call} {shared : OS.CallResources.Shared}
    {state : State} {contract : Contract}
    (current : OS.CallResources.Current call shared state)
    (code : CodeAt state.memory 4096 bytes) (pc : state.rip = 4096)
    (vc : wp graph 4096 (fun _ read => OS.CallResources.ReadAllowed call shared read)
      2 start state contract) :
    Grading.ReadOnlyPolicy state (OS.CallResources.Current call shared)
      (fun _ read => OS.CallResources.ReadAllowed call shared read) := by
  have valid : CFG.Valid bytes graph := CFG.check_sound (by decide +kernel)
  have offset : (graph.node start).offset = 0 := by decide +kernel
  exact readOnly_policy valid code (by simpa only [offset, BitVec.add_zero] using pc) vc _
    (fun _ same => current.sameMemory same)

end Generated
end EDSL.Tests.SequentialRotate

#audit_edsl
