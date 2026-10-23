/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.Effects.Frames
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.Tests.EffectVCGen
open X86 Sequential

/-!
Owned synthetic bytes and independent literal contracts for the production
vector executor and the shared effect VCG. The only current-state predicate is
`True`: these fixtures claim no logical OS authority. Initial executable bytes
are proved from the actual mapping; the generic separation frame transports
them through actual data writes. No future code binding or post-memory premise
is supplied. Atomic events are obtained from the checked production trace.

Scope is bounded sequential execution and its ordered actual atomic events.
This is not concurrency, TSO, linearizability, whole-OS or corpus evidence.
-/

private def memory (bytes : List Byte) (target : Word) : Memory where
  read address :=
    if 0x4000 ≤ address.toNat ∧ address.toNat < 0x4000 + bytes.length then
      bytes[address.toNat - 0x4000]?
    else if target.toNat ≤ address.toNat ∧ address.toNat < target.toNat + 4 then
      [0x2a, 0, 0, 0][address.toNat - target.toNat]?
    else if 0x9000 ≤ address.toNat ∧ address.toNat < 0x9008 then
      [0, 0x50, 0, 0, 0, 0, 0, 0][address.toNat - 0x9000]?
    else none
  executable address := decide (0x4000 ≤ address.toNat ∧
    address.toNat < 0x4000 + bytes.length)
  writable address := decide (target.toNat ≤ address.toNat ∧
    address.toNat < target.toNat + 4)

private def entryState (bytes : List Byte) (target : Word := 0x8000)
    (source : Word := 0x11223344) : State where
  registers register := match register with
    | .rax => 1
    | .rsi => source
    | .rdi => target
    | .rsp => 0x9000
    | _ => 0
  rip := 0x4000
  flags := 0xabcdef
  memory := memory bytes target

/-- A single mapping lemma handles both program lengths and writable-text
negative fixtures. It assumes only a size bound on the selected initial bytes. -/
private theorem initial_code (bytes : List Byte) (size : bytes.length ≤ 4096)
    (target source : Word) :
    CodeAt (entryState bytes target source).memory 0x4000 bytes := by
  refine ⟨by change 16384 + bytes.length ≤ 2 ^ 64; omega, ?_⟩
  intro offset byte present
  have inside := (List.getElem_of_getElem? present).1
  have small : offset < 2 ^ 64 := by omega
  have sumSmall : 16384 + offset < 2 ^ 64 := by omega
  have natural : ((0x4000 : Word) + BitVec.ofNat 64 offset).toNat =
      16384 + offset := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt small]
    change (16384 + offset) % 2 ^ 64 = 16384 + offset
    exact Nat.mod_eq_of_lt sumSmall
  have canonicalByte : canonical ((0x4000 : Word) + BitVec.ofNat 64 offset) = true := by
    unfold canonical
    rw [natural]
    exact decide_eq_true (Or.inl (by omega))
  have mapped : 16384 ≤ 16384 + offset ∧
      16384 + offset < 16384 + bytes.length := by omega
  have executable : (memory bytes target).executable
      ((0x4000 : Word) + BitVec.ofNat 64 offset) = true := by
    change decide (16384 ≤ ((0x4000 : Word) + BitVec.ofNat 64 offset).toNat ∧
      ((0x4000 : Word) + BitVec.ofNat 64 offset).toNat < 16384 + bytes.length) = true
    rw [natural]
    exact decide_eq_true mapped
  have mappedRead : (memory bytes target).read
      ((0x4000 : Word) + BitVec.ofNat 64 offset) = some byte := by
    change (if 16384 ≤ ((0x4000 : Word) + BitVec.ofNat 64 offset).toNat ∧
        ((0x4000 : Word) + BitVec.ofNat 64 offset).toNat < 16384 + bytes.length then
      bytes[((0x4000 : Word) + BitVec.ofNat 64 offset).toNat - 16384]? else _) = some byte
    rw [natural, ite_eq_left mapped]
    simpa only [Nat.add_sub_cancel_left] using present
  change fetchByte (memory bytes target) ((0x4000 : Word) + BitVec.ofNat 64 offset) = .ok byte
  unfold fetchByte
  rw [canonicalByte, executable]
  change (match (memory bytes target).read ((0x4000 : Word) + BitVec.ofNat 64 offset) with
    | some value => (Except.ok value : Except Error Byte)
    | none => Except.error (Error.inaccessibleInstruction
        ((0x4000 : Word) + BitVec.ofNat 64 offset))) = .ok byte
  rw [mappedRead]

private theorem data_separated (length : Nat) (small : length ≤ 7) :
    DWordDisjoint 0x8000 0x4000 length := by
  intro offset inside
  have alternatives : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 ∨
      offset = 4 ∨ offset = 5 ∨ offset = 6 := by omega
  rcases alternatives with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

private def separatedPolicy (bytes : List Byte) : VCGen.Effects.Policy :=
  VCGen.Effects.codeSeparatedPolicy bytes 0x4000 (fun _ => True) (fun _ _ => True)

private theorem separatedFrame (bytes : List Byte) :
    VCGen.Effects.CodeFrame (separatedPolicy bytes) bytes 0x4000 :=
  VCGen.Effects.codeSeparatedPolicy_codeFrame bytes 0x4000
    (fun _ => True) (fun _ _ => True)

namespace StoreLoad

/-- MOV [RDI],ESI; MOV EAX,[RDI]; RET. -/
def bytes : List Byte := [0x89, 0x37, 0x8b, 0x07, 0xc3]

def graph : CFG.Graph := ⟨[
  ⟨0, .legacy .storeEsiRdi, true, 2⟩,
  ⟨2, .legacy .loadEaxRdi, false, 1⟩,
  ⟨4, .legacy .ret, false, 0⟩], 2⟩

abbrev entry : graph.Index := ⟨0, by decide +kernel⟩
private abbrev loadNode : graph.Index := ⟨1, by decide +kernel⟩
private abbrev retNode : graph.Index := ⟨2, by decide +kernel⟩

def initial : State := entryState bytes

theorem valid : CFG.Structural.Valid bytes graph :=
  CFG.Structural.check_sound (by decide +kernel)

private theorem code : CodeAt initial.memory 0x4000 bytes :=
  initial_code bytes (by decide +kernel) 0x8000 0x11223344

/-- Literal byte order, return state, instruction cost and original stack read.
The store's permission checks are not extra operand reads. -/
def Post (result : Result) (events : List AtomicEvent) : Prop :=
  result.state.registers .rax = 0x11223344 ∧
  result.state.memory.read 0x8000 = some 0x44 ∧
  result.state.memory.read 0x8001 = some 0x33 ∧
  result.state.memory.read 0x8002 = some 0x22 ∧
  result.state.memory.read 0x8003 = some 0x11 ∧
  result.state.rip = 0x5000 ∧ result.state.registers .rsp = 0x9008 ∧
  result.instructions = 3 ∧
  result.reads = [⟨.data, 0x8000, 4⟩, ⟨.stack, 0x9000, 8⟩] ∧ events = []

theorem generated :
    VCGen.Effects.wp graph 0x4000 (separatedPolicy bytes) 3 entry initial Post := by
  refine ⟨trivial, ?_⟩
  intro choices
  refine ⟨?_, ?_, loadNode, by decide +kernel, rfl, ?_⟩
  · intro _ _
    trivial
  · exact VCGen.Effects.CodeSeparated.store32 rfl
      (data_separated bytes.length (by decide +kernel))
  · refine ⟨trivial, ?_⟩
    intro nextChoices
    refine ⟨?_, VCGen.Effects.CodeSeparated.readOnly rfl,
      retNode, by decide +kernel, rfl, ?_⟩
    · intro _ _
      trivial
    · refine ⟨trivial, ?_⟩
      intro returnChoices
      exact ⟨(fun _ _ => trivial), VCGen.Effects.CodeSeparated.readOnly rfl,
        trivial, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Any complete flag stream replays the actual bytes with the literal contract
and a checked trace. Executable text is framed by the shared generic theorem. -/
theorem runs (choices : ChoiceStream FlagChoices) :
    ∃ result events, runWith choices 3 initial = .ok result ∧ Post result events ∧
      result.instructions ≤ 3 ∧
      VCGen.Effects.Trace bytes 0x4000 (separatedPolicy bytes) choices initial result events :=
  VCGen.Effects.run_sound valid (separatedFrame bytes) code rfl generated choices

end StoreLoad

namespace AtomicPair

/-- XCHG [RDI],EAX; LOCK XADD [RDI],EAX; RET. -/
def bytes : List Byte := [0x87, 0x07, 0xf0, 0x0f, 0xc1, 0x07, 0xc3]

def graph : CFG.Graph := ⟨[
  ⟨0, .legacy .exchangeEaxRdi, true, 2⟩,
  ⟨2, .legacy .fetchAddEaxRdi, false, 1⟩,
  ⟨6, .legacy .ret, false, 0⟩], 2⟩

abbrev entry : graph.Index := ⟨0, by decide +kernel⟩
private abbrev addNode : graph.Index := ⟨1, by decide +kernel⟩
private abbrev retNode : graph.Index := ⟨2, by decide +kernel⟩

def initial : State := entryState bytes

theorem valid : CFG.Structural.Valid bytes graph :=
  CFG.Structural.check_sound (by decide +kernel)

private theorem code : CodeAt initial.memory 0x4000 bytes :=
  initial_code bytes (by decide +kernel) 0x8000 0x11223344

/-- The second operation reads the first operation's 1, adds the exchanged 42,
and returns 1. Literal event order and multiplicity are part of the contract. -/
def Post (result : Result) (events : List AtomicEvent) : Prop :=
  result.state.registers .rax = 1 ∧
  result.state.memory.read 0x8000 = some 0x2b ∧
  result.state.memory.read 0x8001 = some 0 ∧
  result.state.memory.read 0x8002 = some 0 ∧
  result.state.memory.read 0x8003 = some 0 ∧
  result.state.rip = 0x5000 ∧ result.state.registers .rsp = 0x9008 ∧
  result.instructions = 3 ∧
  result.reads = [⟨.data, 0x8000, 4⟩, ⟨.data, 0x8000, 4⟩,
    ⟨.stack, 0x9000, 8⟩] ∧
  events = [⟨0x8000, 42, 1⟩, ⟨0x8000, 1, 43⟩]

theorem generated :
    VCGen.Effects.wp graph 0x4000 (separatedPolicy bytes) 3 entry initial Post := by
  refine ⟨trivial, ?_⟩
  intro choices
  refine ⟨?_, ?_, addNode, by decide +kernel, rfl, ?_⟩
  · intro _ _
    trivial
  · exact VCGen.Effects.CodeSeparated.exchange
      (data_separated bytes.length (by decide +kernel))
  · refine ⟨trivial, ?_⟩
    intro nextChoices
    refine ⟨?_, ?_, retNode, by decide +kernel, rfl, ?_⟩
    · intro _ _
      trivial
    · exact VCGen.Effects.CodeSeparated.fetchAdd
        (data_separated bytes.length (by decide +kernel))
    · refine ⟨trivial, ?_⟩
      intro returnChoices
      exact ⟨(fun _ _ => trivial), VCGen.Effects.CodeSeparated.readOnly rfl,
        trivial, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Events are actual `Trace.atomic` payloads derived by shared soundness,
not an event list assumed as an execution premise or guessed from final RAM. -/
theorem runs (choices : ChoiceStream FlagChoices) :
    ∃ result events, runWith choices 3 initial = .ok result ∧ Post result events ∧
      result.instructions ≤ 3 ∧
      VCGen.Effects.Trace bytes 0x4000 (separatedPolicy bytes) choices initial result events :=
  VCGen.Effects.run_sound valid (separatedFrame bytes) code rfl generated choices

/-- A swapped event contract disagrees with the first actual production atomic
step, even though it contains the same two payloads and final memory value. -/
theorem reversed_events_rejected :
    ¬ VCGen.Effects.wp graph 0x4000 (separatedPolicy bytes) 3 entry initial
      (fun _ events => events = [⟨0x8000, 1, 43⟩, ⟨0x8000, 42, 1⟩]) := by
  intro vc
  obtain ⟨_, _, _, reversed, _, trace⟩ :=
    VCGen.Effects.run_sound valid (separatedFrame bytes) code rfl vc
      (fun _ => FlagChoices.uniform false)
  cases trace with
  | ret _ _ _ actual _ _ _ => cases actual
  | next _ _ _ actual _ _ _ => cases actual
  | atomic _ _ _ actual _ _ _ =>
    cases actual
    have wrong : (42 : BitVec 32) = 1 :=
      congrArg AtomicEvent.before (List.cons.inj reversed).1
    exact (by decide +kernel : (42 : BitVec 32) ≠ 1) wrong

end AtomicPair

namespace SameValue

def initial : State := entryState StoreLoad.bytes 0x8000 42

/-- Separately chosen effect policy: writes are forbidden regardless of
whether their resulting memory equals their input memory. -/
def denyWrites : VCGen.Effects.Policy where
  Current := fun _ => True
  AllowedRead := fun _ _ => True
  AllowedEffect := fun _ instruction _ => CFG.readOnly instruction = true

private theorem address_of_delta {address : Word} {offset : Nat}
    (small : offset < 2 ^ 64) (delta : (address - 0x8000).toNat = offset) :
    address = 0x8000 + BitVec.ofNat 64 offset := by
  have difference : address - 0x8000 = BitVec.ofNat 64 offset := by
    apply BitVec.eq_of_toNat_eq
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] using delta
  simpa only [BitVec.add_comm] using BitVec.sub_eq_iff_eq_add.mp difference

private theorem same_memory :
    writeDWordUnchecked initial.memory 0x8000 42 = initial.memory := by
  have reads : storedDWordByte initial.memory 0x8000 42 = initial.memory.read := by
    funext address
    unfold storedDWordByte
    split
    · rename_i delta
      rw [address_of_delta (by decide +kernel) delta]
      rfl
    · rename_i delta
      rw [address_of_delta (by decide +kernel) delta]
      rfl
    · rename_i delta
      rw [address_of_delta (by decide +kernel) delta]
      rfl
    · rename_i delta
      rw [address_of_delta (by decide +kernel) delta]
      rfl
    · rfl
  unfold writeDWordUnchecked
  rw [reads]

/-- Physical write permission is present and the actual store has write intent,
yet its complete successor memory is extensionally equal to the input memory. -/
theorem actual_same_value_store (choices : FlagChoices) :
    ∃ observation after,
      CodeAt initial.memory 0x4000 StoreLoad.bytes ∧
      Sequential.decodeAt initial = .ok (.legacy .storeEsiRdi) ∧
      (Sequential.Instruction.legacy .storeEsiRdi).storeIntent initial = some (0x8000, 42) ∧
      stepWith choices initial = .ok observation ∧ observation.result = .next after ∧
      after.memory = initial.memory ∧ after.rip = 0x4002 := by
  refine ⟨_, _, initial_code StoreLoad.bytes (by decide +kernel) 0x8000 42,
    rfl, rfl, rfl, rfl, ?_, rfl⟩
  exact same_memory

/-- Denial is checked on the actual instruction, before any postcondition.
No fuel or postcondition can authorize this same-value write. -/
theorem denied_same_value_store (fuel : Nat) (Post : VCGen.Effects.Contract) :
    ¬ VCGen.Effects.wp StoreLoad.graph 0x4000 denyWrites fuel
      StoreLoad.entry initial Post := by
  cases fuel with
  | zero => exact id
  | succ fuel =>
    intro vc
    have denied : (false : Bool) = true :=
      (vc.2 (FlagChoices.uniform false)).2.1
    cases denied

end SameValue

namespace TextOverlap

/-- The store targets the selected executable RET byte. That byte is deliberately
writable, so the production executor can perform the write. -/
def initial : State := entryState StoreLoad.bytes 0x4004

theorem separated_effect_rejected :
    ¬ VCGen.Effects.CodeSeparated StoreLoad.bytes 0x4000 initial
      (.legacy .storeEsiRdi) := by
  intro allowed
  cases allowed with
  | readOnly permitted => cases permitted
  | @store32 _ address _ intent disjoint =>
    have sameAddress : (0x4004 : Word) = address :=
      congrArg Prod.fst (Option.some.inj intent)
    have overlap := disjoint 4 (by decide +kernel)
    rw [← sameAddress] at overlap
    change 4 ≤ 0 at overlap
    omega
  | store64 intent _ => cases intent

/-- Structural validity and a real successful store do not preserve text.
The production write changes the protected byte from RET to the literal 0x44. -/
theorem actual_text_write (choices : FlagChoices) :
    ∃ observation after,
      CodeAt initial.memory 0x4000 StoreLoad.bytes ∧
      Sequential.decodeAt initial = .ok (.legacy .storeEsiRdi) ∧
      stepWith choices initial = .ok observation ∧ observation.result = .next after ∧
      initial.memory.executable 0x4004 = true ∧
      after.memory.read 0x4004 = some 0x44 ∧
      ¬ CodeAt after.memory 0x4000 StoreLoad.bytes := by
  refine ⟨_, _, initial_code StoreLoad.bytes (by decide +kernel) 0x4004 0x11223344,
    rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro retained
  have oldRet := retained.2 4 0xc3 rfl
  change (Except.ok (0x44 : Byte) : Except Error Byte) = .ok 0xc3 at oldRet
  exact (by decide +kernel : (0x44 : Byte) ≠ 0xc3) (Except.ok.inj oldRet)

/-- The generic separation VC rejects the actual overlapping footprint for
any fuel/postcondition, even though the initial structural graph is valid. -/
theorem overlapping_store_rejected (fuel : Nat) (Post : VCGen.Effects.Contract) :
    ¬ VCGen.Effects.wp StoreLoad.graph 0x4000 (separatedPolicy StoreLoad.bytes)
      fuel StoreLoad.entry initial Post := by
  cases fuel with
  | zero => exact id
  | succ fuel =>
    intro vc
    exact separated_effect_rejected (vc.2 (FlagChoices.uniform false)).2.1

end TextOverlap
end EDSL.Tests.EffectVCGen

#print axioms EDSL.Tests.EffectVCGen.StoreLoad.valid
#print axioms EDSL.Tests.EffectVCGen.StoreLoad.generated
#print axioms EDSL.Tests.EffectVCGen.StoreLoad.runs
#print axioms EDSL.Tests.EffectVCGen.AtomicPair.valid
#print axioms EDSL.Tests.EffectVCGen.AtomicPair.generated
#print axioms EDSL.Tests.EffectVCGen.AtomicPair.runs
#print axioms EDSL.Tests.EffectVCGen.AtomicPair.reversed_events_rejected
#print axioms EDSL.Tests.EffectVCGen.SameValue.actual_same_value_store
#print axioms EDSL.Tests.EffectVCGen.SameValue.denied_same_value_store
#print axioms EDSL.Tests.EffectVCGen.TextOverlap.separated_effect_rejected
#print axioms EDSL.Tests.EffectVCGen.TextOverlap.actual_text_write
#print axioms EDSL.Tests.EffectVCGen.TextOverlap.overlapping_store_rejected
#audit_edsl
