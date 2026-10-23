/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.Effects.SeparationCheck
import EDSL.X86.VCGen.Effects.Reflection
import tests.EffectVCGen

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Independent literal machine-result and ordered-event contracts checked through
the new finite effect-WP reflection API. All WP decisions below are built by
`Effects.decidableWP`, with explicit Current/read/effect/Post deciders; effect
separation is decided by `Effects.decidableCodeSeparated`. No existing generated
WP proof is used to manufacture a decision.

The public StoreLoad/AtomicPair bytes, graphs, initial states and literal Posts
are shared with EffectVCGen. Initial code binding is proved separately from an
actual mapping. Acceptance is connected to the production execution by the new
`checked_run_sound`, structural validation, the original entry PC and the generic
separation frame. No future-memory or future-CodeAt premise is assumed.

These are bounded sequential controls. Footprint separation grants neither
writability nor OS authority; no concurrency, TSO, linearizability, hardware or
corpus claim follows from these tests.
-/

namespace EDSL.Tests.EffectReflection
open X86 Sequential
open X86.VCGen

private abbrev separatedPolicy (bytes : List Byte)
    (Current : State → Prop := fun _ => True)
    (AllowedRead : State → Read → Prop := fun _ _ => True) : Effects.Policy :=
  Effects.codeSeparatedPolicy bytes 0x4000 Current AllowedRead

private instance separatedDecision (bytes : List Byte) (graph : CFG.Graph)
    (Current : State → Prop) (AllowedRead : State → Read → Prop)
    (fuel : Nat) (node : graph.Index) (initial : State) (Post : Effects.Contract)
    [decCurrent : ∀ state, Decidable (Current state)]
    [decReads : ∀ state read, Decidable (AllowedRead state read)]
    [decPost : ∀ result events, Decidable (Post result events)] :
    Decidable (Effects.wp graph 0x4000 (separatedPolicy bytes Current AllowedRead)
      fuel node initial Post) :=
  Effects.decidableWP graph 0x4000 (separatedPolicy bytes Current AllowedRead)
    decCurrent decReads
    (fun before instruction _ =>
      Effects.decidableCodeSeparated bytes 0x4000 before instruction)
    fuel node initial Post decPost

/- An actual initial mapping, matching the shared public states by reduction.
The code region has priority even when a deliberately writable target overlaps
it. The data word is 42; the original return slot contains 0x5000. -/
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

/- Adapted from the explicit canonical/execute/read mapping argument in
EffectVCGen; it proves only the initially mapped executable bytes. -/
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

namespace StoreLoad
open EffectVCGen.StoreLoad (bytes graph entry initial Post valid)

private instance (result : Result) (events : List AtomicEvent) :
    Decidable (Post result events) := by
  unfold EffectVCGen.StoreLoad.Post
  infer_instance

/-- Checks the literal 0x11223344 load, four little-endian bytes, 0x5000
return, RSP 0x9008, cost three, ordered data/stack reads and no atomic events. -/
theorem accepts :
    Effects.check graph 0x4000 (separatedPolicy bytes) 3 entry initial Post = true := by
  decide +kernel

/-- Computed acceptance supplies an actual run and its actual ordered trace. -/
theorem checked_run (choices : ChoiceStream FlagChoices) :
    ∃ result events, runWith choices 3 initial = .ok result ∧ Post result events ∧
      result.instructions ≤ 3 ∧
      Effects.Trace bytes 0x4000 (separatedPolicy bytes) choices initial result events :=
  Effects.checked_run_sound (node := entry) valid
    (Effects.codeSeparatedPolicy_codeFrame bytes 0x4000 (fun _ => True) (fun _ _ => True))
    (initial_code bytes (by decide +kernel) 0x8000 0x11223344) rfl accepts choices

private def onlyData (_state : State) (read : Read) : Prop := read.kind = .data

private instance (state : State) (read : Read) : Decidable (onlyData state read) :=
  inferInstanceAs (Decidable (read.kind = .data))

/-- The load's real data read is allowed; the readable RET slot is denied by
the independent read policy. Physical readability alone cannot authorize it. -/
theorem denies_return_read :
    Effects.check graph 0x4000 (separatedPolicy bytes (fun _ => True) onlyData)
      3 entry initial Post = false := by
  decide +kernel

private def stackUnpopped (state : State) : Prop := state.registers .rsp = 0x9000

private instance (state : State) : Decidable (stackUnpopped state) :=
  inferInstanceAs (Decidable (state.registers .rsp = 0x9000))

/-- Current holds before all three instructions, including RET. Only the
final state violates it, because the actual return pops eight stack bytes. -/
theorem denies_final_current :
    Effects.check graph 0x4000 (separatedPolicy bytes stackUnpopped)
      3 entry initial Post = false := by
  decide +kernel

private def unwritable : State :=
  { initial with memory := { initial.memory with writable := fun _ => false } }

/-- A successful separation check supplies no production write permission. -/
theorem separation_is_not_writability :
    Effects.checkCodeSeparated bytes 0x4000 unwritable (.legacy .storeEsiRdi) = true ∧
      executeWith unwritable (.legacy .storeEsiRdi) (FlagChoices.uniform false) =
        .error (.writeDenied 0x8000) := by
  constructor
  · decide +kernel
  · rfl

end StoreLoad

namespace AtomicPair
open EffectVCGen.AtomicPair (bytes graph entry initial Post valid)

private instance (result : Result) (events : List AtomicEvent) :
    Decidable (Post result events) := by
  unfold EffectVCGen.AtomicPair.Post
  infer_instance

/-- XCHG observes 42 and stores 1; XADD observes that 1 and stores 43.
The exact two events, return value 1, final bytes, reads and cost are checked. -/
theorem accepts :
    Effects.check graph 0x4000 (separatedPolicy bytes) 3 entry initial Post = true := by
  decide +kernel

theorem checked_run (choices : ChoiceStream FlagChoices) :
    ∃ result events, runWith choices 3 initial = .ok result ∧ Post result events ∧
      result.instructions ≤ 3 ∧
      Effects.Trace bytes 0x4000 (separatedPolicy bytes) choices initial result events :=
  Effects.checked_run_sound (node := entry) valid
    (Effects.codeSeparatedPolicy_codeFrame bytes 0x4000 (fun _ => True) (fun _ _ => True))
    (initial_code bytes (by decide +kernel) 0x8000 0x11223344) rfl accepts choices

private def finalResult (result : Result) : Prop :=
  result.state.registers .rax = 1 ∧ result.state.memory.read 0x8000 = some 0x2b ∧
  result.state.rip = 0x5000 ∧ result.state.registers .rsp = 0x9008 ∧
  result.instructions = 3 ∧
  result.reads = [⟨.data, 0x8000, 4⟩, ⟨.data, 0x8000, 4⟩, ⟨.stack, 0x9000, 8⟩]

private def reversed (result : Result) (events : List AtomicEvent) : Prop :=
  finalResult result ∧ events = [⟨0x8000, 1, 43⟩, ⟨0x8000, 42, 1⟩]

private def dropped (result : Result) (events : List AtomicEvent) : Prop :=
  finalResult result ∧ events = [⟨0x8000, 1, 43⟩]

private instance (result : Result) (events : List AtomicEvent) :
    Decidable (reversed result events) := by
  unfold reversed finalResult
  infer_instance

private instance (result : Result) (events : List AtomicEvent) :
    Decidable (dropped result events) := by
  unfold dropped finalResult
  infer_instance

/-- The same literal final result cannot excuse a reversed event history. -/
theorem rejects_reversed_events :
    Effects.check graph 0x4000 (separatedPolicy bytes) 3 entry initial reversed = false := by
  decide +kernel

/-- Keeping only the last event would hide the exchange that supplied XADD. -/
theorem rejects_dropped_event :
    Effects.check graph 0x4000 (separatedPolicy bytes) 3 entry initial dropped = false := by
  decide +kernel

end AtomicPair

namespace SameValue
open EffectVCGen.StoreLoad (bytes graph entry)

def initial : State := entryState bytes 0x8000 42

def Post (result : Result) (events : List AtomicEvent) : Prop :=
  result.state.registers .rax = 42 ∧
  result.state.memory.read 0x8000 = some 0x2a ∧
  result.state.memory.read 0x8001 = some 0 ∧
  result.state.memory.read 0x8002 = some 0 ∧
  result.state.memory.read 0x8003 = some 0 ∧
  result.state.rip = 0x5000 ∧ result.state.registers .rsp = 0x9008 ∧
  result.instructions = 3 ∧
  result.reads = [⟨.data, 0x8000, 4⟩, ⟨.stack, 0x9000, 8⟩] ∧ events = []

private instance (result : Result) (events : List AtomicEvent) :
    Decidable (Post result events) := by
  unfold Post
  infer_instance

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

/-- The real executor succeeds with write permission and complete successor
memory equality; this equality is proved, never supplied as a policy premise. -/
theorem actual_same_value_store (choices : FlagChoices) :
    ∃ observation after,
      CodeAt initial.memory 0x4000 bytes ∧
      executeWith initial (.legacy .storeEsiRdi) choices = .ok observation ∧
      observation.result = .next after ∧ after.memory = initial.memory ∧
      after.rip = 0x4002 := by
  refine ⟨_, _, initial_code bytes (by decide +kernel) 0x8000 42,
    rfl, rfl, ?_, rfl⟩
  exact same_memory

theorem permitted_accepts :
    Effects.check graph 0x4000 (separatedPolicy bytes) 3 entry initial Post = true := by
  decide +kernel

private def denyWrites : Effects.Policy where
  Current := fun _ => True
  AllowedRead := fun _ _ => True
  AllowedEffect := fun _ instruction _ => CFG.readOnly instruction = true

private instance :
    Decidable (Effects.wp graph 0x4000 denyWrites 3 entry initial Post) :=
  Effects.decidableWP graph 0x4000 denyWrites
    (fun _ => inferInstanceAs (Decidable True))
    (fun _ _ => inferInstanceAs (Decidable True))
    (fun _ instruction _ =>
      inferInstanceAs (Decidable (CFG.readOnly instruction = true)))
    3 entry initial Post (fun _ _ => inferInstance)

/-- The baseline checker above accepts exactly this literal execution, but
read-only authorization must reject its actual same-value store intent. -/
theorem denied_rejects :
    Effects.check graph 0x4000 denyWrites 3 entry initial Post = false := by
  decide +kernel

end SameValue

namespace TextOverlap
open EffectVCGen.StoreLoad (bytes graph entry)

def initial : State := entryState bytes 0x4004

private def Post (result : Result) (events : List AtomicEvent) : Prop :=
  result.state.registers .rax = 0x11223344 ∧
  result.state.memory.read 0x4004 = some 0x44 ∧
  result.state.rip = 0x5000 ∧ result.state.registers .rsp = 0x9008 ∧
  result.instructions = 3 ∧
  result.reads = [⟨.data, 0x4004, 4⟩, ⟨.stack, 0x9000, 8⟩] ∧ events = []

private instance (result : Result) (events : List AtomicEvent) :
    Decidable (Post result events) := by
  unfold Post
  infer_instance

/-- The selected final RET byte is both executable and writable. Production
execution really stores 0x44 there; policy rejection is not a permission fault. -/
theorem actual_writable_text_store (choices : FlagChoices) :
    ∃ observation after,
      CodeAt initial.memory 0x4000 bytes ∧
      initial.memory.executable 0x4004 = true ∧
      initial.memory.writable 0x4004 = true ∧
      initial.memory.read 0x4004 = some 0xc3 ∧
      executeWith initial (.legacy .storeEsiRdi) choices = .ok observation ∧
      observation.result = .next after ∧ after.memory.read 0x4004 = some 0x44 := by
  exact ⟨_, _, initial_code bytes (by decide +kernel) 0x4004 0x11223344,
    rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem footprint_rejects :
    Effects.checkCodeSeparated bytes 0x4000 initial (.legacy .storeEsiRdi) = false := by
  decide +kernel

/-- Without effect denial, these literal result/read obligations would agree
with graph-directed execution. The actual overlapping footprint is forbidden. -/
theorem checker_rejects :
    Effects.check graph 0x4000 (separatedPolicy bytes) 3 entry initial Post = false := by
  decide +kernel

end TextOverlap

namespace VectorBranch

/- Owned copy of the literal branch fixture, with no import of its private
names or its old proofs. Offsets: 0 IMUL; 4 JZ20; 6 JP14; 8 MOV0; 13 RET;
14 MOV1; 19 RET; 20 JP28; 22 MOV2; 27 RET; 28 MOV3; 33 RET. -/
def bytes : List Byte :=
  [0x48,0x0f,0xaf,0xc6,
   0x74,0x0e, 0x7a,0x06,
   0xb8,0,0,0,0, 0xc3,
   0xb8,1,0,0,0, 0xc3,
   0x7a,0x06,
   0xb8,2,0,0,0, 0xc3,
   0xb8,3,0,0,0, 0xc3]

def graph : CFG.Graph :=
  ⟨[⟨0,.imulReg64 .rax .rsi,true,12⟩,
    ⟨4,.je 0x0e,false,11⟩,
    ⟨6,.jcc .parity 0x06,false,10⟩,
    ⟨8,.legacy (.mov32 .rax 0),false,9⟩,
    ⟨13,.legacy .ret,false,8⟩,
    ⟨14,.legacy (.mov32 .rax 1),false,7⟩,
    ⟨19,.legacy .ret,false,6⟩,
    ⟨20,.jcc .parity 0x06,false,5⟩,
    ⟨22,.legacy (.mov32 .rax 2),false,4⟩,
    ⟨27,.legacy .ret,false,3⟩,
    ⟨28,.legacy (.mov32 .rax 3),false,2⟩,
    ⟨33,.legacy .ret,false,1⟩],12⟩

abbrev entry : graph.Index := ⟨0, by decide +kernel⟩

def initial : State where
  registers register := match register with
    | .rax => 3
    | .rsi => 5
    | .rsp => 0x9000
    | _ => 0
  rip := 0x4000
  flags := 0x202
  memory := memory bytes 0x8000

theorem structurally_valid : CFG.Structural.Valid bytes graph :=
  CFG.Structural.check_sound (by decide +kernel)

private def returnContract (result : Result) (events : List AtomicEvent) : Prop :=
  result.state.registers .rsp = 0x9008 ∧ result.state.rip = 0x5000 ∧
  result.instructions = 5 ∧ result.reads = [⟨.stack, 0x9000, 8⟩] ∧ events = []

def Post (result : Result) (events : List AtomicEvent) : Prop :=
  (result.state.registers .rax = 0 ∨ result.state.registers .rax = 1 ∨
    result.state.registers .rax = 2 ∨ result.state.registers .rax = 3) ∧
  returnContract result events

private def diagonal (result : Result) (events : List AtomicEvent) : Prop :=
  (result.state.registers .rax = 0 ∨ result.state.registers .rax = 3) ∧
  returnContract result events

private instance (result : Result) (events : List AtomicEvent) :
    Decidable (Post result events) := by
  unfold Post returnContract
  infer_instance

private instance (result : Result) (events : List AtomicEvent) :
    Decidable (diagonal result events) := by
  unfold diagonal returnContract
  infer_instance

private def vector (parity zero : Bool) : FlagChoices :=
  ⟨true, parity, false, zero, false, true⟩

private structure ReturnSnapshot where
  value : Word
  rsp : Word
  rip : Word
  flags : Word
  instructions : Nat
  reads : List Read
  deriving DecidableEq

/- A projection of the production run only; errors remain distinct from every
expected successful return. There is no alternate interpreter or event oracle. -/
private def snapshot (choices : FlagChoices) : Option ReturnSnapshot :=
  match runWith (fun _ => choices) 5 initial with
  | .error _ => none
  | .ok result => some ⟨result.state.registers .rax, result.state.registers .rsp,
      result.state.rip, result.state.flags, result.instructions, result.reads⟩

/-- The two cross valuations are real decoded executions, just like the two
diagonal valuations. Each literal result costs five and reads only the RET slot. -/
theorem actual_four_results :
    ([vector false false, vector true false, vector false true, vector true true] :
      List FlagChoices).map snapshot =
    [some ⟨0,0x9008,0x5000,0x202,5,[⟨.stack,0x9000,8⟩]⟩,
     some ⟨1,0x9008,0x5000,0x206,5,[⟨.stack,0x9000,8⟩]⟩,
     some ⟨2,0x9008,0x5000,0x242,5,[⟨.stack,0x9000,8⟩]⟩,
     some ⟨3,0x9008,0x5000,0x246,5,[⟨.stack,0x9000,8⟩]⟩] := by
  decide +kernel

/-- The new effect-WP checker enumerates all active IMUL flag choices. -/
theorem accepts_union :
    Effects.check graph 0x4000 (separatedPolicy bytes) 5 entry initial Post = true := by
  decide +kernel

/-- Enumerating only uniform vectors would wrongly accept {0,3}. Independent
PF/ZF choices force the new Boolean checker to reject that correlated contract. -/
theorem rejects_diagonal :
    Effects.check graph 0x4000 (separatedPolicy bytes) 5 entry initial diagonal = false := by
  decide +kernel

theorem checked_run (choices : ChoiceStream FlagChoices) :
    ∃ result events, runWith choices 5 initial = .ok result ∧ Post result events ∧
      result.instructions ≤ 5 ∧
      Effects.Trace bytes 0x4000 (separatedPolicy bytes) choices initial result events := by
  have code : CodeAt initial.memory 0x4000 bytes :=
    initial_code bytes (by decide +kernel) 0x8000 0x11223344
  have nodePC : initial.rip = 0x4000 + BitVec.ofNat 64 (graph.node entry).offset := rfl
  have frame : Effects.CodeFrame (separatedPolicy bytes) bytes 0x4000 :=
    Effects.codeSeparatedPolicy_codeFrame bytes 0x4000 (fun _ => True) (fun _ _ => True)
  exact Effects.checked_run_sound
    (bytes := bytes) (graph := graph) (profile := CFG.defaultProfile)
    (base := 0x4000) (policy := separatedPolicy bytes) (fuel := 5)
    (node := entry) (initial := initial) (Post := Post)
    structurally_valid frame code nodePC accepts_union choices

end VectorBranch

namespace Footprint

/-- Either the last write byte or the last selected-code byte can overlap. -/
theorem last_byte_overlap :
    Effects.checkCodeFootprint 4 0x1000 0x1003 1 = false ∧
    Effects.checkCodeFootprint 8 0x1000 0x1007 1 = false ∧
    Effects.checkCodeFootprint 4 0x1003 0x1000 4 = false := by
  decide +kernel

/-- Adjacency in either direction is separation; the first excluded byte is
exactly four/eight bytes after the store address, not one byte farther. -/
theorem exact_width_separation :
    Effects.checkCodeFootprint 4 0x1000 0x1004 2 = true ∧
    Effects.checkCodeFootprint 8 0x1000 0x1008 2 = true ∧
    Effects.checkCodeFootprint 4 0x1004 0x1000 4 = true := by
  decide +kernel

/-- A write starting at 2^64-2 wraps through bytes 0 and 1. Separately, the
selected three-byte window starting at 2^64-1 wraps through 0 and 1. -/
theorem modular_wrapping :
    Effects.checkCodeFootprint 4 0xfffffffffffffffe 0 2 = false ∧
    Effects.checkCodeFootprint 4 0xfffffffffffffffe 2 2 = true ∧
    Effects.checkCodeFootprint 4 0 0xffffffffffffffff 3 = false ∧
    Effects.checkCodeFootprint 4 2 0xffffffffffffffff 3 = true := by
  decide +kernel

/-- Empty selected text has no byte to overlap, even at the write address. -/
theorem empty_window (width : Nat) (address : Word) :
    Effects.checkCodeFootprint width address address 0 = true := by
  rfl

/-- Use actual prestate RDI and the production instruction classifiers. A
protected byte four bytes later permits a dword store but rejects a qword store. -/
theorem instruction_widths :
    Effects.checkCodeSeparated [0] 0x8004 EffectVCGen.StoreLoad.initial
      (.legacy .storeEsiRdi) = true ∧
    Effects.checkCodeSeparated [0] 0x8004 EffectVCGen.StoreLoad.initial
      (.storeMem64 (.base .rdi) .rsi) = false ∧
    Effects.checkCodeSeparated [0] 0x8008 EffectVCGen.StoreLoad.initial
      (.storeMem64 (.base .rdi) .rsi) = true := by
  decide +kernel

end Footprint
end EDSL.Tests.EffectReflection

#print axioms EDSL.Tests.EffectReflection.StoreLoad.accepts
#print axioms EDSL.Tests.EffectReflection.StoreLoad.checked_run
#print axioms EDSL.Tests.EffectReflection.StoreLoad.denies_return_read
#print axioms EDSL.Tests.EffectReflection.StoreLoad.denies_final_current
#print axioms EDSL.Tests.EffectReflection.StoreLoad.separation_is_not_writability
#print axioms EDSL.Tests.EffectReflection.AtomicPair.accepts
#print axioms EDSL.Tests.EffectReflection.AtomicPair.checked_run
#print axioms EDSL.Tests.EffectReflection.AtomicPair.rejects_reversed_events
#print axioms EDSL.Tests.EffectReflection.AtomicPair.rejects_dropped_event
#print axioms EDSL.Tests.EffectReflection.SameValue.actual_same_value_store
#print axioms EDSL.Tests.EffectReflection.SameValue.permitted_accepts
#print axioms EDSL.Tests.EffectReflection.SameValue.denied_rejects
#print axioms EDSL.Tests.EffectReflection.TextOverlap.actual_writable_text_store
#print axioms EDSL.Tests.EffectReflection.TextOverlap.footprint_rejects
#print axioms EDSL.Tests.EffectReflection.TextOverlap.checker_rejects
#print axioms EDSL.Tests.EffectReflection.VectorBranch.structurally_valid
#print axioms EDSL.Tests.EffectReflection.VectorBranch.actual_four_results
#print axioms EDSL.Tests.EffectReflection.VectorBranch.accepts_union
#print axioms EDSL.Tests.EffectReflection.VectorBranch.rejects_diagonal
#print axioms EDSL.Tests.EffectReflection.VectorBranch.checked_run
#print axioms EDSL.Tests.EffectReflection.Footprint.last_byte_overlap
#print axioms EDSL.Tests.EffectReflection.Footprint.exact_width_separation
#print axioms EDSL.Tests.EffectReflection.Footprint.modular_wrapping
#print axioms EDSL.Tests.EffectReflection.Footprint.empty_window
#print axioms EDSL.Tests.EffectReflection.Footprint.instruction_widths
#audit_edsl
