/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.Effects.Checked
import tests.EffectVCGen

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.Tests.EffectChecked
open X86 Sequential
open EDSL.Tests.EffectVCGen

private def Current (_ : State) : Prop := True
private def AllowedRead (_ : State) (_ : Read) : Prop := True
private def decCurrent (state : State) : Decidable (Current state) := isTrue trivial
private def decReads (state : State) (read : Read) : Decidable (AllowedRead state read) :=
  isTrue trivial

private def decStorePost (result : Result) (events : List AtomicEvent) :
    Decidable (StoreLoad.Post result events) := by
  unfold StoreLoad.Post
  infer_instance

private def certifyStore (initial : State) : Bool :=
  VCGen.Effects.certifySeparated StoreLoad.bytes StoreLoad.graph 0x4000 Current AllowedRead
    decCurrent decReads 3 StoreLoad.entry initial StoreLoad.Post decStorePost

/-- Computed acceptance authenticates actual bytes as well as the independent
literal result/read/event contract, without a per-client CodeAt/frame proof. -/
theorem store_accepted : certifyStore StoreLoad.initial = true := by decide +kernel

theorem store_runs (choices : ChoiceStream FlagChoices) :
    ∃ result events, runWith choices 3 StoreLoad.initial = .ok result ∧
      StoreLoad.Post result events ∧ result.instructions ≤ 3 ∧
      VCGen.Effects.Trace StoreLoad.bytes 0x4000
        (VCGen.Effects.codeSeparatedPolicy StoreLoad.bytes 0x4000 Current AllowedRead)
        choices StoreLoad.initial result events :=
  VCGen.Effects.certifySeparated_sound StoreLoad.bytes StoreLoad.graph 0x4000 Current AllowedRead
    decCurrent decReads 3 StoreLoad.entry StoreLoad.initial StoreLoad.Post decStorePost
    store_accepted choices

private def altered : State :=
  { StoreLoad.initial with
    memory :=
      { StoreLoad.initial.memory with
        read := fun address =>
          if address = 0x4000 then some 0x90
          else StoreLoad.initial.memory.read address } }

private def rawStore (initial : State) : Bool :=
  letI := VCGen.Effects.decidableSeparatedWP StoreLoad.bytes StoreLoad.graph 0x4000
    Current AllowedRead decCurrent decReads 3 StoreLoad.entry initial StoreLoad.Post decStorePost
  VCGen.Effects.check StoreLoad.graph 0x4000
    (VCGen.Effects.codeSeparatedPolicy StoreLoad.bytes 0x4000 Current AllowedRead)
    3 StoreLoad.entry initial StoreLoad.Post

/-- Symbolic execution of the proposed instructions still meets its post when
only actual text is changed. The combined checker must reject the RAM mismatch. -/
theorem changed_text_rejected :
    rawStore altered = true ∧ ELF.checkCode altered.memory 0x4000 StoreLoad.bytes = false ∧
      certifyStore altered = false := by decide +kernel

theorem changed_text_is_nop : Sequential.decodeAt altered = .ok (.nop .one) := rfl

namespace Entry
private def bytes : List Byte := [0xc3]
private def graph : CFG.Graph := ⟨[⟨0, .legacy .ret, true, 1⟩], 1⟩
private def node : graph.Index := ⟨0, by decide +kernel⟩

-- The return slot is readable and valid. Only 0x4000 is executable text.
private def initial : State := { StoreLoad.initial with
  memory := { StoreLoad.initial.memory with
    read := fun address => if address = 0x4000 then some 0xc3
      else StoreLoad.initial.memory.read address
    executable := fun address => decide (address = 0x4000) }
  rip := 0x4001 }

private def Post (result : Result) (events : List AtomicEvent) : Prop :=
  result.state.rip = 0x5000 ∧ result.state.registers .rsp = 0x9008 ∧
    result.instructions = 1 ∧ events = []

private def decPost (result : Result) (events : List AtomicEvent) :
    Decidable (Post result events) := by unfold Post; infer_instance

private def raw : Bool :=
  letI := VCGen.Effects.decidableSeparatedWP bytes graph 0x4000 Current AllowedRead
    decCurrent decReads 1 node initial Post decPost
  VCGen.Effects.check graph 0x4000
    (VCGen.Effects.codeSeparatedPolicy bytes 0x4000 Current AllowedRead) 1 node initial Post

/-- RET's executor ignores its incoming RIP, so a WP alone can accept this
state. The combined checker must retain its separate entry-PC obligation. -/
theorem wrong_entry_rejected :
    CFG.Structural.check bytes graph = true ∧ ELF.checkCode initial.memory 0x4000 bytes = true ∧
      raw = true ∧ VCGen.Effects.certifySeparated bytes graph 0x4000 Current AllowedRead
        decCurrent decReads 1 node initial Post decPost = false := by decide +kernel

theorem actual_entry_fault : Sequential.decodeAt initial =
    .error (.inaccessibleInstruction 0x4001) := rfl
end Entry

end EDSL.Tests.EffectChecked
#print axioms EDSL.Tests.EffectChecked.store_accepted
#print axioms EDSL.Tests.EffectChecked.store_runs
#print axioms EDSL.Tests.EffectChecked.changed_text_rejected
#print axioms EDSL.Tests.EffectChecked.changed_text_is_nop
#print axioms EDSL.Tests.EffectChecked.Entry.wrong_entry_rejected
#print axioms EDSL.Tests.EffectChecked.Entry.actual_entry_fault
#audit_edsl
