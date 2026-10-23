/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.Effects.Reflection
import EDSL.X86.VCGen.Effects.SeparationCheck

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
A combined entry point for bounded programs using the shared code-separation
policy. It checks the proposed graph against the selected bytes, the actual
initial executable mapping, entry RIP, and generated effect obligations.
Independent current-state, read and result/event predicates remain client inputs.
The policy's code frame is proved once by the shared adapter.

This certifies sequential model execution only. The separation policy protects
the selected code, without supplying current OS authority, caller-slot ownership,
a scheduler, physical refinement, or additional corpus coverage.
-/

namespace EDSL.X86.VCGen.Effects
open Sequential

/-- Reuse the finite separation decision as the effect-policy decision. -/
def decidableSeparatedWP (bytes : List Byte) (graph : CFG.Graph) (base : Word)
    (Current : State → Prop) (AllowedRead : State → Read → Prop)
    (decCurrent : ∀ state, Decidable (Current state))
    (decReads : ∀ state read, Decidable (AllowedRead state read))
    (fuel : Nat) (node : graph.Index) (initial : State) (Post : Contract)
    (decPost : ∀ result events, Decidable (Post result events)) :
    Decidable (wp graph base (codeSeparatedPolicy bytes base Current AllowedRead)
      fuel node initial Post) :=
  decidableWP graph base (codeSeparatedPolicy bytes base Current AllowedRead)
    decCurrent decReads (fun state instruction _ =>
      decidableCodeSeparated bytes base state instruction)
    fuel node initial Post decPost

/-- All code/graph/entry checks use current inputs; they are not inferred from
metadata or from a successful symbolic execution of proposed instructions. -/
def certifySeparatedWith (profile : CFG.Profile) (bytes : List Byte)
    (graph : CFG.Graph) (base : Word)
    (Current : State → Prop) (AllowedRead : State → Read → Prop)
    (decCurrent : ∀ state, Decidable (Current state))
    (decReads : ∀ state read, Decidable (AllowedRead state read))
    (fuel : Nat) (node : graph.Index) (initial : State) (Post : Contract)
    (decPost : ∀ result events, Decidable (Post result events)) : Bool :=
  letI := decidableSeparatedWP bytes graph base Current AllowedRead decCurrent decReads
    fuel node initial Post decPost
  CFG.Structural.checkWith profile bytes graph && ELF.checkCode initial.memory base bytes &&
    decide (initial.rip = base + BitVec.ofNat 64 (graph.node node).offset) &&
    check graph base (codeSeparatedPolicy bytes base Current AllowedRead) fuel node initial Post

/-- Combined acceptance constructs actual returning execution for any full flag
stream, the independent postcondition, ordered atomic trace and instruction bound.
No extra executable-mapping, entry-PC or code-frame premise is assumed. -/
theorem certifySeparatedWith_sound (profile : CFG.Profile) (bytes : List Byte)
    (graph : CFG.Graph) (base : Word)
    (Current : State → Prop) (AllowedRead : State → Read → Prop)
    (decCurrent : ∀ state, Decidable (Current state))
    (decReads : ∀ state read, Decidable (AllowedRead state read))
    (fuel : Nat) (node : graph.Index) (initial : State) (Post : Contract)
    (decPost : ∀ result events, Decidable (Post result events))
    (accepted : certifySeparatedWith profile bytes graph base Current AllowedRead
      decCurrent decReads fuel node initial Post decPost = true)
    (choices : ChoiceStream FlagChoices) :
    ∃ result events, runWith choices fuel initial = .ok result ∧ Post result events ∧
      result.instructions ≤ fuel ∧
      Trace bytes base (codeSeparatedPolicy bytes base Current AllowedRead)
        choices initial result events := by
  letI := decidableSeparatedWP bytes graph base Current AllowedRead decCurrent decReads
    fuel node initial Post decPost
  have parts : CFG.Structural.checkWith profile bytes graph = true ∧
      ELF.checkCode initial.memory base bytes = true ∧
      initial.rip = base + BitVec.ofNat 64 (graph.node node).offset ∧
      check graph base (codeSeparatedPolicy bytes base Current AllowedRead)
        fuel node initial Post = true := by
    simpa only [certifySeparatedWith, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using accepted
  exact checked_run_sound (CFG.Structural.checkWith_sound parts.1)
    (codeSeparatedPolicy_codeFrame bytes base Current AllowedRead)
    (ELF.checkCode_sound _ _ _ parts.2.1) parts.2.2.1 parts.2.2.2 choices

/-- The unchanged default static caps; larger inputs require an explicit profile. -/
def certifySeparated (bytes : List Byte) (graph : CFG.Graph) (base : Word)
    (Current : State → Prop) (AllowedRead : State → Read → Prop)
    (decCurrent : ∀ state, Decidable (Current state))
    (decReads : ∀ state read, Decidable (AllowedRead state read))
    (fuel : Nat) (node : graph.Index) (initial : State) (Post : Contract)
    (decPost : ∀ result events, Decidable (Post result events)) : Bool :=
  certifySeparatedWith CFG.defaultProfile bytes graph base Current AllowedRead decCurrent decReads
    fuel node initial Post decPost

theorem certifySeparated_sound (bytes : List Byte) (graph : CFG.Graph) (base : Word)
    (Current : State → Prop) (AllowedRead : State → Read → Prop)
    (decCurrent : ∀ state, Decidable (Current state))
    (decReads : ∀ state read, Decidable (AllowedRead state read))
    (fuel : Nat) (node : graph.Index) (initial : State) (Post : Contract)
    (decPost : ∀ result events, Decidable (Post result events))
    (accepted : certifySeparated bytes graph base Current AllowedRead decCurrent decReads
      fuel node initial Post decPost = true)
    (choices : ChoiceStream FlagChoices) :
    ∃ result events, runWith choices fuel initial = .ok result ∧ Post result events ∧
      result.instructions ≤ fuel ∧
      Trace bytes base (codeSeparatedPolicy bytes base Current AllowedRead)
        choices initial result events :=
  certifySeparatedWith_sound CFG.defaultProfile bytes graph base Current AllowedRead decCurrent
    decReads fuel node initial Post decPost accepted choices

#print axioms decidableSeparatedWP
#print axioms certifySeparatedWith
#print axioms certifySeparatedWith_sound
#print axioms certifySeparated
#print axioms certifySeparated_sound

end EDSL.X86.VCGen.Effects
#audit_edsl
