/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.PureCall.Resources
import EDSL.X86.VCGen.Policy
import EDSL.X86.VCGen.CutpointPolicy

set_option warningAsError true

namespace EDSL.X86.VCGen
open Sequential

variable {profile : CFG.Profile}

/-- Generated obligations retain complete current RAM and permit only the
original caller slot. Actual read success comes from the production step. -/
def PureCallAllowed (initial before : State) (read : Read) : Prop :=
  before.memory = initial.memory ∧ EDSL.PureCall.RawRead initial read

/-- Universal production WP evidence implies the fixed scalar call contract
and its every-prefix current-resource policy, for every AF stream. The optional
Evidence projection is proof evidence, separate from mathematical spec and
admission. Trusted registration fixes spec; submissions cannot select it.

CFG validity binds the complete selected bytes. Initial executable RAM and PC
come from Pre, not an assumed future run. This establishes no native loading,
physical refinement, certificate/score or additional target feature support. -/
theorem pureCall_semantics_of_generated
    (spec : EDSL.PureCall.Spec) (bytes : List Byte) (graph : CFG.Graph)
    (valid : CFG.Valid bytes graph profile) (entry : graph.Index)
    (entryOffset : (graph.node entry).offset = 0) (fuel : Nat)
    (Evidence : EDSL.PureCall.Invocation spec → State → Result → Prop)
    (project : ∀ input initial result, Evidence input initial result →
      EDSL.PureCall.Post spec input initial result.state)
    (generated : ∀ input initial, EDSL.PureCall.Pre spec bytes input initial →
      wp graph initial.rip (PureCallAllowed initial) fuel entry initial
        (Evidence input initial)) :
    Grading.ReadOnlySemanticClaim (EDSL.PureCall.readOnlyTask spec) bytes := by
  apply EDSL.PureCall.semantics_of_raw
  intro input initial pre
  have pc : initial.rip = initial.rip + BitVec.ofNat 64 (graph.node entry).offset := by
    simp [entryOffset]
  have vc := generated input initial pre
  constructor
  · intro choices
    obtain ⟨result, execution, evidence, _, _⟩ := sound valid pre.code pc vc choices
    exact ⟨result, execution, project input initial result evidence⟩
  · exact (readOnly_policy_memory valid pre.code pc vc).mono
      (fun _ memory => memory) (fun _ _ allowed => allowed.2)

/-- Present scalar-call admission and generated sparse loop obligations imply
termination and every-prefix read authority. The loop invariant/rank are proof
evidence, never restrictions assuming a result or successful future execution.
The protected original return slot is the only permitted operand read. -/
theorem pureCall_raw_of_cutpoints
    (spec : EDSL.PureCall.Spec) (bytes : List Byte) (graph : CFG.Graph)
    (valid : CFG.Valid bytes graph profile)
    (generated : ∀ input initial, EDSL.PureCall.Pre spec bytes input initial →
      ∃ annotations : Cutpoints.Annotations bytes graph initial.rip
        (EDSL.PureCall.Post spec input initial)
        (fun _ read => EDSL.PureCall.RawRead initial read),
        annotations.Inv valid.entry initial) :
    ∀ input initial, EDSL.PureCall.Pre spec bytes input initial →
      Sequential.AllExecutions initial
        (fun result => EDSL.PureCall.Post spec input initial result.state) ∧
      EDSL.PureCall.RawPolicy initial := by
  intro input initial pre
  obtain ⟨annotations, admitted⟩ := generated input initial pre
  have binding : CFG.At bytes graph initial.rip valid.entry initial := by
    refine ⟨pre.code, ?_⟩
    simp [valid.entry_offset]
  obtain ⟨executions, policy⟩ :=
    annotations.total_policy valid valid.entry_cutpoint binding admitted
  refine ⟨?_, policy⟩
  intro choices
  obtain ⟨result, execution, post, _⟩ := executions choices
  exact ⟨result, execution, post⟩

/-- The generic scalar resource bridge lifts the same sparse loop proof to
every admitted loaded call, retaining current caller/code loans and complete
RAM/ABI frames. Native loading, hardware correspondence and interference
control remain the existing sequential target assumptions. -/
theorem pureCall_semantics_of_cutpoints
    (spec : EDSL.PureCall.Spec) (bytes : List Byte) (graph : CFG.Graph)
    (valid : CFG.Valid bytes graph profile)
    (generated : ∀ input initial, EDSL.PureCall.Pre spec bytes input initial →
      ∃ annotations : Cutpoints.Annotations bytes graph initial.rip
        (EDSL.PureCall.Post spec input initial)
        (fun _ read => EDSL.PureCall.RawRead initial read),
        annotations.Inv valid.entry initial) :
    Grading.ReadOnlySemanticClaim (EDSL.PureCall.readOnlyTask spec) bytes :=
  EDSL.PureCall.semantics_of_raw
    (pureCall_raw_of_cutpoints spec bytes graph valid generated)

end EDSL.X86.VCGen
