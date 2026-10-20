/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.CutpointPolicy
import EDSL.BufferCall.Resources

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.X86.VCGen
open Sequential

variable {profile : CFG.Profile}

/-- Present-only buffer admission plus generated cutpoint VCs proves raw call
semantics. Annotations and their initial invariant are proof evidence, outside
`Pre`; no successful evaluator run, fixed fuel or per-instruction client proof
is an admission premise. Empty buffers and zero dynamic ranks are retained. -/
theorem bufferCall_raw_of_cutpoints
    (spec : EDSL.BufferCall.Spec) (bytes : List Byte) (graph : CFG.Graph)
    (valid : CFG.Valid bytes graph profile)
    (generated : ∀ input initial, EDSL.BufferCall.Pre spec bytes input initial →
      ∃ annotations : Cutpoints.Annotations bytes graph initial.rip
        (EDSL.BufferCall.Post spec input initial)
        (fun _ read => EDSL.BufferCall.RawRead spec input initial read),
        annotations.Inv valid.entry initial) :
    ∀ input initial, EDSL.BufferCall.Pre spec bytes input initial →
      Sequential.AllExecutions initial
        (fun result => EDSL.BufferCall.Post spec input initial result.state) ∧
      EDSL.BufferCall.RawPolicy spec input initial := by
  intro input initial pre
  obtain ⟨annotations, admitted⟩ := generated input initial pre
  have binding : CFG.At bytes graph initial.rip valid.entry initial := by
    refine ⟨pre.code, ?_⟩
    simp [valid.entry_offset]
  obtain ⟨executions, policy⟩ := annotations.total_policy valid valid.entry_cutpoint binding admitted
  refine ⟨?_, policy⟩
  intro choices
  obtain ⟨result, execution, post, _⟩ := executions choices
  exact ⟨result, execution, post⟩

/-- Generated sparse cutpoint evidence establishes the independent buffer-call
contract for every AF stream, with original code/caller/buffer resources and
actual current read authority at every continuing prefix and after return.
The whole-RAM and ABI observations are exactly `BufferCall.Post`.

The checked complete CFG and generated VCs are proof evidence, never present
input-domain premises. Termination uses the existing dynamic natural rank;
there is no fixed input limit or separate executor. Native loading, stable
ordinary RAM, interference control and the sequential callable target profile
remain the environmental boundary of the represented semantics. -/
theorem bufferCall_semantics_of_cutpoints
    (spec : EDSL.BufferCall.Spec) (bytes : List Byte) (graph : CFG.Graph)
    (valid : CFG.Valid bytes graph profile)
    (generated : ∀ input initial, EDSL.BufferCall.Pre spec bytes input initial →
      ∃ annotations : Cutpoints.Annotations bytes graph initial.rip
        (EDSL.BufferCall.Post spec input initial)
        (fun _ read => EDSL.BufferCall.RawRead spec input initial read),
        annotations.Inv valid.entry initial) :
    Grading.ReadOnlySemanticClaim (EDSL.BufferCall.readOnlyTask spec) bytes :=
  EDSL.BufferCall.semantics_of_raw
    (bufferCall_raw_of_cutpoints spec bytes graph valid generated)

end EDSL.X86.VCGen
