/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.ChoicesPolicy
import EDSL.X86.VCGen.PureCall
import EDSL.PureCall.ResourcesFor

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.X86.VCGen
open Sequential

variable {profile : CFG.Profile}

/-- Universal vector WP evidence yields the original scalar-call postcondition
and resource policy for every complete flag-choice stream. The specification,
raw admission and resource admission are unchanged; `Evidence` and its
projection are proof evidence. Actual validated bytes and entry PC bind the
graph to executable memory. The vector soundness and policy theorems handle
IMUL directly, without a Bool simulation for that instruction.

The resource claim retains the same supplied logical code/caller ownership at
every actual prefix and at return. Stable ordinary RAM, no asynchronous
interference and the callable profile's other environmental assumptions still
apply. Native loading, physical CPU/OS refinement, registration, certificates
and scoring are outside this theorem. -/
theorem pureCall_semantics_of_generatedWith
    (spec : EDSL.PureCall.Spec) (bytes : List Byte) (graph : CFG.Graph)
    (valid : CFG.Valid bytes graph profile) (entry : graph.Index)
    (entryOffset : (graph.node entry).offset = 0) (fuel : Nat)
    (Evidence : EDSL.PureCall.Invocation spec → State → Result → Prop)
    (project : ∀ input initial result, Evidence input initial result →
      EDSL.PureCall.Post spec input initial result.state)
    (generated : ∀ input initial, EDSL.PureCall.Pre spec bytes input initial →
      wpWith graph initial.rip (PureCallAllowed initial) fuel entry initial
        (Evidence input initial)) :
    Grading.ReadOnlySemanticClaimFor .flags (EDSL.PureCall.readOnlyTask spec) bytes := by
  apply EDSL.PureCall.semantics_of_rawFor .flags
  intro input initial pre
  have pc : initial.rip = initial.rip + BitVec.ofNat 64 (graph.node entry).offset := by
    simp [entryOffset]
  have vc := generated input initial pre
  constructor
  · intro choices
    obtain ⟨result, execution, evidence, _, _⟩ := soundWith valid pre.code pc vc choices
    exact ⟨result, execution, project input initial result evidence⟩
  · exact (readOnly_policy_memoryWith valid pre.code pc vc).mono
      (fun _ memory => memory) (fun _ _ allowed => allowed.2)

end EDSL.X86.VCGen
