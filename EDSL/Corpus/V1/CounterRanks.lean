/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.CounterGCCRank
import EDSL.Corpus.V1.CounterClangRank
import EDSL.OS.TSO64.EffectSimulation.Mixed.CountedRank

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Compiler-specific count and decoded-edge certificates instantiate the shared
local rank interface. Every-node invariant retention, authenticated idle
transport and actual step lifting remain generic. These adapters introduce
no scheduler, terminating execution, fairness or corpus admission theorem.
-/

namespace EDSL.Corpus.V1.CounterGCC
open OS.TSO64.EffectSimulation CounterCommon

/-- The complete GCC graph satisfies the reusable rank laws under its existing
input invariant and actual retirement continuation. -/
def rankLaws {site : Site .defaultGCC} {call : Call} {initial : S}
    (pre : Pre site call initial) :
    Mixed.RankLaws (rules site call pre.callerCanonical) :=
  Mixed.RankLaws.ofCountedStages
    (rules site call pre.callerCanonical) call.iterations.toNat 16
    TerminationRank.stage
    (fun node => ⟨TerminationRank.stage_positive node, TerminationRank.stage_lt_sixteen node⟩)
    (fun _ _ _ ordinary edge => TerminationRank.ordinary_stage_decreases ordinary edge)
    (fun _ _ _ _ invariant locked => TerminationRank.locked_count_lt_requested invariant locked)

#print axioms rankLaws
end EDSL.Corpus.V1.CounterGCC

namespace EDSL.Corpus.V1.CounterClang
open OS.TSO64.EffectSimulation CounterCommon

/-- The complete Clang graph satisfies the same reusable rank laws, including
its remainder loop and eight-increment main body. -/
def rankLaws {site : Site .defaultClang} {call : Call} {initial : S}
    (pre : Pre site call initial) :
    Mixed.RankLaws (rules site call pre.callerCanonical pre.stack) :=
  Mixed.RankLaws.ofCountedStages
    (rules site call pre.callerCanonical pre.stack) call.iterations.toNat 16
    CounterClangRank.stage
    CounterClangRank.stage_bounds
    (fun _ _ _ ordinary edge => CounterClangRank.ordinary_stage_decreases ordinary edge)
    (fun _ _ _ _ invariant locked => CounterClangRank.locked_count_lt_requested invariant locked)

#print axioms rankLaws
end EDSL.Corpus.V1.CounterClang

#audit_edsl
