/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.CounterGCCRank
import EDSL.Corpus.V1.CounterClangRank
import EDSL.OS.TSO64.EffectSimulation.Mixed.RankedLocal

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
    Mixed.RankLaws (rules site call pre.callerCanonical) where
  rank := TerminationRank.rank site call
  positive := by
    intro node state history _invariant
    exact TerminationRank.rank_positive site call node state history
  idle := by
    intro node before after history extended idle _invariant
    exact TerminationRank.rank_idle_eq idle
  retired := by
    intro node before history af result retirement invariant issued follows
    exact TerminationRank.follow_rank_decreases invariant issued follows

#print axioms rankLaws
end EDSL.Corpus.V1.CounterGCC

namespace EDSL.Corpus.V1.CounterClang
open OS.TSO64.EffectSimulation CounterCommon

/-- The complete Clang graph satisfies the same reusable rank laws, including
its remainder loop and eight-increment main body. -/
def rankLaws {site : Site .defaultClang} {call : Call} {initial : S}
    (pre : Pre site call initial) :
    Mixed.RankLaws (rules site call pre.callerCanonical pre.stack) where
  rank := CounterClangRank.rank site call
  positive := by
    intro node state history _invariant
    exact CounterClangRank.rank_positive site call node state history
  idle := by
    intro node before after history extended idle _invariant
    exact CounterClangRank.rank_idle idle
  retired := by
    intro node before history af result retirement invariant issued follows
    exact CounterClangRank.follow_rank_decreases invariant issued follows

#print axioms rankLaws
end EDSL.Corpus.V1.CounterClang

#audit_edsl
