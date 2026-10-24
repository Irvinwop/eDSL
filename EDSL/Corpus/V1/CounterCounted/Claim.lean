/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.CounterCounted.PrefixFrames
import EDSL.Corpus.V1.CounterCounted.Completion

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Both complete frozen compiler images satisfy one independent counted-void-call
contract for every admitted finite population. Shared adapters prove prefix
safety, full actual RMW and RET provenance, ABI return frames, chronological
modular conservation, enabledness, finite chosen completion and bounded own
progress across arbitrary successful finite interleavings.

The input count is uint32 and the shared cell is uint64. An invocation's own
increments can interleave with its peers; the invocation is not one atomic
fetch-add operation. Completion does not assume scheduler fairness. Bounds
count modeled issues and establish no minimum cost or wall-clock bound.

The represented machine/resource/translation assumptions remain explicit in
the independent contract and production semantics. This theorem is a modeled
image claim; exact-file certificate registration, useful loaded executions,
native conformance and compiler/physical-OS refinement are separate obligations.
-/

namespace EDSL.Corpus.V1.CounterCounted
open X86 OS OS.TSO64

/-- Complete universal candidate proof against the unchanged independent task,
without manager-created inputs or caller-supplied proof annotations. -/
theorem claim (compiler : CounterCommon.Compiler) :
    Grading.ConcurrentTask.Counted64.Claim (image compiler) where
  prefixes := prefixes compiler
  completed := by
    intro before target cell requests pre actions actual run returned
    rcases actual with ⟨cut, observations⟩
    exact post_of_safe pre run (safePrefix pre run) returned
  enabled := enabled compiler
  completion := by
    intro before target cell requests pre prior actual run
    rcases actual with ⟨cut, observations⟩
    exact completion_of_safety pre (prefixes compiler before target cell requests pre) run
  ownProgress := ownProgress compiler

#print axioms claim

end EDSL.Corpus.V1.CounterCounted

#audit_edsl
