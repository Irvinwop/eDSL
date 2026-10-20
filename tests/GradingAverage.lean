/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Driver
import EDSL.PureCall.Candidate
import EDSL.Corpus.V1.AverageBodies
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.GradingAverage
open X86 Grading

/-- Export one compiler's evidence through the fixed registered contract.
Present domain witnesses do not assume any successful future execution. -/
private theorem raw_claim (compiler : Corpus.V1.AverageCode.Compiler)
    (semantic : ReadOnlySemanticClaim (PureCall.readOnlyTask Arithmetic64.average)
      (Corpus.V1.AverageCode.bytes compiler)) :
    Claim .average64 (Corpus.V1.AverageCode.bytes compiler) := by
  refine ⟨?_, (old_nonvacuous_iff _ _).mpr
    (PureCall.Candidate.nonvacuous Arithmetic64.average
      (0xffffffffffffffff, 0xfffffffffffffffd) trivial
      Arithmetic64.average_useful_overflow_asymmetric _ ?_ ?_)⟩
  · change SemanticClaim (ofReadOnly (PureCall.readOnlyTask Arithmetic64.average)) _
    exact (old_semanticClaim_iff _ _).mpr semantic
  all_goals cases compiler <;> decide +kernel

theorem raw_gcc : Claim .average64
    [0xf3,0x0f,0x1e,0xfa,0x48,0x89,0xf8,0x48,0x21,0xf7,
     0x48,0x31,0xf0,0x48,0xd1,0xe8,0x48,0x01,0xf8,0xc3] :=
  raw_claim .defaultGCC Corpus.V1.AverageBodies.gcc_semantics

theorem raw_clang : Claim .average64
    [0x48,0x89,0xf0,0x48,0x21,0xf8,0x48,0x31,0xfe,
     0x48,0xd1,0xee,0x48,0x01,0xf0,0xc3] :=
  raw_claim .defaultClang Corpus.V1.AverageBodies.clang_semantics

open Lean EDSLGrader EDSLGrader.Runtime

run_cmd do
  let environment := (← getEnv).toKernelEnv
  let some id := taskID "average64" | throwError "Average task name rejected"
  for (bytes, proof) in #[
      (Corpus.V1.AverageCode.bytes .defaultGCC, ``raw_gcc),
      (Corpus.V1.AverageCode.bytes .defaultClang, ``raw_clang)] do
    match checkExpr environment {} (expectedClaim id bytes) (mkConst proof)
        `EDSLGrader.Internal.averagePositive with
    | .error failure => throwError "Valid average claim rejected: {failure}"
    | .ok _ => pure ()
    -- Addition and average have the same input shape but different fixed
    -- mathematical results. A controller must not interchange their proofs.
    for (expected, label) in #[
        (expectedClaim .addModulo64 bytes, "wrong task"),
        (expectedClaim id (bytes.dropLast ++ [0x90]), "changed RET")] do
      match checkExpr environment {} expected (mkConst proof)
          `EDSLGrader.Internal.averageNegative with
      | .ok _ => throwError "Average proof accepted for {label}"
      | .error failure =>
        unless failure.kind == .rejected && failure.message == "kernel declTypeMismatch" do
          throwError "Average {label} failed for an unexpected reason: {failure}"
  logInfo "Average controller accepts exact claims and rejects wrong task/changed RET at defaults"

end EDSL.Tests.GradingAverage
#audit_edsl
