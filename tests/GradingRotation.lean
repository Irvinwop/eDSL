/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Driver
import EDSL.Corpus.V1.RotationBodies

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.GradingRotation
open X86 Grading

private theorem raw_claim (compiler : Corpus.V1.RotationCode.Compiler)
    (semantic : ReadOnlySemanticClaim (PureCall.readOnlyTask Arithmetic64.rotateLeft)
      (Corpus.V1.RotationCode.bytes compiler)) :
    Claim .rotateLeft64 (Corpus.V1.RotationCode.bytes compiler) := by
  refine ⟨?_, domain_nonvacuous .rotateLeft64 _ ?_ ?_⟩
  · change SemanticClaim (ofReadOnly (PureCall.readOnlyTask Arithmetic64.rotateLeft)) _
    exact (old_semanticClaim_iff _ _).mpr semantic
  all_goals cases compiler <;> decide +kernel

-- Whole frozen symbol extents, including GCC's ENDBR64 and each actual RET.
theorem raw_gcc : Claim .rotateLeft64
    [0xf3,0x0f,0x1e,0xfa,0x48,0x89,0xf8,0x89,0xf1,0x48,0xd3,0xc0,0xc3] :=
  raw_claim .defaultGCC Corpus.V1.RotationBodies.gcc_semantics

theorem raw_clang : Claim .rotateLeft64
    [0x89,0xf1,0x48,0x89,0xf8,0x48,0xd3,0xc0,0xc3] :=
  raw_claim .defaultClang Corpus.V1.RotationBodies.clang_semantics

open Lean EDSLGrader EDSLGrader.Runtime

run_cmd do
  let environment := (← getEnv).toKernelEnv
  let some id := taskID "rotateLeft64" | throwError "Rotation task name rejected"
  for (bytes, proof) in #[
      (Corpus.V1.RotationCode.bytes .defaultGCC, ``raw_gcc),
      (Corpus.V1.RotationCode.bytes .defaultClang, ``raw_clang)] do
    match checkExpr environment {} (expectedClaim id bytes) (mkConst proof)
        `EDSLGrader.Internal.rotationPositive with
    | .error failure => throwError "Valid rotation claim rejected: {failure}"
    | .ok checked =>
      logInfo m!"Rotation {proof}: accepted; kernelChecks={checked.kernelChecks}"
    for (expected, label) in #[
        (expectedClaim .average64 bytes, "wrong average64 task"),
        (expectedClaim id (bytes.dropLast ++ [0x90]), "changed final RET")] do
      match checkExpr environment {} expected (mkConst proof)
          `EDSLGrader.Internal.rotationNegative with
      | .ok _ => throwError "Rotation proof accepted for {label}"
      | .error failure =>
        unless failure.kind == .rejected && failure.message == "kernel declTypeMismatch" do
          throwError "Rotation {label} failed for an unexpected reason: {failure}"
        logInfo m!"Rotation {proof}: {label} rejected with kernel declTypeMismatch"

#print axioms raw_gcc
#print axioms raw_clang
end EDSL.Tests.GradingRotation
#audit_edsl
