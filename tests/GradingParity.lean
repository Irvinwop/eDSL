/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Driver
import EDSL.Corpus.V1.ParityBodies
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.GradingParity
open X86 Grading

/-- The existing generic useful-domain constructor and each compiler's
independent semantics establish the fixed registered claim. -/
private theorem raw_claim (compiler : Corpus.V1.ParityCode.Compiler)
    (semantic : ReadOnlySemanticClaim (PureCall.readOnlyTask Arithmetic64.parity64)
      (Corpus.V1.ParityCode.bytes compiler)) :
    Claim .parity64 (Corpus.V1.ParityCode.bytes compiler) := by
  refine ⟨?_, domain_nonvacuous .parity64 _ ?_ ?_⟩
  · change SemanticClaim (ofReadOnly (PureCall.readOnlyTask Arithmetic64.parity64)) _
    exact (old_semanticClaim_iff _ _).mpr semantic
  all_goals cases compiler <;> decide +kernel

-- Literal whole symbol extents independently pin both controller mappings.
-- GCC retains ENDBR64, both RETs and padding; Clang retains its six-byte NOP.
theorem raw_gcc : Claim .parity64
    [0xf3,0x0f,0x1e,0xfa,0x31,0xc0,0x48,0x85,0xff,0x74,0x15,
     0x0f,0x1f,0x44,0x00,0x00,0x89,0xfa,0x83,0xe2,0x01,0x31,0xd0,
     0x48,0xd1,0xef,0x75,0xf4,0xc3,0x0f,0x1f,0x00,0xc3] :=
  raw_claim .defaultGCC Corpus.V1.ParityBodies.gcc_semantics

theorem raw_clang : Claim .parity64
    [0x31,0xc0,0x48,0x85,0xff,0x74,0x1c,0x48,0x89,0xf9,
     0x66,0x0f,0x1f,0x44,0x00,0x00,0x89,0xfa,0x83,0xe2,0x01,
     0x31,0xd0,0x48,0xd1,0xe9,0x48,0x83,0xff,0x01,0x48,0x89,0xcf,
     0x77,0xed,0xc3] :=
  raw_claim .defaultClang Corpus.V1.ParityBodies.clang_semantics

open Lean EDSLGrader EDSLGrader.Runtime

run_cmd do
  let environment := (← getEnv).toKernelEnv
  let some id := taskID "parity64" | throwError "Parity task name rejected"
  for (bytes, proof) in #[
      (Corpus.V1.ParityCode.bytes .defaultGCC, ``raw_gcc),
      (Corpus.V1.ParityCode.bytes .defaultClang, ``raw_clang)] do
    match checkExpr environment {} (expectedClaim id bytes) (mkConst proof)
        `EDSLGrader.Internal.parityPositive with
    | .error failure => throwError "Valid parity claim rejected: {failure}"
    | .ok checked =>
      logInfo m!"Parity {proof}: accepted; kernelChecks={checked.kernelChecks}"
    -- Popcount has the same full64-input/low32-output shape but a different
    -- independent mathematical result. Neither that task nor altered code
    -- can reuse a parity proof. All checks retain the default limits.
    for (expected, label) in #[
        (expectedClaim .populationCount64 bytes, "wrong populationCount64 task"),
        (expectedClaim id (bytes.dropLast ++ [0x90]), "changed final RET")] do
      match checkExpr environment {} expected (mkConst proof)
          `EDSLGrader.Internal.parityNegative with
      | .ok _ => throwError "Parity proof accepted for {label}"
      | .error failure =>
        unless failure.kind == .rejected && failure.message == "kernel declTypeMismatch" do
          throwError "Parity {label} failed for an unexpected reason: {failure}"
        logInfo m!"Parity {proof}: {label} rejected with kernel declTypeMismatch"

#print axioms raw_gcc
#print axioms raw_clang
end EDSL.Tests.GradingParity
#audit_edsl
