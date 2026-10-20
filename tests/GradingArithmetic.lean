/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Driver
import EDSL.Corpus.V1.Arithmetic
import EDSL.Audit

namespace EDSL.Tests.GradingArithmetic

/-- An independently typed claim at literal bytes supplies the positive side
of the controller boundary, without using its task-name or quotation function. -/
theorem addition_claim : Grading.Claim .addModulo64 [0x48,0x8d,0x04,0x37,0xc3] :=
  (Corpus.V1.Arithmetic.certificate .defaultClang).claim

open Lean EDSLGrader EDSLGrader.Runtime

-- Exercise the real expected-type controller and kernel, without replacing
-- either with a mock or asserting the parser's assigned enum value. A valid
-- pair-program proof must not become an addition proof through task aliasing.
run_cmd do
  let env := (← getEnv).toKernelEnv
  let some id := taskID "addModulo64" | throwError "addition task name was rejected"
  let additionBytes : List X86.Byte := [0x48,0x8d,0x04,0x37,0xc3]
  match checkExpr env { kernelRecDepth := 4096 } (expectedClaim id additionBytes)
      (mkConst ``addition_claim) `EDSLGrader.Internal.additionPositive with
  | .error failure => throwError "valid addition claim rejected: {failure}"
  | .ok _ => pure ()
  match checkExpr env { kernelRecDepth := 4096 } (expectedClaim id Pair32.bytes)
      (mkConst ``Grading.Known.pair) `EDSLGrader.Internal.additionWrongTask with
  | .ok _ => throwError "valid pair-program proof was accepted as addition"
  | .error failure =>
    unless failure.kind == .rejected && failure.message == "kernel declTypeMismatch" do
      throwError "wrong-task proof failed for an unexpected reason: {failure}"
  logInfo "Addition controller accepts its actual claim and rejects an unrelated valid program claim"

end EDSL.Tests.GradingArithmetic

#audit_edsl
