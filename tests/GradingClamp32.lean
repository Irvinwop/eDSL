/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Driver
import EDSL.Corpus.V1.Clamps
import EDSL.Audit

namespace EDSL.Tests.GradingClamp32

/-- The proof has an independently written task and literal body type; the
controller must choose this same claim when parsing its registered task name. -/
theorem clamp_claim : Grading.Claim .clampSigned32
    [0x89,0xd0,0x39,0xd7,0x0f,0x4c,0xc7,0x39,0xf7,0x0f,0x4c,0xc6,0xc3] :=
  (Corpus.V1.Clamps.certificate .defaultClang).claim

/-- The default GCC body retains ENDBR64 and crosses the controller's balanced
byte-quotation threshold. Its expected type still fixes every literal byte. -/
theorem gcc_clamp_claim : Grading.Claim .clampSigned32
    [0xf3,0x0f,0x1e,0xfa,0x39,0xd7,0x89,0xf0,0x0f,0x4e,0xd7,
      0x39,0xf7,0x0f,0x4d,0xc2,0xc3] :=
  (Corpus.V1.Clamps.certificate .defaultGCC).claim

open Lean EDSLGrader EDSLGrader.Runtime

-- Exercise the actual expected-type builder and kernel. A valid independent
-- pair-program proof must not pass as an interval-projection proof.
run_cmd do
  let env := (← getEnv).toKernelEnv
  let some id := taskID "clampSigned32" | throwError "clamp task name was rejected"
  let bytes : List X86.Byte :=
    [0x89,0xd0,0x39,0xd7,0x0f,0x4c,0xc7,0x39,0xf7,0x0f,0x4c,0xc6,0xc3]
  match checkExpr env { kernelRecDepth := 4096 } (expectedClaim id bytes)
      (mkConst ``clamp_claim) `EDSLGrader.Internal.clampPositive with
  | .error failure => throwError "valid clamp claim rejected: {failure}"
  | .ok _ => pure ()
  let gccBytes : List X86.Byte :=
    [0xf3,0x0f,0x1e,0xfa,0x39,0xd7,0x89,0xf0,0x0f,0x4e,0xd7,
      0x39,0xf7,0x0f,0x4d,0xc2,0xc3]
  match checkExpr env { kernelRecDepth := 4096 } (expectedClaim id gccBytes)
      (mkConst ``gcc_clamp_claim) `EDSLGrader.Internal.gccClampPositive with
  | .error failure => throwError "valid GCC clamp claim rejected: {failure}"
  | .ok _ => pure ()
  match checkExpr env { kernelRecDepth := 4096 } (expectedClaim id Pair32.bytes)
      (mkConst ``Grading.Known.pair) `EDSLGrader.Internal.clampWrongTask with
  | .ok _ => throwError "valid pair-program proof was accepted as clamp"
  | .error failure =>
    unless failure.kind == .rejected && failure.message == "kernel declTypeMismatch" do
      throwError "wrong-task proof failed for an unexpected reason: {failure}"
  logInfo "Clamp controller accepts both final-file claims and rejects an unrelated valid program claim"

end EDSL.Tests.GradingClamp32

#audit_edsl
