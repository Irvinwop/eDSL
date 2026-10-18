/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Driver
import EDSL.Grading.AtomicLogical64.Artifact

/-! Closed controller for discarded full64 atomic union. The installed task,
ISA relation, resource policy and limits are independent of submitted data. -/
namespace EDSLGrader.AtomicLogical64
open Lean EDSL EDSLGrader.Runtime

abbrev Artifact := EDSL.Grading.AtomicLogical64.Artifact

def expectedClaim (bytes : List X86.Byte) : Expr :=
  mkApp (mkConst ``EDSL.Grading.AtomicLogical64.Claim) (EDSLGrader.byteExpr bytes)

/-- Packet checking and the literal-artifact wrapper use the same supplied
limits and cumulative kernel checking budget. Neither restores a proof status
from a cache nor imports candidate code into the trusted environment. -/
def grade (env : Kernel.Environment) (limits : Limits) (artifact : Artifact)
    (packet : String) : Except Failure EDSLGrader.Acceptance := do
  let selected ← EDSL.Grading.Artifact.select artifact |>.mapError fun _ =>
    ⟨.unsupported, "atomic union artifact admission failed"⟩
  let checked ← checkPacket env limits (expectedClaim selected.code) packet
  let code := EDSLGrader.byteExpr selected.code
  let someCode := mkApp2 (mkConst ``Option.some [Level.zero])
    (toTypeExpr (List X86.Byte)) code
  let selection := mkApp2 (mkConst ``Eq.refl [Level.one])
    (toTypeExpr (Option (List X86.Byte))) someCode
  let literal := EDSLGrader.artifactExpr artifact
  let value := mkAppN (mkConst ``EDSL.Grading.AtomicLogical64.Artifact.certify)
    #[literal, code, selection, checked.value]
  let expected := mkApp (mkConst ``EDSL.Grading.AtomicLogical64.Artifact.Claim) literal
  let wrapped ← checkExpr checked.env limits expected value
    `EDSLGrader.Internal.atomicLogical64Artifact
  return {
    codeBytes := selected.code.length
    declarations := checked.declarations
    constants := max checked.constants wrapped.constants
    decoderSteps := checked.decoderSteps
    auditSteps := checked.auditSteps + wrapped.auditSteps
    kernelChecks := checked.kernelChecks + wrapped.kernelChecks }

end EDSLGrader.AtomicLogical64
