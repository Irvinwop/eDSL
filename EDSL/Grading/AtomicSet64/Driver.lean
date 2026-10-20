/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Driver
import EDSL.Grading.AtomicSet64.Artifact

/-! Data-only controller for uninterrupted full64 set calls. The desired task
is independent of actual opcodes; their actual ordered events remain in the
checked execution contract. -/
namespace EDSLGrader.AtomicSet64
open Lean EDSL EDSLGrader.Runtime

abbrev Artifact := EDSL.Grading.AtomicSet64.Artifact

def operationExpr : Logical64.Operation → Expr
  | .intersection => mkConst ``Logical64.Operation.intersection
  | .union => mkConst ``Logical64.Operation.union
  | .symmetricDifference => mkConst ``Logical64.Operation.symmetricDifference

def expectedClaim (desired : Logical64.Operation) (bytes : List X86.Byte) : Expr :=
  mkApp2 (mkConst ``EDSL.Grading.AtomicSet64.Claim)
    (operationExpr desired) (EDSLGrader.byteExpr bytes)

/-- Packet and literal-artifact wrapper share the supplied limits and the
cumulative kernel ceiling. Checking imports no candidate code and raises no
wrapper recursion limit. -/
def grade (env : Kernel.Environment) (limits : Limits) (desired : Logical64.Operation)
    (artifact : Artifact) (packet : String) : Except Failure EDSLGrader.Acceptance := do
  let selected ← EDSL.Grading.Artifact.select artifact |>.mapError fun _ =>
    ⟨.unsupported, "atomic set artifact admission failed"⟩
  let checked ← checkPacket env limits (expectedClaim desired selected.code) packet
  let code := EDSLGrader.byteExpr selected.code
  let someCode := mkApp2 (mkConst ``Option.some [Level.zero])
    (toTypeExpr (List X86.Byte)) code
  let selection := mkApp2 (mkConst ``Eq.refl [Level.one])
    (toTypeExpr (Option (List X86.Byte))) someCode
  let literal := EDSLGrader.artifactExpr artifact
  let value := mkAppN (mkConst ``EDSL.Grading.AtomicSet64.Artifact.certify)
    #[operationExpr desired, literal, code, selection, checked.value]
  let expected := mkApp2 (mkConst ``EDSL.Grading.AtomicSet64.Artifact.Claim)
    (operationExpr desired) literal
  let wrapped ← checkExpr checked.env limits expected value
    `EDSLGrader.Internal.atomicSet64Artifact
  return {
    codeBytes := selected.code.length
    declarations := checked.declarations
    constants := max checked.constants wrapped.constants
    decoderSteps := checked.decoderSteps
    auditSteps := checked.auditSteps + wrapped.auditSteps
    kernelChecks := checked.kernelChecks + wrapped.kernelChecks }

end EDSLGrader.AtomicSet64
