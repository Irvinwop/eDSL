/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.CallStack.Driver
import EDSL.Grading.CallMemory64.Artifact

/-! Closed controller for the callable DATA8 contract. Code and entry select
the expected fixed proposition; proof data selects neither the task nor its
admission, current resource policy, imports or budget. -/
namespace EDSLGrader.CallMemory64
open Lean EDSL EDSLGrader.Runtime

abbrev Artifact := EDSL.Grading.CallMemory64.Artifact

def expectedClaim (program : EDSL.CallStack.Program) : Expr :=
  mkApp (mkConst ``EDSL.CallMemory64.Claim) (CallStack.programExpr program)

def makeArtifact (bytes : ByteArray) (entry : Nat) (span : Option Nat) : Artifact :=
  CallStack.makeArtifact bytes entry span

/-- Check the selected program and a wrapper containing the entire literal
artifact. The shared selector's successful result is reduced again by the
kernel, with the packet and wrapper sharing one cumulative heartbeat budget. -/
def grade (env : Kernel.Environment) (limits : Limits) (artifact : Artifact)
    (packet : String) : Except Failure EDSLGrader.Acceptance := do
  let selected ← artifact.select |>.mapError fun _ =>
    ⟨.unsupported, "callable DATA8 artifact admission failed"⟩
  let checked ← checkPacket env limits (expectedClaim selected.program) packet
  let program := CallStack.programExpr selected.program
  let someProgram := mkApp2 (mkConst ``Option.some [Level.zero])
    (mkConst ``EDSL.CallStack.Program) program
  let selection := mkApp2 (mkConst ``Eq.refl [Level.one])
    (mkApp (mkConst ``Option [Level.zero]) (mkConst ``EDSL.CallStack.Program)) someProgram
  let value := mkAppN (mkConst ``EDSL.Grading.CallMemory64.Artifact.certify)
    #[CallStack.artifactExpr artifact, program, selection, checked.value]
  let expected := mkApp (mkConst ``EDSL.Grading.CallMemory64.Artifact.Claim)
    (CallStack.artifactExpr artifact)
  let wrapperLimits := { limits with kernelRecDepth := 32768 }
  let wrapped ← checkExpr checked.env wrapperLimits expected value
    `EDSLGrader.Internal.callMemory64Artifact
  return {
    codeBytes := selected.program.bytes.length
    declarations := checked.declarations
    constants := max checked.constants wrapped.constants
    decoderSteps := checked.decoderSteps
    auditSteps := checked.auditSteps + wrapped.auditSteps
    kernelChecks := checked.kernelChecks + wrapped.kernelChecks }

end EDSLGrader.CallMemory64
