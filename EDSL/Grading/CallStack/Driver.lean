/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Driver
import EDSL.Grading.CallStack.Artifact

/-! Closed controller for the resource-first callable contract. Candidate
packets cannot choose its engine, input domain, expected type or imports.
This IO controller is provisioned as trusted, as in the existing grader. -/
namespace EDSLGrader.CallStack
open Lean EDSL EDSLGrader.Runtime

abbrev Artifact := EDSL.Grading.CallStack.Artifact

def programExpr (program : EDSL.CallStack.Program) : Expr :=
  mkApp2 (mkConst ``EDSL.CallStack.Program.mk) (EDSLGrader.byteExpr program.bytes) (toExpr program.entry)

def artifactExpr : Artifact → Expr
  | .raw bytes entry => mkApp2 (mkConst ``EDSL.Grading.CallStack.Artifact.raw)
      (EDSLGrader.byteExpr bytes) (toExpr entry)
  | .elf bytes span entry => mkApp3 (mkConst ``EDSL.Grading.CallStack.Artifact.elf)
      (EDSLGrader.byteExpr bytes) (toExpr span) (toExpr entry)

def expectedClaim (program : EDSL.CallStack.Program) : Expr :=
  mkApp (mkConst ``EDSL.Grading.CallStack.Claim) (programExpr program)

def makeArtifact (bytes : ByteArray) (entry : Nat) (span : Option Nat) : Artifact :=
  let file := bytes.data.toList.map (fun byte => BitVec.ofNat 8 byte.toNat)
  match span with
  | none => .raw file entry
  | some length => .elf file length entry

/-- Host selection chooses the expected statement, while the final checked
wrapper independently reduces selection for the entire literal artifact and
its entry metadata. It uses the same cumulative kernel budget as its packet. -/
def grade (env : Kernel.Environment) (limits : Limits) (artifact : Artifact)
    (packet : String) : Except Failure EDSLGrader.Acceptance := do
  let selected ← artifact.select |>.mapError fun _ =>
    ⟨.unsupported, "call artifact admission failed"⟩
  let checked ← checkPacket env limits (expectedClaim selected.program) packet
  let program := programExpr selected.program
  let someProgram := mkApp2 (mkConst ``Option.some [Level.zero])
    (mkConst ``EDSL.CallStack.Program) program
  let selection := mkApp2 (mkConst ``Eq.refl [Level.one])
    (mkApp (mkConst ``Option [Level.zero]) (mkConst ``EDSL.CallStack.Program)) someProgram
  let value := mkAppN (mkConst ``EDSL.Grading.CallStack.Artifact.certify)
    #[artifactExpr artifact, program, selection, checked.value]
  let expected := mkApp (mkConst ``EDSL.Grading.CallStack.Artifact.Claim) (artifactExpr artifact)
  let wrapperLimits := { limits with kernelRecDepth := 32768 }
  let wrapped ← checkExpr checked.env wrapperLimits expected value
    `EDSLGrader.Internal.callStackArtifact
  return {
    codeBytes := selected.program.bytes.length
    declarations := checked.declarations
    constants := max checked.constants wrapped.constants
    decoderSteps := checked.decoderSteps
    auditSteps := checked.auditSteps + wrapped.auditSteps
    kernelChecks := checked.kernelChecks + wrapped.kernelChecks }

end EDSLGrader.CallStack
