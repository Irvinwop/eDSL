/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.RegistryDriver
import EDSL.PureCall.Candidate
import EDSL.Corpus.V1.SignumResources
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.Tests.GradingSignum
open X86 Grading Corpus.V1

/-- The fixed registration owns both the independent mathematical task and
its flag-vector execution model. A useful present-only candidate witness does
not narrow universal admission to the signed minimum. -/
private theorem raw_claim (compiler : SignumCode.Compiler) :
    RegisteredClaim .signumSigned32 (SignumCode.bytes compiler) := by
  apply (registeredClaim_signumSigned32_iff _).mpr
  refine ⟨SignumResources.semantics compiler, ?_⟩
  exact PureCall.Candidate.nonvacuous Scalar32.signumSigned
    SignumResources.usefulValue (SignumCode.domain _) SignumResources.useful_value _
    (by cases compiler <;> decide +kernel) (by cases compiler <;> decide +kernel)

theorem raw_gcc : RegisteredClaim .signumSigned32
    [0xf3,0x0f,0x1e,0xfa,0x31,0xc0,0x85,0xff,0x0f,0x9f,0xc0,0xc1,0xef,0x1f,0x29,0xf8,0xc3] :=
  raw_claim .defaultGCC

theorem raw_clang : RegisteredClaim .signumSigned32
    [0x89,0xf9,0xc1,0xf9,0x1f,0x31,0xc0,0x85,0xff,0x0f,0x95,0xc0,0x09,0xc8,0xc3] :=
  raw_claim .defaultClang

open Lean EDSLGrader EDSLGrader.Runtime

run_cmd do
  let environment := (← getEnv).toKernelEnv
  let some id := registryID "signumSigned32" | throwError "Signed signum task name rejected"
  let some multiplyID := registryID "multiplyModulo64" | throwError "Multiplication task name rejected"
  -- Parse both names and use the actual expected-expression constructors in
  -- kernel checks. An incorrect parser or registryExpr mapping therefore fails
  -- acceptance or the distinct registered-task rejection below.
  for (bytes, proof, changed, other) in #[
      (SignumCode.bytes .defaultGCC, ``raw_gcc,
        [0xf3,0x0f,0x1e,0xfa,0x31,0xc0,0x85,0xff,0x0f,0x9f,0xc0,0xc1,0xef,0x1e,0x29,0xf8,0xc3],
        SignumCode.bytes .defaultClang),
      (SignumCode.bytes .defaultClang, ``raw_clang,
        [0x89,0xf9,0xc1,0xf9,0x1f,0x31,0xc0,0x85,0xff,0x0f,0x95,0xc0,0x31,0xc8,0xc3],
        SignumCode.bytes .defaultGCC)] do
    match checkExpr environment {} (expectedRegisteredClaim id bytes) (mkConst proof)
        `EDSLGrader.Internal.signumPositive with
    | .error failure => throwError "Valid signum claim rejected: {failure}"
    | .ok _ => pure ()
    for (expected, label) in #[
        (expectedRegisteredClaim multiplyID bytes, "wrong registered mathematical task"),
        (expectedClaim .addModulo64 bytes, "wrong legacy mathematical task"),
        (expectedRegisteredClaim id (bytes.dropLast ++ [0x90]), "changed RET"),
        (expectedRegisteredClaim id changed, "changed shift count or OR opcode"),
        (expectedRegisteredClaim id other, "cross-compiler code")] do
      match checkExpr environment {} expected (mkConst proof)
          `EDSLGrader.Internal.signumNegative with
      | .ok _ => throwError "Signum proof accepted for {label}"
      | .error failure =>
        unless failure.kind == .rejected && failure.message == "kernel declTypeMismatch" do
          throwError "Signum {label} failed for an unexpected reason: {failure}"
  logInfo "Signum controller accepts both exact claims and rejects wrong tasks and changed code"

#print axioms raw_gcc
#print axioms raw_clang
end EDSL.Tests.GradingSignum
#audit_edsl
