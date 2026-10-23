/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.RegistryDriver
import EDSL.PureCall.Candidate
import EDSL.Corpus.V1.MultiplyResources
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.GradingMultiply
open X86 Grading Corpus.V1

/-- The generic raw domain witnesses present code/caller resources independently
of execution. The fixed registry owns the model, mathematical specification,
policies and usefulness; no final ELF image is needed for a raw-code packet. -/
private theorem raw_claim (compiler : MultiplyCode.Compiler) :
    RegisteredClaim .multiplyModulo64 (MultiplyCode.bytes compiler) := by
  apply (registeredClaim_multiplyModulo64_iff _).mpr
  refine ⟨MultiplyResources.semantics compiler, ?_⟩
  exact PureCall.Candidate.nonvacuous Arithmetic64.multiplyModulo
    (0xffffffffffffffff, 2) trivial MultiplyResources.useful_value _
    (by cases compiler <;> decide +kernel) (by cases compiler <;> decide +kernel)

theorem raw_gcc : RegisteredClaim .multiplyModulo64
    [0xf3,0x0f,0x1e,0xfa,0x48,0x89,0xf8,0x48,0x0f,0xaf,0xc6,0xc3] :=
  raw_claim .defaultGCC

theorem raw_clang : RegisteredClaim .multiplyModulo64
    [0x48,0x89,0xf8,0x48,0x0f,0xaf,0xc6,0xc3] := raw_claim .defaultClang

open Lean EDSLGrader EDSLGrader.Runtime

run_cmd do
  let environment := (← getEnv).toKernelEnv
  let some id := registryID "multiplyModulo64" | throwError "Multiplication task name rejected"
  for (bytes, proof) in #[
      (MultiplyCode.bytes .defaultGCC, ``raw_gcc),
      (MultiplyCode.bytes .defaultClang, ``raw_clang)] do
    match checkExpr environment {} (expectedRegisteredClaim id bytes) (mkConst proof)
        `EDSLGrader.Internal.multiplyPositive with
    | .error failure => throwError "Valid multiplication claim rejected: {failure}"
    | .ok _ => pure ()
    -- Fixed full64 multiplication cannot borrow an addition contract or a
    -- claim for bytes whose terminating RET has been replaced by a NOP.
    for (expected, label) in #[
        (expectedClaim .addModulo64 bytes, "wrong mathematical task"),
        (expectedRegisteredClaim id (bytes.dropLast ++ [0x90]), "changed RET")] do
      match checkExpr environment {} expected (mkConst proof)
          `EDSLGrader.Internal.multiplyNegative with
      | .ok _ => throwError "Multiplication proof accepted for {label}"
      | .error failure =>
        unless failure.kind == .rejected && failure.message == "kernel declTypeMismatch" do
          throwError "Multiplication {label} failed for an unexpected reason: {failure}"
  logInfo "Multiplication controller accepts exact claims and rejects wrong task/changed RET"

end EDSL.Tests.GradingMultiply
#audit_edsl
