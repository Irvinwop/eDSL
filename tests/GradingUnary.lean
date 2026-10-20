/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Driver
import EDSL.Corpus.V1.UnaryCertificates
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.GradingUnary
open X86 Grading

/-- Independently fixed task and complete literal code types challenge the
controller's new name-to-task and task-to-expression paths. -/
theorem clang_absolute : Claim .absSigned32
    [0x89,0xf8,0xf7,0xd8,0x0f,0x48,0xc7,0xc3] :=
  (Corpus.V1.UnaryCertificates.certificate .defaultClang .absSigned32).claim

theorem gcc_absolute : Claim .absSigned32
    [0xf3,0x0f,0x1e,0xfa,0x89,0xf8,0xf7,0xd8,0x0f,0x48,0xc7,0xc3] :=
  (Corpus.V1.UnaryCertificates.certificate .defaultGCC .absSigned32).claim

theorem clang_reverse : Claim .byteSwap64 [0x48,0x89,0xf8,0x48,0x0f,0xc8,0xc3] :=
  (Corpus.V1.UnaryCertificates.certificate .defaultClang .byteSwap64).claim

theorem gcc_reverse : Claim .byteSwap64
    [0xf3,0x0f,0x1e,0xfa,0x48,0x89,0xf8,0x48,0x0f,0xc8,0xc3] :=
  (Corpus.V1.UnaryCertificates.certificate .defaultGCC .byteSwap64).claim

/-- Raw-code grading reuses the universal body proof and an independent
trusted current-resource domain. It need not serialize unused ELF metadata. -/
private theorem raw_claim (compiler : Corpus.V1.UnaryCode.Compiler)
    (operation : Corpus.V1.UnaryCode.Operation) :
    Claim (Corpus.V1.UnaryCertificates.taskID operation)
      (Corpus.V1.UnaryCode.bytes compiler operation) := by
  refine ⟨?_, domain_nonvacuous _ _ ?_ ?_⟩
  · rw [Corpus.V1.UnaryCertificates.registration operation]
    exact (old_semanticClaim_iff _ _).mpr
      (Corpus.V1.UnaryBodies.raw_semantics compiler operation)
  all_goals cases compiler <;> cases operation <;> decide +kernel

theorem raw_clang_absolute : Claim .absSigned32
    [0x89,0xf8,0xf7,0xd8,0x0f,0x48,0xc7,0xc3] :=
  raw_claim .defaultClang .absSigned32

theorem raw_gcc_absolute : Claim .absSigned32
    [0xf3,0x0f,0x1e,0xfa,0x89,0xf8,0xf7,0xd8,0x0f,0x48,0xc7,0xc3] :=
  raw_claim .defaultGCC .absSigned32

theorem raw_clang_reverse : Claim .byteSwap64 [0x48,0x89,0xf8,0x48,0x0f,0xc8,0xc3] :=
  raw_claim .defaultClang .byteSwap64

theorem raw_gcc_reverse : Claim .byteSwap64
    [0xf3,0x0f,0x1e,0xfa,0x48,0x89,0xf8,0x48,0x0f,0xc8,0xc3] :=
  raw_claim .defaultGCC .byteSwap64

open Lean EDSLGrader EDSLGrader.Runtime

run_cmd do
  let environment := (← getEnv).toKernelEnv
  let checks : Array (String × List Byte × Name) := #[
    ("absSigned32", [0x89,0xf8,0xf7,0xd8,0x0f,0x48,0xc7,0xc3], ``clang_absolute),
    ("absSigned32", [0xf3,0x0f,0x1e,0xfa,0x89,0xf8,0xf7,0xd8,0x0f,0x48,0xc7,0xc3], ``gcc_absolute),
    ("byteSwap64", [0x48,0x89,0xf8,0x48,0x0f,0xc8,0xc3], ``clang_reverse),
    ("byteSwap64", [0xf3,0x0f,0x1e,0xfa,0x48,0x89,0xf8,0x48,0x0f,0xc8,0xc3], ``gcc_reverse)]
  for (request, bytes, proof) in checks do
    let some id := taskID request | throwError "Unary task name rejected: {request}"
    match checkExpr environment {} (expectedClaim id bytes) (mkConst proof)
        `EDSLGrader.Internal.unaryPositive with
    | .error failure => throwError "Valid unary claim rejected: {failure}"
    | .ok _ => pure ()
  let some absolute := taskID "absSigned32" | throwError "Absolute task name rejected"
  -- An authentic swap proof and exact swap bytes still have the wrong contract.
  match checkExpr environment {}
      (expectedClaim absolute [0x48,0x89,0xf8,0x48,0x0f,0xc8,0xc3])
      (mkConst ``clang_reverse) `EDSLGrader.Internal.unaryWrongTask with
  | .ok _ => throwError "Byte reversal proof accepted as signed absolute value"
  | .error failure =>
    unless failure.kind == .rejected && failure.message == "kernel declTypeMismatch" do
      throwError "Wrong-task rejection had an unexpected reason: {failure}"
  -- Same contract, but a changed final RET cannot reuse the original proof.
  match checkExpr environment {}
      (expectedClaim absolute [0x89,0xf8,0xf7,0xd8,0x0f,0x48,0xc7,0x90])
      (mkConst ``clang_absolute) `EDSLGrader.Internal.unaryChangedCode with
  | .ok _ => throwError "Absolute proof accepted for changed final bytes"
  | .error failure =>
    unless failure.kind == .rejected && failure.message == "kernel declTypeMismatch" do
      throwError "Changed-code rejection had an unexpected reason: {failure}"
  logInfo "Unary controller accepts four exact claims; wrong task and changed bytes reject at default limits"

end EDSL.Tests.GradingUnary
#audit_edsl
