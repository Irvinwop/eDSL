/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Driver
import EDSL.Corpus.V1.PopcountCertificates
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.GradingPopcount
open X86 Grading

/-- Raw proof packets retain the independently registered mathematical task
and decoder-independent useful current resources, without serializing the
unused complete-ELF literal and symbol tables. -/
private theorem raw_claim (compiler : Corpus.V1.PopcountCode.Compiler)
    (semantic : ReadOnlySemanticClaim (PureCall.readOnlyTask Arithmetic64.populationCount)
      (Corpus.V1.PopcountCode.bytes compiler)) :
    Claim .populationCount64 (Corpus.V1.PopcountCode.bytes compiler) := by
  refine ⟨?_, domain_nonvacuous _ _ ?_ ?_⟩
  · rw [Corpus.V1.PopcountCertificates.registration]
    exact (old_semanticClaim_iff _ _).mpr semantic
  all_goals cases compiler <;> decide +kernel

-- Independently literal complete byte extents challenge both name-to-task and
-- task-to-expression controller paths, including default GCC's ENDBR64.
theorem raw_gcc : Claim .populationCount64
    [0xf3,0x0f,0x1e,0xfa,0x31,0xd2,0x48,0x85,0xff,0x74,0x11,
     0x0f,0x1f,0x44,0,0,0x48,0x8d,0x47,0xff,0x83,0xc2,1,
     0x48,0x21,0xc7,0x75,0xf4,0x89,0xd0,0xc3] :=
  raw_claim .defaultGCC Corpus.V1.PopcountBodies.gcc_semantics

theorem raw_clang : Claim .populationCount64
    [0x31,0xc0,0x48,0x85,0xff,0x74,0x14,0x66,0x0f,0x1f,0x84,0,0,0,0,0,
     0x48,0x8d,0x4f,0xff,0xff,0xc0,0x48,0x21,0xcf,0x75,0xf5,0xc3] :=
  raw_claim .defaultClang Corpus.V1.PopcountBodies.clang_semantics

open Lean EDSLGrader EDSLGrader.Runtime

run_cmd do
  let environment := (← getEnv).toKernelEnv
  let some id := taskID "populationCount64" | throwError "Population count task name rejected"
  let cases : Array (List Byte × Name) := #[
    (Corpus.V1.PopcountCode.bytes .defaultGCC, ``raw_gcc),
    (Corpus.V1.PopcountCode.bytes .defaultClang, ``raw_clang)]
  for (bytes, proof) in cases do
    match checkExpr environment {} (expectedClaim id bytes) (mkConst proof)
        `EDSLGrader.Internal.popcountPositive with
    | .error failure => throwError "Valid population count claim rejected: {failure}"
    | .ok _ => pure ()
    -- Authentic exact code and a valid proof for a different mathematical task
    -- must be rejected; a changed last RET must also fail the expected type.
    for (expected, label) in #[
        (expectedClaim .byteSwap64 bytes, "wrong task"),
        (expectedClaim id (bytes.dropLast ++ [0x90]), "changed RET")] do
      match checkExpr environment {} expected (mkConst proof)
          `EDSLGrader.Internal.popcountNegative with
      | .ok _ => throwError "Population count proof accepted for {label}"
      | .error failure =>
        unless failure.kind == .rejected && failure.message == "kernel declTypeMismatch" do
          throwError "Population count {label} failed for an unexpected reason: {failure}"
  logInfo "Population count controller accepts two exact claims and rejects wrong task/changed RET at defaults"

end EDSL.Tests.GradingPopcount
#audit_edsl
