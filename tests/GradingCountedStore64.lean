/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Driver
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.GradingCountedStore64
open EDSL X86 X86.Sequential Grading CountedStore64

/-- Even a truncated FF group instruction has independently inhabited,
useful raw and current ownership domains. Admission never assumes execution. -/
theorem unsupported_domain : Nonvacuous (registered .countedStore64) [0xff] :=
  domain_nonvacuous .countedStore64 [0xff] (by decide) (by decide)

theorem unsupported_not_claim : ¬Claim .countedStore64 [0xff] := by
  intro claim
  let witness := CountedStore64.Domain.unsupported
  have total := (claim.1.machine (resourceInput witness.resource)
    witness.initial witness.pre.machine).1
  have decoded : Sequential.decodeAt witness.initial = .error (.inaccessibleInstruction 4097) :=
    CountedStore64.Domain.unsupported_rejected
  have fault : step false witness.initial = .error (.inaccessibleInstruction 4097) := by
    simp only [Sequential.step, decoded, error_bind]
  have impossible := total.no_fault_prefix (fun _ => false)
    (Sequential.run_fault (choices := fun _ => false) (fuel := 0) fault)
  cases impossible

end EDSL.Tests.GradingCountedStore64

open Lean EDSL EDSL.Grading EDSLGrader EDSLGrader.Runtime

/-- Check the real data-only runtime against fresh trusted modules. A proof
for either complete compiler window must fail for changed bytes or task. -/
def checkCountedPackets : IO Unit := do
  initSearchPath (← findSysroot)
  let trusted ← importModules #[{ module := `EDSL.Grading.Known },
    { module := `EDSL.Grading.Artifact },
    { module := `EDSL.Grading.CallStack.Artifact },
    { module := `EDSL.Grading.CallMemory64.Artifact },
    { module := `EDSL.Grading.CallMemoryLoop64.Artifact },
    { module := `EDSL.Grading.AtomicLogical64.Artifact },
    { module := `EDSL.Grading.AtomicSet64.Artifact }]
    {} (trustLevel := 0) (plugins := #[]) (loadExts := false)
  let env := trusted.toKernelEnv
  let some id := taskID "countedStore64" | throw (IO.userError "counted task spelling rejected")
  for (bytes, name) in [(CountedStore64.GCC.bytes, ``Known.countedStore64GCC),
      (CountedStore64.Clang.bytes, ``Known.countedStore64Clang)] do
    for (dialect, encoded) in [("v1", encodeTreePacket [] (mkConst name)),
        ("v2", encodePacket [] (mkConst name))] do
      let packet ← match encoded with
        | .ok packet => pure packet
        | .error failure => throw (IO.userError s!"packet encoding failed: {failure}")
      let accepted ← match grade env {} id (.raw bytes) packet with
        | .ok checked => pure checked
        | .error failure => throw (IO.userError s!"{name} {dialect} rejected: {failure}")
      for (wrongTask, wrongBytes) in [(TaskID.storeReturnValue64, bytes),
          (id, bytes ++ [0x90])] do
        match grade env {} wrongTask (.raw wrongBytes) packet with
        | .ok _ => throw (IO.userError s!"{name} {dialect} accepted different task or bytes")
        | .error failure =>
          unless failure.kind == .rejected do
            throw (IO.userError s!"wrong task/bytes failed for unexpected reason: {failure}")
      IO.println s!"PASS {name} {dialect}: audit={accepted.auditSteps}; changed task/bytes rejected"

#eval checkCountedPackets

#print axioms EDSL.Grading.Known.countedStore64GCC
#print axioms EDSL.Grading.Known.countedStore64Clang
#print axioms EDSL.Tests.GradingCountedStore64.unsupported_not_claim
#audit_edsl
