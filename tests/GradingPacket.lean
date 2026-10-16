/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Driver
import EDSL.Grading.Export

open Lean EDSLGrader EDSLGrader.Runtime EDSL EDSL.Grading

namespace GradingPacketTests

private def unwrap (result : Except Failure α) : IO α :=
  match result with
  | .ok value => pure value
  | .error failure => throw (IO.userError s!"{failure}")

private def require (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def malformed (env : Kernel.Environment) (packet : String) : IO Unit :=
  match checkPacket env {} (mkConst ``True) packet with
  | .error failure => require (failure.kind == .malformed)
      s!"mixed packet representation failed for an unexpected reason: {failure}"
  | .ok _ => throw (IO.userError "mixed packet representation was accepted")

def main : IO Unit := do
  let (trustedEnv, clientEnv) ← Export.loadEnvironments `tests.fixtures.StrideMov
  let trusted := trustedEnv.toKernelEnv
  require ((trusted.find? `EDSL.StrideMov.claim).isNone)
    "candidate module was imported into the trusted snapshot"
  require ((clientEnv.toKernelEnv.find? `EDSL.StrideMov.claim).isSome)
    "stride client module was not loaded"
  let (writeTrusted, writeClient) ← Export.loadEnvironments `tests.fixtures.WriteIntermediate
  require ((writeTrusted.toKernelEnv.find? `EDSL.WriteIntermediateSupported.claim).isNone)
    "mutable candidate module was imported into the trusted snapshot"
  require ((writeClient.toKernelEnv.find? `EDSL.WriteIntermediateSupported.claim).isSome)
    "mutable client module was not loaded"
  let tree ← unwrap (encodeTreePacket [] (mkConst ``True.intro))
  let shared ← unwrap (encodePacket [] (mkConst ``True.intro))
  let _ ← unwrap (checkPacket trusted {} (mkConst ``True) tree)
  let _ ← unwrap (checkPacket trusted {} (mkConst ``True) shared)
  malformed trusted (tree.replace "edsl-proof-v1" "edsl-proof-v2")
  malformed trusted (shared.replace "edsl-proof-v2" "edsl-proof-v1")
  malformed trusted (shared.replace "edsl-proof-v2" "edsl-proof-v3")

  -- Full fresh implementation replay runs through the installed native CLI in
  -- verify-grading.sh, including raw/ELF reference/body and mutated code. Avoid
  -- duplicating those full replays inside the elaborator's evaluation budget.
  IO.println "Version dispatch, legacy compatibility, and trusted snapshot isolation passed"

#eval main
end GradingPacketTests
