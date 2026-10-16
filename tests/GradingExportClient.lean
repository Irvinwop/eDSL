/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Export

/-! Run after compiling tests.fixtures.GradingClient into the configured module
search path. These are real module-import/codec/kernel integration tests. The
expected proposition comes from the separate fixed trusted snapshot, never
from the client theorem's declared type. -/

set_option warningAsError true

open Lean EDSLGrader EDSLGrader.Runtime

namespace GradingExportClientTests

private def require (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap (result : Except Failure α) : IO α :=
  match result with
  | .ok value => pure value
  | .error failure => throw (IO.userError s!"unexpected failure: {failure}")

private def expectFailure (kind : FailureKind) (result : Except Failure α)
    (context : String) : IO Unit :=
  match result with
  | .error failure => require (failure.kind == kind)
      s!"{context}: wrong failure category: {failure}"
  | .ok _ => throw (IO.userError s!"{context}: unexpectedly succeeded")

private def hasName (packet : Export.Packet) (name : Name) : Bool :=
  packet.declarations.any fun decl => decl.getNames.contains name

def main : IO Unit := do
  let (trustedEnv, clientEnv) ← Export.loadEnvironments `tests.fixtures.GradingClient
  let trusted := trustedEnv.toKernelEnv
  let client := clientEnv.toKernelEnv
  let some known := trusted.find? `EDSL.Grading.Known.pair
    | throw (IO.userError "fixed pair contract unavailable")
  let expected := known.type
  for mode in [Export.Mode.reference, .body] do
    let packet ← unwrap <| Export.exportTheorem trusted client known.name mode
    require packet.declarations.isEmpty "trusted theorem unexpectedly redeclared"
    require ((packet.value == mkConst known.name) == (mode == .reference))
      "known reference/body mode did not select the requested proof"
    let _ ← unwrap <| checkPacket trusted {} expected packet.text

  for mode in [Export.Mode.reference, .body] do
    let packet ← unwrap <| Export.exportTheorem trusted client
      `GradingExportClientFixture.pair mode
    -- Require a real fresh helper closure, including an opaque proof body,
    -- parameterized recursor and mutually generated recursors. Dropping the
    -- closure below must make replay fail against the independent snapshot.
    for name in [`GradingExportClientFixture.Target, `GradingExportClientFixture.sealed,
        `GradingExportClientFixture.Header.rec, `GradingExportClientFixture.Even.rec,
        `GradingExportClientFixture.Odd.rec] do
      require (hasName packet name) s!"fresh dependency not exported: {name}"
    require ((hasName packet `GradingExportClientFixture.pair) == (mode == .reference))
      "fresh reference/body mode included the wrong root declaration"
    let checked ← unwrap <| checkPacket trusted {} expected packet.text
    require (checked.kernelChecks > 1) "fresh packet did not reconstruct helpers in the kernel"
    let stripped ← unwrap <| encodePacket [] packet.value
    expectFailure .malformed (checkPacket trusted {} expected stripped)
      "fresh closure removed"

  expectFailure .unsupported
    (Export.exportTheorem trusted client `GradingExportClientFixture.polymorphic)
    "uninstantiated theorem universes"
  expectFailure .unsupported
    (Export.exportTheorem trusted client `GradingExportClientFixture.Target)
    "definition selected as theorem"
  expectFailure .unsupported
    (Export.exportTheorem trusted client `GradingExportClientFixture.nestedPair)
    "nested inductive dependency"
  expectFailure .resource
    (Export.exportTheorem trusted client `GradingExportClientFixture.pair
      .reference { maxSteps := 0 }) "discovery budget"
  expectFailure .resource
    (Export.exportTheorem trusted client `GradingExportClientFixture.pair
      .reference { maxDeclarations := 2 }) "generated constant name budget"
  IO.println "GradingExportClient: known reference/body and fresh safe helper/inductive closure replay passed; unsupported and resource cases rejected"

#eval main

end GradingExportClientTests
