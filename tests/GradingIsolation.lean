/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Driver
import EDSL.Grading.ExportRegistry

open Lean EDSLGrader EDSLGrader.Runtime

/-- One process per owned client keeps its real import snapshots bounded.
The client theorem must be available to export and absent from the installed
grader. Neither assertion imports the client into the trusted snapshot. -/
def main (arguments : List String) : IO Unit := do
  let (registered, selected) := match arguments with
    | "--registered" :: rest => (true, rest)
    | _ => (false, arguments)
  let [moduleText, theoremText] := selected
    | throw (IO.userError "usage: GradingIsolation.lean [--registered] MODULE THEOREM")
  let (trusted, client) ← if registered then Export.loadRegisteredEnvironments moduleText.toName
    else Export.loadEnvironments moduleText.toName
  if (trusted.toKernelEnv.find? theoremText.toName).isSome then
    throw (IO.userError s!"candidate theorem entered the trusted snapshot: {theoremText}")
  if (client.toKernelEnv.find? theoremText.toName).isNone then
    throw (IO.userError s!"client theorem was not loaded: {theoremText}")
  IO.println s!"Client export and trusted snapshot isolation passed: {theoremText}"
