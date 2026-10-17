/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Export

open Lean EDSLGrader.Runtime EDSLGrader.Export

private def failureStatus : FailureKind → UInt32
  | .malformed => 4
  | .unsupported => 3
  | .rejected | .audit => 5
  | .resource => 6
  | .internal => 1

def main (args : List String) : IO UInt32 := do
  let stderr ← IO.getStderr
  let selected := match args with
    | [mod, theoremText, output] => some (mod, theoremText, output, Mode.reference)
    | [mod, theoremText, output, "--body"] => some (mod, theoremText, output, Mode.body)
    | ["--body", mod, theoremText, output] => some (mod, theoremText, output, Mode.body)
    | _ => none
  let some (mod, theoremText, output, mode) := selected | do
    stderr.putStrLn "usage: edsl-proof-export MODULE THEOREM OUTPUT.json [--body]"
    return 2
  if mod.isEmpty || theoremText.isEmpty || mod.toName.isAnonymous || theoremText.toName.isAnonymous then
    stderr.putStrLn "usage: MODULE and THEOREM must be nonempty Lean names"
    return 2
  try
    let (trusted, client) ← loadEnvironments mod.toName
    match exportTheorem trusted.toKernelEnv client.toKernelEnv theoremText.toName mode with
    | .error failure =>
      stderr.putStrLn s!"{repr failure.kind}: {failure.message}"
      return failureStatus failure.kind
    | .ok packet =>
      IO.FS.writeFile output packet.text
      IO.println s!"EXPORTED: client packet; auxiliaryDeclarations={packet.declarations.length}, declaredNames={packet.declaredNames}, bytes={packet.text.utf8ByteSize}. Submit to the matching fixed-contract grader for artifact checking."
      return 0
  catch error =>
    stderr.putStrLn s!"internal: client module import or output IO failed: {error}"
    return 1
