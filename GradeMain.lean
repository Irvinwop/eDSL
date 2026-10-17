/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Driver

open EDSLGrader EDSLGrader.Runtime

def main (args : List String) : IO UInt32 := do
  let stderr ← IO.getStderr
  let selected := match args with
    | [task, input, proof] => (taskID task).map fun id => (id, input, proof, none)
    | ["--elf", span, task, input, proof] => do
      let id ← taskID task
      let span ← span.toNat?
      pure (id, input, proof, some span)
    | _ => none
  let some (id, input, proof, span) := selected | do
    stderr.putStrLn "usage: edsl-grade [--elf SPAN_BYTES] {pair32|stride32|write32|storeReturn32|storeReturnValue64|countedStore64|maximum64|minimum64|signedMaximum64|arrayMaximum64|arraySum64} INPUT PROOF.json"
    return 2
  try
    let limits : Limits := {}
    let raw ← readBounded input (if span.isSome then 65536 else 4096)
    let packet ← readPacket proof limits
    let env ← trustedEnvironment
    let result := do
      let raw ← raw
      let packet ← packet
      grade env.toKernelEnv limits id (makeArtifact raw span) packet
    match result with
    | .error failure =>
      stderr.putStrLn s!"{repr failure.kind}: {failure.message}; no defect conclusion"
      return failureStatus failure.kind
    | .ok accepted =>
      IO.println s!"ACCEPTED: fixed task, exact artifact, current OS authority and registered effects; codeBytes={accepted.codeBytes}, auxiliaryDeclarations={accepted.declarations}, decoderSteps={accepted.decoderSteps}, kernelChecks={accepted.kernelChecks}"
      return 0
  catch _ =>
    stderr.putStrLn "internal: IO or trusted installation failure; no defect conclusion"
    return 1
