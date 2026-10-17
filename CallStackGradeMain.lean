/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.CallStack.Driver

open EDSLGrader EDSLGrader.Runtime

def main (args : List String) : IO UInt32 := do
  let stderr ← IO.getStderr
  let selected := match args with
    | [entry, input, proof] => do
      let offset ← entry.toNat?
      pure (offset, input, proof, none)
    | ["--elf", span, entry, input, proof] => do
      let length ← span.toNat?
      let offset ← entry.toNat?
      pure (offset, input, proof, some length)
    | _ => none
  let some (entry, input, proof, span) := selected | do
    stderr.putStrLn "usage: edsl-grade-call-stack [--elf SPAN_BYTES] ENTRY_OFFSET INPUT PROOF.json"
    return 2
  try
    let limits : Limits := {}
    let raw ← readBounded input (if span.isSome then 65536 else 4096)
    let packet ← readPacket proof limits
    let env ← trustedEnvironment
    let result := do
      let raw ← raw
      let packet ← packet
      CallStack.grade env.toKernelEnv limits (CallStack.makeArtifact raw entry span) packet
    match result with
    | .error failure =>
      stderr.putStrLn s!"{repr failure.kind}: {failure.message}; no defect conclusion"
      return failureStatus failure.kind
    | .ok accepted =>
      IO.println s!"ACCEPTED: fixed call contract, exact artifact, selected entry and current OS resources; codeBytes={accepted.codeBytes}, auxiliaryDeclarations={accepted.declarations}, decoderSteps={accepted.decoderSteps}, kernelChecks={accepted.kernelChecks}"
      return 0
  catch _ =>
    stderr.putStrLn "internal: IO or trusted installation failure; no defect conclusion"
    return 1
