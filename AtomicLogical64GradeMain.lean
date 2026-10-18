/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.AtomicLogical64.Driver

open EDSLGrader EDSLGrader.Runtime

def main (args : List String) : IO UInt32 := do
  let stderr ← IO.getStderr
  let selected := match args with
    | [input, proof] => if input == "--elf" then none else some (input, proof, none)
    | ["--elf", span, input, proof] => do
      let length ← span.toNat?
      pure (input, proof, some length)
    | _ => none
  let some (input, proof, span) := selected | do
    stderr.putStrLn "usage: edsl-grade-atomic-logical64 [--elf SPAN_BYTES] INPUT PROOF.json"
    return 2
  try
    let limits : Limits := {}
    let raw ← readBounded input (if span.isSome then 65536 else 4096)
    let packet ← readPacket proof limits
    let env ← trustedEnvironment
    let result := do
      let raw ← raw
      let packet ← packet
      AtomicLogical64.grade env.toKernelEnv limits (makeArtifact raw span) packet
    match result with
    | .error failure =>
      stderr.putStrLn s!"{repr failure.kind}: {failure.message}; no defect conclusion"
      return failureStatus failure.kind
    | .ok accepted =>
      IO.println s!"ACCEPTED: fixed full64 atomic union, exact selected artifact bytes, current actor/code/caller authority and actual CPU/OS trace; codeBytes={accepted.codeBytes}, auxiliaryDeclarations={accepted.declarations}, decoderSteps={accepted.decoderSteps}, kernelChecks={accepted.kernelChecks}. Source memory-order, concurrent linearizability and physical/kernel refinement remain external."
      return 0
  catch _ =>
    stderr.putStrLn "internal: IO or trusted installation failure; no defect conclusion"
    return 1
