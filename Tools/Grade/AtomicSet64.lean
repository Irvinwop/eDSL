/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.AtomicSet64.Driver

open EDSL EDSLGrader EDSLGrader.Runtime

private def parseOperation : String → Option Logical64.Operation
  | "intersection" => some .intersection
  | "union" => some .union
  | "symmetricDifference" => some .symmetricDifference
  | _ => none

def main (args : List String) : IO UInt32 := do
  let stderr ← IO.getStderr
  let selected := match args with
    | [task, input, proof] =>
      if input == "--elf" then none
      else (parseOperation task).map fun desired => (desired, input, proof, none)
    | [task, "--elf", span, input, proof] => do
      let desired ← parseOperation task
      let length ← span.toNat?
      pure (desired, input, proof, some length)
    | _ => none
  let some (desired, input, proof, span) := selected | do
    stderr.putStrLn "usage: edsl-grade-atomic-set64 intersection|union|symmetricDifference [--elf SPAN_BYTES] INPUT PROOF.json"
    return 2
  try
    let limits : Limits := {}
    let raw ← readBounded input (if span.isSome then 65536 else 4096)
    let packet ← readPacket proof limits
    let env ← trustedEnvironment
    let result := do
      let raw ← raw
      let packet ← packet
      EDSLGrader.AtomicSet64.grade env.toKernelEnv limits desired (makeArtifact raw span) packet
    match result with
    | .error failure =>
      stderr.putStrLn s!"{repr failure.kind}: {failure.message}; no defect conclusion"
      return failureStatus failure.kind
    | .ok accepted =>
      IO.println s!"ACCEPTED: uninterrupted full64 {reprStr desired} calls, exact selected artifact bytes, current actor/code/caller authority and actual ordered CPU/OS events, including mixed operations; codeBytes={accepted.codeBytes}, auxiliaryDeclarations={accepted.declarations}, decoderSteps={accepted.decoderSteps}, kernelChecks={accepted.kernelChecks}. Source memory-order, concurrent compound-call linearizability, whole-OS and physical/kernel refinement remain external."
      return 0
  catch _ =>
    stderr.putStrLn "internal: IO or trusted installation failure; no defect conclusion"
    return 1
