/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Sum32.Artifact
import Lean

open EDSL

private structure Rejection where
  status : UInt32
  message : String

private def unsupported (message : String) : Rejection :=
  ⟨3, "UNSUPPORTED: " ++ message ++ "; no defect conclusion"⟩

private def malformed (message : String) : Rejection :=
  ⟨4, "MALFORMED: " ++ message ++ "; no defect conclusion"⟩

private def decodeFailure (offset : Nat) (error : X86.Error) : Rejection :=
  match error with
  | .inaccessibleInstruction _ => malformed s!"incomplete executable instruction at offset {offset}"
  | _ => unsupported s!"sequential decoder at offset {offset}: {reprStr error}"

private def layoutFailure : Sum32.CheckFault → Rejection
  | .decode offset error => decodeFailure offset error
  | .truncated offset => malformed s!"instruction extends beyond the raw window at offset {offset}"
  | .byteLimit => unsupported "function exceeds the 64-byte bound"
  | .instructionLimit => unsupported "function exceeds the 32-instruction bound"
  | .unsupportedLayout => unsupported "decoded graph is outside the supported sum32 contract shapes"
  | .invalidLayout => unsupported "decoded graph does not satisfy the sum32 layout/operation contract"

private def containerFailure : ELF.Error → Rejection
  | .truncated => malformed "truncated ELF header or file-backed segment"
  | .badMagic => malformed "ELF magic is absent"
  | .invalidImage => malformed "ELF segment/entry constraints failed"
  | error => unsupported s!"ELF container: {reprStr error}"

private def windowFailure : Sum32.Artifact.EntryError → Rejection
  | .decode offset error => decodeFailure offset error
  | .byteLimit => unsupported "no complete RET-terminated entry window within 64 bytes"
  | .instructionLimit => unsupported "no RET within 32 sequentially decoded instructions"

private structure Candidate where
  source : String
  codeBytes : Nat
  nodes : Nat

private def analyze (file : List X86.Byte) (elf : Bool) : Except Rejection Candidate := do
  if elf then
    let image ← (ELF.parse file).mapError containerFailure
    let bytes ← (Sum32.Artifact.entryWindow file image).mapError windowFailure
    let plan ← (Sum32.analyze bytes).mapError layoutFailure
    if !ELF.checkEntry file image bytes then
      throw (unsupported "selected entry window is not a complete executable file-backed interval")
    return ⟨Sum32.Artifact.elfSource file bytes image plan, bytes.length, plan.nodes.length⟩
  else
    if file.isEmpty then throw (malformed "empty raw function window")
    let plan ← (Sum32.analyze file).mapError layoutFailure
    return ⟨Sum32.Artifact.rawSource file plan, file.length, plan.nodes.length⟩

def main (arguments : List String) : IO UInt32 := do
  let stderr ← IO.getStderr
  let selected := match arguments with
    | [input, output] => some (input, output, false)
    | ["--elf", input, output] => some (input, output, true)
    | _ => none
  let some (input, output, elf) := selected | do
    stderr.putStrLn "usage: edsl-certify-sum32 [--elf] INPUT CERTIFICATE.lean"
    return 2
  try
    let raw ← IO.FS.readBinFile input
    let file := raw.data.toList.map fun byte => BitVec.ofNat 8 byte.toNat
    let analyzed := analyze file elf
    if let .error rejection := analyzed then
      stderr.putStrLn rejection.message
      return rejection.status
    let .ok candidate := analyzed | return 1
    let outputPath : System.FilePath := output
    if let some parent := outputPath.parent then IO.FS.createDirAll parent
    IO.FS.writeFile outputPath candidate.source
    let absolute ← IO.FS.realPath outputPath
    -- Runtime certificate checking owns this lock. Do not invoke this CLI
    -- while an outer process holds the same build lock.
    let checked ← IO.Process.output { cmd := "flock", args := #[
      "/tmp/edsl-lean-build.lock", "lean", "-DwarningAsError=true", absolute.toString] }
    if checked.exitCode != 0 then
      stderr.putStr checked.stdout
      stderr.putStr checked.stderr
      stderr.putStrLn "CERTIFICATE-FAILURE: kernel checking failed; no certification or defect conclusion"
      return 1
    let stdout ← IO.getStdout
    stdout.putStr checked.stdout
    stdout.putStrLn s!"CERTIFIED: {raw.size} literal artifact bytes, {candidate.codeBytes} function bytes, {candidate.nodes} decoded instructions; modeled sum32 for every admitted input and AF choice, with exact cost/reads and explicit caller RAM/resources; native/kernel conformance external; {absolute}"
    return 0
  catch error =>
    stderr.putStrLn s!"IO-FAILURE: {error}; no certification or defect conclusion"
    return 5
