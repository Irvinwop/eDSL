/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.StoreReturn32.Artifact
import Lean

open EDSL

private structure Rejection where
  status : UInt32
  message : String

private def unsupported (message : String) : Rejection :=
  ⟨3, "UNSUPPORTED: " ++ message ++ "; no defect conclusion"⟩

private def malformed (message : String) : Rejection :=
  ⟨4, "MALFORMED: " ++ message ++ "; no defect conclusion"⟩

private def containerFailure : ELF.Error → Rejection
  | .truncated => malformed "truncated ELF header or file-backed segment"
  | .badMagic => malformed "ELF magic is absent"
  | .invalidImage => unsupported "ELF segment/entry constraints are outside the admitted profile"
  | error => unsupported s!"ELF container: {reprStr error}"

private def windowFailure : Sum32.Artifact.EntryError → Rejection
  | .decode offset (.inaccessibleInstruction _) =>
    malformed s!"incomplete executable instruction at offset {offset}"
  | .decode offset error => unsupported s!"sequential decoder at offset {offset}: {reprStr error}"
  | .byteLimit => unsupported "no complete RET-terminated entry window within 64 bytes"
  | .instructionLimit => unsupported "no RET within 32 sequentially decoded instructions"

private structure Candidate where
  source : String
  shape : StoreReturn32.Shape
  codeBytes : Nat

private def analyze (file : List X86.Byte) (elf : Bool) : Except Rejection Candidate := do
  if elf then
    let image ← (ELF.parse file).mapError containerFailure
    let bytes ← (Sum32.Artifact.entryWindow file image).mapError windowFailure
    let some shape := StoreReturn32.check bytes |
      throw (unsupported "entry window is outside the store-return32 shapes")
    if !ELF.checkEntry file image bytes then
      throw (unsupported "selected entry window is not a complete executable file-backed interval")
    return ⟨StoreReturn32.Artifact.elfSource file bytes image shape, shape, bytes.length⟩
  else
    if file.isEmpty then throw (malformed "empty raw function window")
    let some shape := StoreReturn32.check file |
      throw (unsupported "complete raw window is outside the store-return32 shapes")
    return ⟨StoreReturn32.Artifact.rawSource file shape, shape, file.length⟩

def main (arguments : List String) : IO UInt32 := do
  let stderr ← IO.getStderr
  let selected := match arguments with
    | [input, output] => if input == "--elf" then none else some (input, output, false)
    | ["--elf", input, output] => some (input, output, true)
    | _ => none
  let some (input, output, elf) := selected | do
    stderr.putStrLn "usage: edsl-certify-store-return32 [--elf] INPUT CERTIFICATE.lean"
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
    -- This CLI owns the checking lock; callers must not hold it around the CLI.
    let checked ← IO.Process.output { cmd := "flock", args := #[
      "/tmp/edsl-lean-build.lock", "lean", "-DwarningAsError=true", absolute.toString] }
    if checked.exitCode != 0 then
      stderr.putStr checked.stdout
      stderr.putStr checked.stderr
      stderr.putStrLn "CERTIFICATE-FAILURE: kernel checking failed; no certification or defect conclusion"
      return 1
    let stdout ← IO.getStdout
    stdout.putStr checked.stdout
    stdout.putStrLn s!"CERTIFIED: {raw.size} literal artifact bytes, {candidate.codeBytes} function bytes, shape {candidate.shape.name}; low32 store and full pointer return for all admitted inputs/AF choices, exactly 3 instructions and stack8 operand read; current caller OS resources and native/kernel conformance remain explicit; {absolute}"
    return 0
  catch error =>
    stderr.putStrLn s!"IO-FAILURE: {error}; no certification or defect conclusion"
    return 5
