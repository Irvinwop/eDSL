/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.AtomicSet64.Artifact
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
  | .truncated => malformed "truncated ELF header or segment"
  | .badMagic => malformed "ELF magic is absent"
  | error => unsupported s!"ELF container: {reprStr error}"

private def parseOperation : String → Option Logical64.Operation
  | "and" => some .intersection
  | "or" => some .union
  | "xor" => some .symmetricDifference
  | _ => none

/-- Bound growing files and streams, reading one extra byte to reject an
overlong whole artifact instead of certifying a truncated five-byte prefix. -/
private def readBounded (path : System.FilePath) (limit : Nat) : IO (Except Rejection ByteArray) :=
  IO.FS.withFile path .read fun handle => do
    let mut bytes := ByteArray.empty
    let mut done := false
    for _ in List.range (limit / 4096 + 2) do
      if !done then
        let chunk ← handle.read (USize.ofNat (min 4096 (limit + 1 - bytes.size)))
        bytes := bytes ++ chunk
        if bytes.size > limit then
          return .error (unsupported "complete input exceeds the profile byte limit")
        if chunk.isEmpty then done := true
    if !done then return .error (unsupported "complete input exceeds the profile byte limit")
    return .ok bytes

private def analyze (operation : Logical64.Operation) (file : List X86.Byte) (elf : Bool) :
    Except Rejection String := do
  if elf then
    let image ← (ELF.parse file).mapError containerFailure
    if !AtomicSet64.Artifact.completeText image then
      throw (unsupported "requires one complete five-byte executable segment beginning at entry, with no executable prefix/suffix/BSS")
    if !AtomicSet64.Artifact.checkELF operation file image then
      throw (unsupported "complete ELF code differs from the selected locked AND64/OR64/XOR64 with RET")
    return AtomicSet64.Artifact.elfSource operation file image
  else
    if file.isEmpty then throw (malformed "empty raw function")
    if !AtomicSet64.Artifact.checkRaw operation file then
      throw (unsupported "complete raw bytes differ from the selected locked AND64/OR64/XOR64 with RET")
    return AtomicSet64.Artifact.rawSource operation file

def main (arguments : List String) : IO UInt32 := do
  let stderr ← IO.getStderr
  let selected := match arguments with
    | [task, input, output] =>
      if input == "--elf" then none
      else (parseOperation task).map fun operation => (operation, input, output, false)
    | [task, "--elf", input, output] =>
      (parseOperation task).map fun operation => (operation, input, output, true)
    | _ => none
  let some (operation, input, output, elf) := selected | do
    stderr.putStrLn "usage: edsl-certify-atomic-set64 and|or|xor [--elf] INPUT CERTIFICATE.lean"
    return 2
  try
    let read ← readBounded input (if elf then ELF.maxFileSize else 5)
    let .ok raw := read | do
      let .error rejection := read | return 1
      stderr.putStrLn rejection.message
      return rejection.status
    let file := raw.data.toList.map fun byte => BitVec.ofNat 8 byte.toNat
    let analyzed := analyze operation file elf
    let .ok source := analyzed | do
      let .error rejection := analyzed | return 1
      stderr.putStrLn rejection.message
      return rejection.status
    let outputPath : System.FilePath := output
    if let some parent := outputPath.parent then IO.FS.createDirAll parent
    IO.FS.writeFile outputPath source
    let absolute ← IO.FS.realPath outputPath
    -- The CLI owns the checking lock. Callers must not hold it around the CLI.
    let checked ← IO.Process.output { cmd := "flock", args := #[
      "/tmp/edsl-lean-build.lock", "lean", "-DwarningAsError=true", absolute.toString] }
    if checked.exitCode != 0 then
      stderr.putStr checked.stdout
      stderr.putStr checked.stderr
      stderr.putStrLn "CERTIFICATE-FAILURE: kernel checking failed; no certification or defect conclusion"
      return 1
    let stdout ← IO.getStdout
    stdout.putStr checked.stdout
    stdout.putStrLn s!"CERTIFIED: {raw.size} literal artifact bytes; complete locked {reprStr operation}/RET, current actor/code/stack authority, independent set membership, all AF streams, one event and exactly two retired instructions. Source/TSO/physical/kernel refinement remains external; {absolute}"
    return 0
  catch error =>
    stderr.putStrLn s!"IO-FAILURE: {error}; no certification or defect conclusion"
    return 5
