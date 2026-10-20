/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Process.WriteExit
import EDSL.Audit
import Lean

private def source (writing : Bool) (bytes : List EDSL.X86.Byte) (image : EDSL.ELF.Image) : String :=
  let literals := String.intercalate ", " (bytes.map fun byte => toString byte.toNat)
  let segments := String.intercalate ", " (image.segments.map fun segment =>
    s!"⟨{segment.offset}, {segment.virtualAddress}, {segment.fileSize}, {segment.memorySize}, {segment.flags}, {segment.alignment}⟩")
  let checker := if writing then "checkWriteExit42" else "checkExit42"
  let specification := if writing then "WriteExitGuarantee" else "Exit42Guarantee"
  let proof := if writing then "writeExit_standalone" else "exit42_standalone"
  let prior := if writing then "" else " OS.AddressSpace.empty"
  "import EDSL.Process.WriteExit\nimport EDSL.Audit\n\n" ++
  "namespace EDSL.Generated.ExitProcess\nopen X86\n" ++
  "set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n" ++
  s!"def observedELF : List Byte := [{literals}]\n" ++
  s!"def observedImage : ELF.Image := ⟨{image.entry}, [{segments}]⟩\n" ++
  s!"theorem checked : Process.{checker} observedELF observedImage = true := by decide\n\n" ++
  "theorem certified (initial : State) :\n" ++
  s!"    Process.{specification} observedELF observedImage{prior} initial :=\n" ++
  s!"  Process.{proof} observedELF observedImage checked initial\n\n" ++
  "end EDSL.Generated.ExitProcess\n\n#audit_edsl\n"

def main (arguments : List String) : IO UInt32 := do
  let stderr ← IO.getStderr
  let selected := match arguments with
    | [input, output] => some (false, input, output)
    | ["exit42", input, output] => some (false, input, output)
    | ["write-exit42", input, output] => some (true, input, output)
    | _ => none
  let some (writing, input, output) := selected | do
    stderr.putStrLn "usage: edsl-certify-process [exit42|write-exit42] PROCESS.elf CERTIFICATE.lean"
    return 2
  let raw ← IO.FS.readBinFile input
  let bytes := raw.data.toList.map fun byte => BitVec.ofNat 8 byte.toNat
  let .ok image := EDSL.ELF.parse bytes | do
    stderr.putStrLn "UNVERIFIED: ELF is outside the supported process container profile; no defect conclusion"
    return 3
  let profileChecked := if writing then EDSL.Process.checkWriteExit42 bytes image
    else EDSL.Process.checkExit42 bytes image
  if !profileChecked then
    stderr.putStrLn "UNVERIFIED: ELF entry does not implement the selected process profile; no defect conclusion"
    return 3
  let outputPath : System.FilePath := output
  if let some parent := outputPath.parent then IO.FS.createDirAll parent
  IO.FS.writeFile outputPath (source writing bytes image)
  let absolute ← IO.FS.realPath outputPath
  let checked ← IO.Process.output { cmd := "lean", args := #["-DwarningAsError=true", absolute.toString] }
  if checked.exitCode != 0 then
    stderr.putStr checked.stdout
    stderr.putStr checked.stderr
    stderr.putStrLn "UNVERIFIED: process certificate failed Lean checking"
    return 1
  let stdout ← IO.getStdout
  stdout.putStr checked.stdout
  let description := if writing then
    "write-exit42: completed modeled output is a prefix of OK/newline; 8 user instructions across a completed write; final modeled exit status 42; write completion and exit progress are explicit"
    else "exit42: 3 user instructions; every completed modeled Linux-exit trace has status 42; progress is explicit"
  stdout.putStrLn s!"CERTIFIED {raw.size} exact ELF bytes; {description}; {absolute}"
  return 0
