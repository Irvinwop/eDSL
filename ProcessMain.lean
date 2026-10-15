/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Process.Certificate
import EDSL.Audit
import Lean

private def source (bytes : List EDSL.X86.Byte) (image : EDSL.ELF.Image) : String :=
  let literals := String.intercalate ", " (bytes.map fun byte => toString byte.toNat)
  let segments := String.intercalate ", " (image.segments.map fun segment =>
    s!"⟨{segment.offset}, {segment.virtualAddress}, {segment.fileSize}, {segment.memorySize}, {segment.flags}, {segment.alignment}⟩")
  "import EDSL.Process.Certificate\nimport EDSL.Audit\n\n" ++
  "namespace EDSL.Generated.ExitProcess\nopen X86\n" ++
  "set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n" ++
  s!"def observedELF : List Byte := [{literals}]\n" ++
  s!"def observedImage : ELF.Image := ⟨{image.entry}, [{segments}]⟩\n" ++
  "theorem checked : Process.checkExit42 observedELF observedImage = true := by decide\n\n" ++
  "theorem certified (initial : State) :\n" ++
  "    Process.Exit42Guarantee observedELF observedImage OS.AddressSpace.empty initial :=\n" ++
  "  Process.exit42_standalone observedELF observedImage checked initial\n\n" ++
  "end EDSL.Generated.ExitProcess\n\n#audit_edsl\n"

def main (arguments : List String) : IO UInt32 := do
  let stderr ← IO.getStderr
  let [input, output] := arguments | do
    stderr.putStrLn "usage: edsl-certify-process EXIT42.elf CERTIFICATE.lean"
    return 2
  let raw ← IO.FS.readBinFile input
  let bytes := raw.data.toList.map fun byte => BitVec.ofNat 8 byte.toNat
  let .ok image := EDSL.ELF.parse bytes | do
    stderr.putStrLn "UNVERIFIED: ELF is outside the supported process container profile; no defect conclusion"
    return 3
  if !EDSL.Process.checkExit42 bytes image then
    stderr.putStrLn "UNVERIFIED: ELF entry does not implement the exit42 process profile; no defect conclusion"
    return 3
  let outputPath : System.FilePath := output
  if let some parent := outputPath.parent then IO.FS.createDirAll parent
  IO.FS.writeFile outputPath (source bytes image)
  let absolute ← IO.FS.realPath outputPath
  let checked ← IO.Process.output { cmd := "lean", args := #["-DwarningAsError=true", absolute.toString] }
  if checked.exitCode != 0 then
    stderr.putStr checked.stdout
    stderr.putStr checked.stderr
    stderr.putStrLn "UNVERIFIED: process certificate failed Lean checking"
    return 1
  let stdout ← IO.getStdout
  stdout.putStr checked.stdout
  stdout.putStrLn s!"CERTIFIED exit42 ELF: {raw.size} exact bytes; 3 user instructions; every completed modeled Linux-exit trace has status 42; progress is explicit; {absolute}"
  return 0
