/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Certificate
import EDSL.Audit
import Lean

private def certificateSource (bytes : List EDSL.X86.Byte) : String :=
  let literals := String.intercalate ", " (bytes.map (fun byte => toString byte.toNat))
  "import EDSL.Certificate\nimport EDSL.Audit\n\n" ++
  "namespace EDSL.Generated\nopen X86\n" ++
  s!"def observedBytes : List Byte := [{literals}]\n\n" ++
  "theorem certified (initial : State) (returnAddress : Word)\n" ++
  "    (code : CodeAt initial.memory initial.rip observedBytes)\n" ++
  "    (stack : readWord initial.memory (initial.registers .rsp) = .ok returnAddress)\n" ++
  "    (returnValid : canonical returnAddress = true) :\n" ++
  "    Executes initial (Examples.Compiler.Increment.finalState initial returnAddress) 2 ∧\n" ++
  "    ¬ Diverges initial ∧\n" ++
  "    ∀ final count, Executes initial final count →\n" ++
  "      final = Examples.Compiler.Increment.finalState initial returnAddress ∧ count = 2 :=\n" ++
  "  Certificate.increment_sound observedBytes (by decide) initial returnAddress code stack returnValid\n" ++
  "end EDSL.Generated\n\n#audit_edsl\n"

def main (arguments : List String) : IO UInt32 := do
  let stderr ← IO.getStderr
  let [input, output] := arguments | do
    stderr.putStrLn "usage: edsl-certify FUNCTION.bin CERTIFICATE.lean"
    return 2
  let raw ← IO.FS.readBinFile input
  let bytes := raw.data.toList.map (fun byte => BitVec.ofNat 8 byte.toNat)
  if !EDSL.Certificate.acceptsIncrement bytes then
    stderr.putStrLn "UNVERIFIED: bytes are unsupported by the increment contract profile; no defect conclusion"
    return 3
  let outputPath : System.FilePath := output
  if let some parent := outputPath.parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile outputPath (certificateSource bytes)
  let absolute ← IO.FS.realPath outputPath
  let checked ← IO.Process.output {
    cmd := "lean"
    args := #["-DwarningAsError=true", absolute.toString]
  }
  if checked.exitCode != 0 then
    stderr.putStr checked.stdout
    stderr.putStr checked.stderr
    stderr.putStrLn "UNVERIFIED: Lean certificate checking failed"
    return 1
  let stdout ← IO.getStdout
  stdout.putStr checked.stdout
  stdout.putStrLn s!"CERTIFIED: {raw.size} exact bytes; all 32-bit inputs; two modeled instructions; certificate {absolute}"
  return 0
