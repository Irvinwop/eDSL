/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Certificate
import EDSL.Audit
import Lean

open EDSL.Certificate

private def parameters (profile : Profile) : String :=
  let code := "    (code : CodeAt initial.memory initial.rip observedBytes)\n"
  let stack := "    (stack : readWord initial.memory (initial.registers .rsp) = .ok returnAddress)\n" ++
    "    (returnValid : canonical returnAddress = true) :\n"
  match profile with
  | .increment =>
    "(initial : State) (returnAddress : Word)\n" ++ code ++ stack
  | .load32 =>
    "(initial : State) (value : BitVec 32) (returnAddress : Word)\n" ++ code ++
    "    (data : loadDWord initial.memory (initial.registers .rdi) = .ok value)\n" ++ stack
  | .store32 =>
    "(initial : State) (returnAddress : Word)\n" ++ code ++
    "    (allowed : canStoreDWord initial.memory (initial.registers .rdi) = true)\n" ++
    "    (codeDisjoint : DWordDisjoint (initial.registers .rdi) initial.rip observedBytes.length)\n" ++
    "    (stackDisjoint : DWordDisjoint (initial.registers .rdi) (initial.registers .rsp) 8)\n" ++ stack

private def finalExpression : Profile → String
  | .increment => "Examples.Compiler.Increment.finalState initial returnAddress"
  | .load32 => "Examples.Compiler.MemoryOps.loadFinal initial value returnAddress"
  | .store32 => "Examples.Compiler.MemoryOps.storeFinal initial returnAddress"

private def proofExpression : Profile → String
  | .increment =>
    "Certificate.increment_sound observedBytes (by decide) initial returnAddress code stack returnValid"
  | .load32 =>
    "Certificate.load32_sound observedBytes (by decide) initial value returnAddress code data stack returnValid"
  | .store32 =>
    "Certificate.store32_sound observedBytes (by decide) initial returnAddress code allowed codeDisjoint stackDisjoint stack returnValid"

private def certificateSource (profile : Profile) (bytes : List EDSL.X86.Byte) : String :=
  let literals := String.intercalate ", " (bytes.map (fun byte => toString byte.toNat))
  let final := finalExpression profile
  "import EDSL.Certificate\nimport EDSL.Audit\n\n" ++
  "namespace EDSL.Generated\nopen X86\n" ++
  s!"def observedBytes : List Byte := [{literals}]\n\n" ++
  "theorem certified " ++ parameters profile ++
  s!"    Executes initial ({final}) 2 ∧\n" ++
  "    ¬ Diverges initial ∧\n" ++
  "    ∀ final count, Executes initial final count →\n" ++
  s!"      final = {final} ∧ count = 2 :=\n" ++
  "  " ++ proofExpression profile ++ "\n" ++
  "end EDSL.Generated\n\n#audit_edsl\n"

private def parseArguments : List String → Option (Profile × String × String)
  | [input, output] => some (.increment, input, output)
  | [name, input, output] => (Profile.parse name).map (fun profile => (profile, input, output))
  | _ => none

def main (arguments : List String) : IO UInt32 := do
  let stderr ← IO.getStderr
  let some (profile, input, output) := parseArguments arguments | do
    stderr.putStrLn "usage: edsl-certify [increment|load32|store32] FUNCTION.bin CERTIFICATE.lean"
    return 2
  let raw ← IO.FS.readBinFile input
  let bytes := raw.data.toList.map (fun byte => BitVec.ofNat 8 byte.toNat)
  if !accepts profile bytes then
    stderr.putStrLn s!"UNVERIFIED: bytes are unsupported by the {profile.name} contract profile; no defect conclusion"
    return 3
  let outputPath : System.FilePath := output
  if let some parent := outputPath.parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile outputPath (certificateSource profile bytes)
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
  stdout.putStrLn s!"CERTIFIED {profile.name}: {raw.size} exact bytes; all admitted entries; two modeled instructions; certificate {absolute}"
  return 0
