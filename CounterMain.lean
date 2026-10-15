/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CounterCertificate
import EDSL.ELF.Loader
import EDSL.Audit
import Lean

private def byteLiterals (bytes : List EDSL.X86.Byte) : String :=
  String.intercalate ", " (bytes.map (fun byte => toString byte.toNat))

private def header : String :=
  "import EDSL.CounterCertificate\nimport EDSL.ELF.Loader\nimport EDSL.Audit\n\n" ++
  "namespace EDSL.GeneratedCounter\nopen X86 OS.AddressSpace\n" ++
  "set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n"

private def parameters : String :=
  "(state : OS.CounterThreads.State) (address : Word) (initial : BitVec 32)\n" ++
  "    (prepared : CounterCertificate.Prepared state)\n" ++
  "    (allAt : OS.CounterThreads.AllAt state address)\n" ++
  "    (observed : loadDWord (toMemory state.shared.shared.resources.space) address = .ok initial)\n" ++
  "    (started : ∀ identifier worker, state.workers identifier = some worker → worker.phase = .entry)\n"

private def conclusion : String :=
  "    CounterCertificate.Execution state address initial ∧\n" ++
  "    CounterCertificate.CompletedSpecification state address initial"

private def source (bytes : List EDSL.X86.Byte) : String :=
  header ++ s!"def observedBytes : List Byte := [{byteLiterals bytes}]\n\n" ++
  "theorem accepted : CounterCertificate.accepts observedBytes = true := by decide\n\n" ++
  "theorem certified " ++ parameters ++
  "    (code : ∀ identifier worker, state.workers identifier = some worker →\n" ++
  "      CodeAt (toMemory state.shared.shared.resources.space) worker.entry.rip observedBytes) :\n" ++
  conclusion ++ " :=\n" ++
  "  CounterCertificate.sound observedBytes accepted state address initial prepared code allAt observed started\n\n" ++
  "end EDSL.GeneratedCounter\n\n#audit_edsl\n"

private def elfSource (file : List EDSL.X86.Byte) (image : EDSL.ELF.Image) : String :=
  let segments := String.intercalate ", " (image.segments.map fun segment =>
    s!"⟨{segment.offset}, {segment.virtualAddress}, {segment.fileSize}, {segment.memorySize}, {segment.flags}, {segment.alignment}⟩")
  header ++ s!"def observedELF : List Byte := [{byteLiterals file}]\n" ++
  s!"def observedImage : ELF.Image := ⟨{image.entry}, [{segments}]⟩\n" ++
  s!"def observedBytes : List Byte := [{byteLiterals EDSL.OS.CounterThreads.bytes}]\n\n" ++
  "theorem accepted : CounterCertificate.accepts observedBytes = true := by decide\n\n" ++
  "theorem parsedImage : ELF.parse observedELF = .ok observedImage :=\n" ++
  "  ELF.checkParsed_sound observedELF observedImage (by decide)\n\n" ++
  "theorem checkedEntry : ELF.checkEntry observedELF observedImage observedBytes = true := by decide\n\n" ++
  "def loadedSpace (prior : Space) : Space := ELF.install observedELF observedImage prior\n\n" ++
  "theorem loadedCode (prior : Space) : CodeAt (toMemory (loadedSpace prior))\n" ++
  "    (ELF.codeAddress observedImage) observedBytes :=\n" ++
  "  ELF.checked_entry_code observedELF observedImage observedBytes prior checkedEntry\n\n" ++
  "theorem certified " ++ parameters ++
  "    (prior : Space) (free : ELF.fresh observedImage prior = true)\n" ++
  "    (loaded : state.shared.shared.resources.space = loadedSpace prior)\n" ++
  "    (entries : ∀ identifier worker, state.workers identifier = some worker →\n" ++
  "      worker.entry.rip = ELF.codeAddress observedImage) :\n" ++
  "    ELF.load observedELF prior = .ok ⟨observedImage, loadedSpace prior⟩ ∧\n" ++
  "    (CounterCertificate.Execution state address initial ∧\n" ++
  "      CounterCertificate.CompletedSpecification state address initial) := by\n" ++
  "  have code : ∀ identifier worker, state.workers identifier = some worker →\n" ++
  "      CodeAt (toMemory state.shared.shared.resources.space) worker.entry.rip observedBytes := by\n" ++
  "    intro identifier worker live\n" ++
  "    rw [loaded, entries identifier worker live]\n" ++
  "    exact loadedCode prior\n" ++
  "  exact ⟨ELF.load_success observedELF prior observedImage parsedImage free,\n" ++
  "    CounterCertificate.sound observedBytes accepted state address initial prepared code allAt observed started⟩\n\n" ++
  "end EDSL.GeneratedCounter\n\n#audit_edsl\n"

def main (arguments : List String) : IO UInt32 := do
  let stderr ← IO.getStderr
  let request := match arguments with
    | [input, output] => some (input, output, false)
    | ["--elf", input, output] => some (input, output, true)
    | _ => none
  let some (input, output, elf) := request | do
    stderr.putStrLn "usage: edsl-certify-counter [--elf] INPUT CERTIFICATE.lean"
    return 2
  let raw ← IO.FS.readBinFile input
  let bytes := raw.data.toList.map (fun byte => BitVec.ofNat 8 byte.toNat)
  let candidate ← if elf then
      match EDSL.ELF.parse bytes with
      | .error error =>
        stderr.putStrLn s!"UNVERIFIED: unsupported counter ELF ({reprStr error}); no defect conclusion"
        pure none
      | .ok image =>
        if EDSL.ELF.checkEntry bytes image EDSL.OS.CounterThreads.bytes then pure (some (elfSource bytes image))
        else
          stderr.putStrLn "UNVERIFIED: counter ELF entry does not match the supported loop; no defect conclusion"
          pure none
    else if EDSL.CounterCertificate.accepts bytes then pure (some (source bytes))
    else
      stderr.putStrLn "UNVERIFIED: unsupported counter-loop bytes; no defect conclusion"
      pure none
  let some candidate := candidate | return 3
  let outputPath : System.FilePath := output
  if let some parent := outputPath.parent then IO.FS.createDirAll parent
  IO.FS.writeFile outputPath candidate
  let absolute ← IO.FS.realPath outputPath
  let checked ← IO.Process.output { cmd := "lean", args := #["-DwarningAsError=true", absolute.toString] }
  if checked.exitCode != 0 then
    stderr.putStr checked.stdout
    stderr.putStr checked.stderr
    stderr.putStrLn "UNVERIFIED: counter certificate checking failed"
    return 1
  let stdout ← IO.getStdout
  stdout.putStr checked.stdout
  stdout.putStrLn s!"CERTIFIED {raw.size} exact counter-loop bytes: arbitrary finite modeled worker workloads; explicit OS resources; universal completed result and constructive finite completion; {absolute}"
  return 0
