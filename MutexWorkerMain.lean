/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.MutexWorkerCertificate
import EDSL.ELF.Loader
import EDSL.Audit
import Lean

private def byteLiterals (bytes : List EDSL.X86.Byte) : String :=
  String.intercalate ", " (bytes.map (fun byte => toString byte.toNat))

private def header : String :=
  "import EDSL.MutexWorkerCertificate\nimport EDSL.ELF.Loader\nimport EDSL.Audit\n\n" ++
  "namespace EDSL.GeneratedMutexWorker\nopen X86 OS.AddressSpace OS.MutexReplay\n" ++
  "set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n"

private def theoremSource : String :=
  "theorem certified (state : OS.MutexReplay.State) (config : OS.Mutex.Config) (initial : BitVec 32)\n" ++
  "    (valid : Invariant config state) (ready : ExecutionReady state) (closed : ClosedUnderTwo config)\n" ++
  "    (entry : ∀ worker ∈ state.workers, worker.phase = .entry)\n" ++
  "    (observed : loadDWord (toMemory state.shared.shared.resources.space) config.dataAddress = .ok initial) :\n" ++
  "    observedBytes = bytes ∧ MutexWorkerCertificate.MachineSpecification state config initial :=\n" ++
  "  MutexWorkerCertificate.machine_sound observedBytes accepted state config initial valid ready closed entry observed\n\n" ++
  "theorem checkedSchedules (state : OS.MutexReplay.State) (config : OS.Mutex.Config) (initial : BitVec 32)\n" ++
  "    (valid : Invariant config state) (ready : LoanReady state) (closed : ClosedUnderTwo config)\n" ++
  "    (entry : ∀ worker ∈ state.workers, worker.phase = .entry)\n" ++
  "    (observed : loadDWord (toMemory state.shared.shared.resources.space) config.dataAddress = .ok initial) :\n" ++
  "    observedBytes = bytes ∧ MutexWorkerCertificate.CompletedSpecification state config initial :=\n" ++
  "  MutexWorkerCertificate.universal_sound observedBytes accepted state config initial valid ready closed entry observed\n\n" ++
  "theorem checkedReplay (state : OS.MutexReplay.State) (selections : List Nat)\n" ++
  "    (result : OS.MutexReplay.State × List (Nat × AtomicEvent))\n" ++
  "    (verified : verify state selections = .ok result) :\n" ++
  "    observedBytes = bytes ∧ ∃ record initial, state.shared.mutex = some record ∧\n" ++
  "      loadDWord (toMemory state.shared.shared.resources.space) record.config.dataAddress = .ok initial ∧\n" ++
  "      schedule state selections = .ok result ∧ Trace state selections result.2 result.1 ∧\n" ++
  "      Post state result.1 initial :=\n" ++
  "  MutexWorkerCertificate.sound observedBytes accepted state selections result verified\n\n"

private def source (bytes : List EDSL.X86.Byte) : String :=
  header ++ s!"def observedBytes : List Byte := [{byteLiterals bytes}]\n\n" ++
  "theorem accepted : MutexWorkerCertificate.accepts observedBytes = true := by decide\n\n" ++
  theoremSource ++ "end EDSL.GeneratedMutexWorker\n\n#audit_edsl\n"

private def elfSource (file : List EDSL.X86.Byte) (image : EDSL.ELF.Image) : String :=
  let segments := String.intercalate ", " (image.segments.map fun segment =>
    s!"⟨{segment.offset}, {segment.virtualAddress}, {segment.fileSize}, {segment.memorySize}, {segment.flags}, {segment.alignment}⟩")
  header ++ s!"def observedELF : List Byte := [{byteLiterals file}]\n" ++
  s!"def observedImage : ELF.Image := ⟨{image.entry}, [{segments}]⟩\n" ++
  s!"def observedBytes : List Byte := [{byteLiterals EDSL.OS.MutexReplay.bytes}]\n\n" ++
  "theorem accepted : MutexWorkerCertificate.accepts observedBytes = true := by decide\n\n" ++
  "theorem parsedImage : ELF.parse observedELF = .ok observedImage :=\n" ++
  "  ELF.checkParsed_sound observedELF observedImage (by decide)\n\n" ++
  "theorem checkedEntry : ELF.checkEntry observedELF observedImage observedBytes = true := by decide\n\n" ++
  "def loadedSpace (prior : Space) : Space := ELF.install observedELF observedImage prior\n\n" ++
  "theorem loadedCode (prior : Space) : CodeAt (toMemory (loadedSpace prior))\n" ++
  "    (ELF.codeAddress observedImage) observedBytes :=\n" ++
  "  ELF.checked_entry_code observedELF observedImage observedBytes prior checkedEntry\n\n" ++
  "theorem loaded (prior : Space) (free : ELF.fresh observedImage prior = true) :\n" ++
  "    ELF.load observedELF prior = .ok ⟨observedImage, loadedSpace prior⟩ :=\n" ++
  "  ELF.load_success observedELF prior observedImage parsedImage free\n\n" ++
  theoremSource ++ "end EDSL.GeneratedMutexWorker\n\n#audit_edsl\n"

def main (arguments : List String) : IO UInt32 := do
  let stderr ← IO.getStderr
  let request := match arguments with
    | [input, output] => some (input, output, false)
    | ["--elf", input, output] => some (input, output, true)
    | _ => none
  let some (input, output, elf) := request | do
    stderr.putStrLn "usage: edsl-certify-mutex-worker [--elf] INPUT CERTIFICATE.lean"
    return 2
  let raw ← IO.FS.readBinFile input
  let bytes := raw.data.toList.map (fun byte => BitVec.ofNat 8 byte.toNat)
  let candidate ← if elf then
      match EDSL.ELF.parse bytes with
      | .error error =>
        stderr.putStrLn s!"UNVERIFIED: unsupported mutex-worker ELF ({reprStr error}); no defect conclusion"
        pure none
      | .ok image =>
        if EDSL.ELF.checkEntry bytes image EDSL.OS.MutexReplay.bytes then pure (some (elfSource bytes image))
        else
          stderr.putStrLn "UNVERIFIED: mutex-worker ELF entry does not match supported bytes; no defect conclusion"
          pure none
    else if EDSL.MutexWorkerCertificate.accepts bytes then pure (some (source bytes))
    else
      stderr.putStrLn "UNVERIFIED: unsupported mutex-worker bytes; no defect conclusion"
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
    stderr.putStrLn "UNVERIFIED: mutex-worker certificate checking failed"
    return 1
  let stdout ← IO.getStdout
  stdout.putStr checked.stdout
  stdout.putStrLn s!"CERTIFIED {raw.size} exact mutex-worker artifact bytes: every admitted instruction-only prefix retains OS invariants and enables live selections; completed calls satisfy payload/return/cost/resource contracts; a completing schedule exists; {absolute}"
  return 0
