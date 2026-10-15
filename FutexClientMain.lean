/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.FutexClientCertificate
import EDSL.Audit
import Lean

private def profileName : String := "publish-payload-wake"

private def literals (bytes : List EDSL.X86.Byte) : String :=
  String.intercalate ", " (bytes.map fun byte => toString byte.toNat)

private def header : String :=
  "import EDSL.FutexClientCertificate\nimport EDSL.Audit\n\n" ++
  "namespace EDSL.GeneratedFutexClient\nopen X86 OS OS.Futex OS.Futex.Clients OS.AddressSpace\n" ++
  "set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n"

private def bindingSource : String :=
  "theorem certified (cohort : Cohort) (state : Futex.State) (worker : Nat) (client : Client)\n" ++
  "    (admitted : Admitted cohort state)\n" ++
  "    (member : cohort.clients[worker]? = some client)\n" ++
  "    (publisher : client.role = .publishPayloadWake)\n" ++
  "    (code : CodeAt state.suspended.machine.memory client.entry.rip observedBytes) :\n" ++
  "    FutexClientCertificate.Specification observedBytes cohort state worker client :=\n" ++
  "  FutexClientCertificate.sound observedBytes accepted admitted member publisher code\n\n"

private def rawSource (bytes : List EDSL.X86.Byte) : String :=
  header ++ s!"def observedBytes : List Byte := [{literals bytes}]\n\n" ++
  "theorem accepted : FutexClientCertificate.accepts observedBytes = true := by decide\n\n" ++
  bindingSource ++ "end EDSL.GeneratedFutexClient\n\n#audit_edsl\n"

private def elfSource (file bytes : List EDSL.X86.Byte) (image : EDSL.ELF.Image) : String :=
  let segments := String.intercalate ", " (image.segments.map fun segment =>
    s!"⟨{segment.offset}, {segment.virtualAddress}, {segment.fileSize}, {segment.memorySize}, {segment.flags}, {segment.alignment}⟩")
  header ++ s!"def observedELF : List Byte := [{literals file}]\n" ++
  s!"def observedImage : ELF.Image := ⟨{image.entry}, [{segments}]⟩\n" ++
  s!"def observedBytes : List Byte := [{literals bytes}]\n\n" ++
  "theorem accepted : FutexClientCertificate.accepts observedBytes = true := by decide\n\n" ++
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
  bindingSource ++
  "theorem loadedCertified (prior : Space) (free : ELF.fresh observedImage prior = true)\n" ++
  "    (cohort : Cohort) (state : Futex.State) (worker : Nat) (client : Client)\n" ++
  "    (admitted : Admitted cohort state)\n" ++
  "    (member : cohort.clients[worker]? = some client)\n" ++
  "    (publisher : client.role = .publishPayloadWake)\n" ++
  "    (memory : state.suspended.machine.memory = toMemory (loadedSpace prior))\n" ++
  "    (entry : client.entry.rip = ELF.codeAddress observedImage) :\n" ++
  "    ELF.load observedELF prior = .ok ⟨observedImage, loadedSpace prior⟩ ∧\n" ++
  "      FutexClientCertificate.Specification observedBytes cohort state worker client :=\n" ++
  "  FutexClientCertificate.loaded_sound observedELF observedBytes observedImage parsedImage\n" ++
  "    checkedEntry accepted prior free admitted member publisher memory entry\n\n" ++
  "end EDSL.GeneratedFutexClient\n\n#audit_edsl\n"

/-- Read the candidate's own current executable entry bytes. The subsequent
checker also requires the complete 32-byte window to be file-backed. -/
private def entryBytes (file : List EDSL.X86.Byte) (image : EDSL.ELF.Image) :
    Except EDSL.X86.Error (List EDSL.X86.Byte) :=
  (List.range 32).mapM fun offset =>
    EDSL.X86.fetchByte (EDSL.OS.AddressSpace.toMemory
      (EDSL.ELF.install file image EDSL.OS.AddressSpace.empty))
      (EDSL.ELF.codeAddress image + BitVec.ofNat 64 offset)

def main (arguments : List String) : IO UInt32 := do
  let stderr ← IO.getStderr
  let selected := match arguments with
    | [name, input, output] => if name = profileName then some (input, output, false) else none
    | ["--elf", name, input, output] => if name = profileName then some (input, output, true) else none
    | _ => none
  let some (input, output, elf) := selected | do
    stderr.putStrLn "usage: edsl-certify-futex-client [--elf] publish-payload-wake FUNCTION CERTIFICATE.lean"
    return 2
  let raw ← IO.FS.readBinFile input
  let bytes := raw.data.toList.map fun byte => BitVec.ofNat 8 byte.toNat
  let candidate ← if elf then
      match EDSL.ELF.parse bytes with
      | .error error =>
        stderr.putStrLn s!"UNVERIFIED: unsupported publication client ELF ({reprStr error}); no defect conclusion"
        pure none
      | .ok image =>
        match entryBytes bytes image with
        | .error _ =>
          stderr.putStrLn "UNVERIFIED: publication client entry is not executable; no defect conclusion"
          pure none
        | .ok observed =>
          if EDSL.FutexClientCertificate.accepts observed && EDSL.ELF.checkEntry bytes image observed then
            pure (some (elfSource bytes observed image))
          else
            stderr.putStrLn "UNVERIFIED: ELF entry does not match the exact 32-byte publication client; no defect conclusion"
            pure none
    else if EDSL.FutexClientCertificate.accepts bytes then pure (some (rawSource bytes))
    else
      stderr.putStrLn "UNVERIFIED: unsupported publication client bytes; no defect conclusion"
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
    stderr.putStrLn "UNVERIFIED: publication client certificate checking failed"
    return 1
  let stdout ← IO.getStdout
  stdout.putStr checked.stdout
  stdout.putStrLn s!"CERTIFIED {raw.size} literal artifact bytes: exact 32-byte {profileName} code; contract conditional on current admission and publishing-member/code binding; positive actual demand/prefix lifts, same-member XCHG publication and typed protected RET; native/kernel conformance and scheduling progress remain external; {absolute}"
  return 0
