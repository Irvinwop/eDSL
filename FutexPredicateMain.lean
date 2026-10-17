/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.FutexPredicateCertificate
import Lean

set_option warningAsError true

private def profileName : String := "wait-recheck"

private def literals (bytes : List EDSL.X86.Byte) : String :=
  String.intercalate ", " (bytes.map fun byte => toString byte.toNat)

/-- Separate literal declarations keep elaboration bounded for each chunk;
balanced references retain their original order without raising proof budgets.
Kernel reduction still checks every full-file parsing and entry claim. -/
private def literalSource (name : String) (bytes : List EDSL.X86.Byte) : String := Id.run do
  let mut remaining := bytes
  let mut terms : Array String := #[]
  let mut definitions := ""
  while !remaining.isEmpty do
    let chunk := s!"{name}Chunk{terms.size}"
    definitions := definitions ++ s!"private def {chunk} : List Byte := [{literals (remaining.take 64)}]\n"
    terms := terms.push chunk
    remaining := remaining.drop 64
  if terms.isEmpty then return s!"def {name} : List Byte := []\n"
  while terms.size > 1 do
    let mut paired : Array String := #[]
    let mut index := 0
    while index < terms.size do
      let left := terms[index]!
      if index + 1 < terms.size then
        paired := paired.push s!"({left} ++ {terms[index + 1]!})"
      else paired := paired.push left
      index := index + 2
    terms := paired
  return definitions ++ s!"def {name} : List Byte := {terms[0]!}\n"

private def header : String :=
  "import EDSL.FutexPredicateCertificate\n\n" ++
  "namespace EDSL.GeneratedFutexPredicate\n" ++
  "open X86 OS OS.Futex OS.Futex.Predicate OS.AddressSpace\n\n"

private def bindingSource : String :=
  "theorem certified (cohort : Predicate.Cohort) (state : Futex.State)\n" ++
  "    (worker : Nat) (client : Predicate.Client)\n" ++
  "    (admitted : Predicate.Admitted cohort state)\n" ++
  "    (member : cohort.clients[worker]? = some (.waitLoop client))\n" ++
  "    (code : CodeAt state.suspended.machine.memory client.entry.rip observedBytes) :\n" ++
  "    FutexPredicateCertificate.Specification observedBytes cohort state worker client :=\n" ++
  "  FutexPredicateCertificate.sound observedBytes accepted admitted member code\n\n" ++
  "theorem completion (cohort : Predicate.Cohort) (state : Futex.State)\n" ++
  "    (worker : Nat) (client : Predicate.Client)\n" ++
  "    (certificate : FutexPredicateCertificate.Specification observedBytes cohort state worker client)\n" ++
  "    (published : loadDWord state.suspended.machine.memory cohort.registration.address = .ok 1)\n" ++
  "    (clear : Futex.Notification.NoQueuedWait state worker) (flags rcx r11 : Word) :\n" ++
  "    ∃ after, Predicate.CompletesWithin 14 cohort worker client state after ∧\n" ++
  "      FutexPredicateCertificate.Specification observedBytes cohort after worker client :=\n" ++
  "  certificate.complete published clear flags rcx r11\n\n"

private def rawSource (bytes : List EDSL.X86.Byte) : String :=
  header ++ literalSource "observedBytes" bytes ++ "\n" ++
  "theorem accepted : FutexPredicateCertificate.accepts observedBytes = true := by decide +kernel\n\n" ++
  bindingSource ++ "end EDSL.GeneratedFutexPredicate\n\n#audit_edsl\n"

private def elfSource (file bytes : List EDSL.X86.Byte) (image : EDSL.ELF.Image) : String :=
  let segments := String.intercalate ", " (image.segments.map fun segment =>
    s!"⟨{segment.offset}, {segment.virtualAddress}, {segment.fileSize}, {segment.memorySize}, {segment.flags}, {segment.alignment}⟩")
  header ++ literalSource "observedELF" file ++
  s!"def observedImage : ELF.Image := ⟨{image.entry}, [{segments}]⟩\n" ++
  literalSource "observedBytes" bytes ++ "\n" ++
  "theorem accepted : FutexPredicateCertificate.accepts observedBytes = true := by decide +kernel\n\n" ++
  "theorem parsedImage : ELF.parse observedELF = .ok observedImage :=\n" ++
  "  ELF.checkParsed_sound observedELF observedImage (by decide +kernel)\n\n" ++
  "theorem checkedEntry : ELF.checkEntry observedELF observedImage observedBytes = true := by decide +kernel\n\n" ++
  "def loadedSpace (prior : Space) : Space := ELF.install observedELF observedImage prior\n\n" ++
  "theorem loadedCode (prior : Space) : CodeAt (toMemory (loadedSpace prior))\n" ++
  "    (ELF.codeAddress observedImage) observedBytes :=\n" ++
  "  ELF.checked_entry_code observedELF observedImage observedBytes prior checkedEntry\n\n" ++
  "theorem loaded (prior : Space) (free : ELF.fresh observedImage prior = true) :\n" ++
  "    ELF.load observedELF prior = .ok ⟨observedImage, loadedSpace prior⟩ :=\n" ++
  "  ELF.load_success observedELF prior observedImage parsedImage free\n\n" ++
  bindingSource ++
  "theorem loadedCertified (prior : Space) (free : ELF.fresh observedImage prior = true)\n" ++
  "    (cohort : Predicate.Cohort) (state : Futex.State) (worker : Nat) (client : Predicate.Client)\n" ++
  "    (admitted : Predicate.Admitted cohort state)\n" ++
  "    (member : cohort.clients[worker]? = some (.waitLoop client))\n" ++
  "    (memory : state.suspended.machine.memory = toMemory (loadedSpace prior))\n" ++
  "    (entry : client.entry.rip = ELF.codeAddress observedImage) :\n" ++
  "    ELF.load observedELF prior = .ok ⟨observedImage, loadedSpace prior⟩ ∧\n" ++
  "      FutexPredicateCertificate.Specification observedBytes cohort state worker client :=\n" ++
  "  FutexPredicateCertificate.loaded_sound observedELF observedBytes observedImage parsedImage\n" ++
  "    checkedEntry accepted prior free admitted member memory entry\n\n" ++
  "end EDSL.GeneratedFutexPredicate\n\n#audit_edsl\n"

private def entryBytes (file : List EDSL.X86.Byte) (image : EDSL.ELF.Image) :
    Except EDSL.X86.Error (List EDSL.X86.Byte) :=
  (List.range 30).mapM fun offset =>
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
    stderr.putStrLn "usage: edsl-certify-futex-predicate [--elf] wait-recheck FUNCTION CERTIFICATE.lean"
    return 2
  let raw ← IO.FS.readBinFile input
  let bytes := raw.data.toList.map fun byte => BitVec.ofNat 8 byte.toNat
  let candidate ← if elf then
      match EDSL.ELF.parse bytes with
      | .error error =>
        stderr.putStrLn s!"UNVERIFIED: unsupported predicate-loop ELF ({reprStr error}); no defect conclusion"
        pure none
      | .ok image =>
        match entryBytes bytes image with
        | .error _ =>
          stderr.putStrLn "UNVERIFIED: predicate-loop entry is not executable; no defect conclusion"
          pure none
        | .ok observed =>
          if EDSL.FutexPredicateCertificate.accepts observed && EDSL.ELF.checkEntry bytes image observed then
            pure (some (elfSource bytes observed image))
          else
            stderr.putStrLn "UNVERIFIED: ELF entry does not match the complete file-backed 30-byte predicate loop; no defect conclusion"
            pure none
    else if EDSL.FutexPredicateCertificate.accepts bytes then pure (some (rawSource bytes))
    else
      stderr.putStrLn "UNVERIFIED: unsupported predicate-loop bytes; no defect conclusion"
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
    stderr.putStrLn "UNVERIFIED: predicate-loop certificate checking failed"
    return 1
  let stdout ← IO.getStdout
  stdout.putStr checked.stdout
  stdout.putStrLn s!"CERTIFIED {raw.size} literal artifact bytes: exact 30-byte {profileName} code; signal 0/1 and WAIT0 model conditional on current admission, actual loop member, ABI, code and protected resources; universal mixed-trace safety and an enabled postnotification suffix of at most 14 Runtime actions; conditional current-LOAD/W1 fastpath minimum of four user instructions; no fairness, timing, ISA-wide optimality or kernel-refinement claim; {absolute}"
  return 0
