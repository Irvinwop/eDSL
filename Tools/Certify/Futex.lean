/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.FutexCertificate
import EDSL.ELF.Loader
import EDSL.Audit
import Lean

open EDSL.Examples.FutexStubs

private def profileName : Profile → String
  | .wait => "wait"
  | .wakeOne => "wake-one"

private def profileTerm : Profile → String
  | .wait => ".wait"
  | .wakeOne => ".wakeOne"

private def parseProfile : String → Option Profile
  | "wait" => some .wait
  | "wake-one" => some .wakeOne
  | _ => none

private def literals (bytes : List EDSL.X86.Byte) : String :=
  String.intercalate ", " (bytes.map fun byte => toString byte.toNat)

private def header : String :=
  "import EDSL.FutexCertificate\nimport EDSL.ELF.Loader\nimport EDSL.Audit\n\n" ++
  "namespace EDSL.GeneratedFutex\nopen X86 OS.AddressSpace Examples.FutexStubs\n" ++
  "set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n"

private def theoremSource (profile : Profile) : String :=
  let term := profileTerm profile
  "theorem certified (initial : State) (word : Word) (expected : BitVec 32)\n" ++
  s!"    (arguments : CanonicalArguments {term} initial word expected)\n" ++
  "    (code : CodeAt initial.memory initial.rip observedBytes) :\n" ++
  s!"    observedBytes = Profile.bytes {term} ∧ FutexCertificate.Specification {term} initial word expected :=\n" ++
  s!"  FutexCertificate.sound {term} observedBytes accepted initial word expected arguments code\n\n"

private def rawSource (profile : Profile) (bytes : List EDSL.X86.Byte) : String :=
  header ++ s!"def observedBytes : List Byte := [{literals bytes}]\n\n" ++
  s!"theorem accepted : FutexCertificate.accepts {profileTerm profile} observedBytes = true := by decide\n\n" ++
  theoremSource profile ++ "end EDSL.GeneratedFutex\n\n#audit_edsl\n"

private def elfSource (profile : Profile) (file : List EDSL.X86.Byte) (image : EDSL.ELF.Image) : String :=
  let term := profileTerm profile
  let segments := String.intercalate ", " (image.segments.map fun segment =>
    s!"⟨{segment.offset}, {segment.virtualAddress}, {segment.fileSize}, {segment.memorySize}, {segment.flags}, {segment.alignment}⟩")
  header ++ s!"def observedELF : List Byte := [{literals file}]\n" ++
  s!"def observedImage : ELF.Image := ⟨{image.entry}, [{segments}]⟩\n" ++
  s!"def observedBytes : List Byte := [{literals profile.bytes}]\n\n" ++
  s!"theorem accepted : FutexCertificate.accepts {term} observedBytes = true := by decide\n\n" ++
  "theorem parsedImage : ELF.parse observedELF = .ok observedImage :=\n" ++
  "  ELF.checkParsed_sound observedELF observedImage (by decide)\n\n" ++
  "theorem checkedEntry : ELF.checkEntry observedELF observedImage observedBytes = true := by decide\n\n" ++
  "def loadedSpace (prior : Space) : Space := ELF.install observedELF observedImage prior\n" ++
  "def loadedEntry (prior : Space) (initial : State) : State :=\n" ++
  "  { initial with memory := toMemory (loadedSpace prior), rip := ELF.codeAddress observedImage }\n\n" ++
  "theorem loadedCode (prior : Space) : CodeAt (toMemory (loadedSpace prior))\n" ++
  "    (ELF.codeAddress observedImage) observedBytes :=\n" ++
  "  ELF.checked_entry_code observedELF observedImage observedBytes prior checkedEntry\n\n" ++
  "theorem loaded (prior : Space) (free : ELF.fresh observedImage prior = true) :\n" ++
  "    ELF.load observedELF prior = .ok ⟨observedImage, loadedSpace prior⟩ :=\n" ++
  "  ELF.load_success observedELF prior observedImage parsedImage free\n\n" ++
  theoremSource profile ++
  "theorem loadedCertified (prior : Space) (initial : State) (word : Word) (expected : BitVec 32)\n" ++
  "    (free : ELF.fresh observedImage prior = true)\n" ++
  s!"    (arguments : CanonicalArguments {term} (loadedEntry prior initial) word expected) :\n" ++
  "    ELF.load observedELF prior = .ok ⟨observedImage, loadedSpace prior⟩ ∧\n" ++
  s!"    FutexCertificate.Specification {term} (loadedEntry prior initial) word expected :=\n" ++
  "  ⟨loaded prior free, (certified (loadedEntry prior initial) word expected arguments (loadedCode prior)).2⟩\n\n" ++
  "end EDSL.GeneratedFutex\n\n#audit_edsl\n"

def main (arguments : List String) : IO UInt32 := do
  let stderr ← IO.getStderr
  let selected := match arguments with
    | [name, input, output] => (parseProfile name).map fun profile => (profile, input, output, false)
    | ["--elf", name, input, output] => (parseProfile name).map fun profile => (profile, input, output, true)
    | _ => none
  let some (profile, input, output, elf) := selected | do
    stderr.putStrLn "usage: edsl-certify-futex [--elf] [wait|wake-one] FUNCTION CERTIFICATE.lean"
    return 2
  let raw ← IO.FS.readBinFile input
  let bytes := raw.data.toList.map fun byte => BitVec.ofNat 8 byte.toNat
  let candidate ← if elf then
      match EDSL.ELF.parse bytes with
      | .error error =>
        stderr.putStrLn s!"UNVERIFIED: unsupported futex function ELF ({reprStr error}); no defect conclusion"
        pure none
      | .ok image =>
        if EDSL.ELF.checkEntry bytes image profile.bytes then pure (some (elfSource profile bytes image))
        else
          stderr.putStrLn "UNVERIFIED: ELF entry does not match selected futex function bytes; no defect conclusion"
          pure none
    else if EDSL.FutexCertificate.accepts profile bytes then pure (some (rawSource profile bytes))
    else
      stderr.putStrLn "UNVERIFIED: unsupported futex function bytes; no defect conclusion"
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
    stderr.putStrLn "UNVERIFIED: futex function certificate checking failed"
    return 1
  let stdout ← IO.getStdout
  stdout.putStr checked.stdout
  stdout.putStrLn s!"CERTIFIED {raw.size} exact {profileName profile} function artifact bytes: canonical ABI request in {profile.entryCost} instructions; conditional current-memory RET, {profile.completedCost} total user instructions; caller-supplied stack; kernel service and wait progress remain external; {absolute}"
  return 0
