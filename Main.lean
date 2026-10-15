/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Certificate
import EDSL.ELF.Loader
import EDSL.Audit
import Lean

open EDSL.Certificate

private def parameters (profile : Profile) : String :=
  let code := "    (code : CodeAt initial.memory initial.rip observedBytes)\n"
  let stack := "    (stack : readWord initial.memory (initial.registers .rsp) = .ok returnAddress)\n" ++
    "    (returnValid : canonical returnAddress = true) :\n"
  match profile with
  | .increment | .incrementLoop => "(initial : State) (returnAddress : Word)\n" ++ code ++ stack
  | .load32 =>
    "(initial : State) (value : BitVec 32) (returnAddress : Word)\n" ++ code ++
    "    (data : loadDWord initial.memory (initial.registers .rdi) = .ok value)\n" ++ stack
  | .store32 =>
    "(initial : State) (returnAddress : Word)\n" ++ code ++
    "    (allowed : canStoreDWord initial.memory (initial.registers .rdi) = true)\n" ++
    "    (codeDisjoint : DWordDisjoint (initial.registers .rdi) initial.rip observedBytes.length)\n" ++
    "    (stackDisjoint : DWordDisjoint (initial.registers .rdi) (initial.registers .rsp) 8)\n" ++ stack

private def finalExpression (profile : Profile) (state : String := "initial") : String :=
  match profile with
  | .increment => s!"Examples.Compiler.Increment.finalState {state} returnAddress"
  | .incrementLoop => s!"Examples.Compiler.IncrementLoop.finalState {state} returnAddress"
  | .load32 => s!"Examples.Compiler.MemoryOps.loadFinal {state} value returnAddress"
  | .store32 => s!"Examples.Compiler.MemoryOps.storeFinal {state} returnAddress"

private def proofExpression (profile : Profile) (state : String := "initial")
    (code : String := "code") : String :=
  match profile with
  | .increment =>
    s!"Certificate.increment_sound observedBytes (by decide) {state} returnAddress {code} stack returnValid"
  | .incrementLoop =>
    s!"Certificate.incrementLoop_sound observedBytes (by decide) {state} returnAddress {code} stack returnValid"
  | .load32 =>
    s!"Certificate.load32_sound observedBytes (by decide) {state} value returnAddress {code} data stack returnValid"
  | .store32 =>
    s!"Certificate.store32_sound observedBytes (by decide) {state} returnAddress {code} allowed codeDisjoint stackDisjoint stack returnValid"

private def byteLiterals (bytes : List EDSL.X86.Byte) : String :=
  String.intercalate ", " (bytes.map (fun byte => toString byte.toNat))

private def instructionCount (profile : Profile) (state : String) : String :=
  if profile = .incrementLoop then s!"(Examples.Compiler.IncrementLoop.cost ({state}.registers .rcx).toNat)"
  else "2"

private def conclusion (profile : Profile) (state final : String) : String :=
  let count := instructionCount profile state
  s!"    Executes {state} ({final}) {count} ∧\n" ++
  s!"    ¬ Diverges {state} ∧\n" ++
  s!"    ∀ final count, Executes {state} final count →\n" ++
  s!"      final = {final} ∧ count = {count}"

private def certificateSource (profile : Profile) (bytes : List EDSL.X86.Byte) : String :=
  "import EDSL.Certificate\nimport EDSL.Audit\n\n" ++
  "namespace EDSL.Generated\nopen X86\n" ++
  s!"def observedBytes : List Byte := [{byteLiterals bytes}]\n\n" ++
  "theorem certified " ++ parameters profile ++
  conclusion profile "initial" (finalExpression profile) ++ " :=\n  " ++ proofExpression profile ++ "\n" ++
  "end EDSL.Generated\n\n#audit_edsl\n"

private def elfParameters (profile : Profile) : String :=
  let start := "(prior : Space) (initial : State) " ++
    (if profile = .load32 then "(value : BitVec 32) " else "") ++ "(returnAddress : Word)\n" ++
    "    (free : ELF.fresh observedImage prior = true)\n"
  let data := match profile with
    | .increment | .incrementLoop => ""
    | .load32 =>
      "    (data : loadDWord (toMemory (loadedSpace prior)) (initial.registers .rdi) = .ok value)\n"
    | .store32 =>
      "    (allowed : canStoreDWord (toMemory (loadedSpace prior)) (initial.registers .rdi) = true)\n" ++
      "    (codeDisjoint : DWordDisjoint (initial.registers .rdi) (ELF.codeAddress observedImage) observedBytes.length)\n" ++
      "    (stackDisjoint : DWordDisjoint (initial.registers .rdi) (initial.registers .rsp) 8)\n"
  start ++ data ++
    "    (stack : readWord (toMemory (loadedSpace prior)) (initial.registers .rsp) = .ok returnAddress)\n" ++
    "    (returnValid : canonical returnAddress = true) :\n"

private def elfCertificateSource (profile : Profile) (file : List EDSL.X86.Byte)
    (image : EDSL.ELF.Image) : String :=
  let segments := String.intercalate ", " (image.segments.map fun segment =>
    s!"⟨{segment.offset}, {segment.virtualAddress}, {segment.fileSize}, {segment.memorySize}, {segment.flags}, {segment.alignment}⟩")
  let state := "(loadedEntry prior initial)"
  "import EDSL.Certificate\nimport EDSL.ELF.Loader\nimport EDSL.Audit\n\n" ++
  "namespace EDSL.Generated\nopen X86 OS.AddressSpace\n" ++
  "set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n" ++
  s!"def observedELF : List Byte := [{byteLiterals file}]\n" ++
  s!"def observedImage : ELF.Image := ⟨{image.entry}, [{segments}]⟩\n" ++
  s!"def observedBytes : List Byte := [{byteLiterals profile.bytes}]\n\n" ++
  "theorem parsedImage : ELF.parse observedELF = .ok observedImage :=\n" ++
  "  ELF.checkParsed_sound observedELF observedImage (by decide)\n\n" ++
  "theorem checkedEntry : ELF.checkEntry observedELF observedImage observedBytes = true := by decide\n\n" ++
  "def loadedSpace (prior : Space) : Space := ELF.install observedELF observedImage prior\n" ++
  "def loadedEntry (prior : Space) (initial : State) : State :=\n" ++
  "  { initial with memory := toMemory (loadedSpace prior), rip := ELF.codeAddress observedImage }\n\n" ++
  "theorem loadedCode (prior : Space) : CodeAt (toMemory (loadedSpace prior))\n" ++
  "    (ELF.codeAddress observedImage) observedBytes :=\n" ++
  "  ELF.checked_entry_code observedELF observedImage observedBytes prior checkedEntry\n\n" ++
  "theorem certified " ++ elfParameters profile ++
  "    ELF.load observedELF prior = .ok ⟨observedImage, loadedSpace prior⟩ ∧\n" ++
  conclusion profile state (finalExpression profile state) ++ " := by\n" ++
  "  exact ⟨ELF.load_success observedELF prior observedImage parsedImage free,\n    " ++
  proofExpression profile state "(loadedCode prior)" ++ "⟩\n" ++
  "end EDSL.Generated\n\n#audit_edsl\n"

private structure Request where
  profile : Profile
  input : String
  output : String
  elf : Bool := false

private def parseArguments : List String → Option Request
  | ["--elf", name, input, output] => (Profile.parse name).map (fun profile => ⟨profile, input, output, true⟩)
  | ["--elf", input, output] => some ⟨.increment, input, output, true⟩
  | [input, output] => some ⟨.increment, input, output, false⟩
  | [name, input, output] => (Profile.parse name).map (fun profile => ⟨profile, input, output, false⟩)
  | _ => none

private def createSource (request : Request) (bytes : List EDSL.X86.Byte) : IO (Option String) := do
  let stderr ← IO.getStderr
  if request.elf then
    match EDSL.ELF.parse bytes with
    | .error error =>
      stderr.putStrLn s!"UNVERIFIED: unsupported ELF container ({reprStr error}); no defect conclusion"
      return none
    | .ok image =>
      if !EDSL.ELF.checkEntry bytes image request.profile.bytes then
        stderr.putStrLn s!"UNVERIFIED: ELF entry does not match the {request.profile.name} file-backed contract; no defect conclusion"
        return none
      return some (elfCertificateSource request.profile bytes image)
  else
    if !accepts request.profile bytes then
      stderr.putStrLn s!"UNVERIFIED: bytes are unsupported by the {request.profile.name} contract profile; no defect conclusion"
      return none
    return some (certificateSource request.profile bytes)

def main (arguments : List String) : IO UInt32 := do
  let stderr ← IO.getStderr
  let some request := parseArguments arguments | do
    stderr.putStrLn "usage: edsl-certify [--elf] [increment|increment-loop|load32|store32] FUNCTION CERTIFICATE.lean"
    return 2
  let raw ← IO.FS.readBinFile request.input
  let bytes := raw.data.toList.map (fun byte => BitVec.ofNat 8 byte.toNat)
  let source ← createSource request bytes
  let some source := source | return 3
  let outputPath : System.FilePath := request.output
  if let some parent := outputPath.parent then IO.FS.createDirAll parent
  IO.FS.writeFile outputPath source
  let absolute ← IO.FS.realPath outputPath
  let checked ← IO.Process.output { cmd := "lean", args := #["-DwarningAsError=true", absolute.toString] }
  if checked.exitCode != 0 then
    stderr.putStr checked.stdout
    stderr.putStr checked.stderr
    stderr.putStrLn "UNVERIFIED: Lean certificate checking failed"
    return 1
  let stdout ← IO.getStdout
  stdout.putStr checked.stdout
  let artifact := if request.elf then "ELF container" else "raw function"
  let cost := if request.profile = .incrementLoop then "2*initial_RCX+3 modeled instructions; proved termination for every 64-bit count"
    else "two modeled instructions"
  stdout.putStrLn s!"CERTIFIED {request.profile.name}: {raw.size} exact {artifact} bytes; all admitted entries; {cost}; certificate {absolute}"
  return 0
