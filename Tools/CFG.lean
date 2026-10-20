/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.CFGArtifact
import EDSL.ELF.FunctionCandidateSource
import Lean

open EDSL X86 Sequential

private structure Failure where
  status : UInt32
  message : String

private def unsupported (message : String) : Failure :=
  ⟨3, "UNSUPPORTED: " ++ message ++ "; no defect conclusion"⟩

private def malformed (message : String) : Failure :=
  ⟨4, "MALFORMED: " ++ message ++ "; no defect conclusion"⟩

private def decodeFailure (offset : Nat) (error : X86.Error) : Failure :=
  match error with
  | .inaccessibleInstruction _ => malformed s!"incomplete instruction at offset {offset}"
  | _ => unsupported s!"sequential decoder at offset {offset}: {reprStr error}"

private def discoveryFailure (profile : CFG.Profile) : CFG.DiscoveryError → Failure
  | .empty => malformed "empty raw function window"
  | .byteLimit => unsupported s!"function span exceeds {profile.maxBytes} bytes"
  | .instructionLimit => unsupported s!"function span exceeds {profile.maxNodes} static instructions"
  | .decode offset error => decodeFailure offset error
  | .truncated offset => malformed s!"incomplete instruction at offset {offset}"
  | .unsupportedInstruction offset => unsupported s!"operation at offset {offset} is outside the read-only CFG profile"
  | .invalidGraph => unsupported "instruction boundaries, branch closure or cutpoint depths failed"

private def containerFailure : ELF.Error → Failure
  | .truncated => malformed "truncated ELF header or file-backed segment"
  | .badMagic => malformed "ELF magic is absent"
  | .invalidImage => malformed "ELF segment/entry constraints failed"
  | error => unsupported s!"ELF container: {reprStr error}"

private structure Candidate where
  source : String
  codeBytes : Nat
  nodes : Nat
  cutpoints : Nat

private def analyze (file : List Byte) (span : Option Nat) : Except Failure Candidate := do
  let (bytes, image) ← match span with
    | none => pure (file, none)
    | some length => do
      let image ← (ELF.parse file).mapError containerFailure
      let bytes ← (CFG.Artifact.entryWindow file image length).mapError fun failure =>
        match failure with
        | .unsupportedSpan => unsupported "explicit ELF span must be 1..64 bytes"
        | .fetch offset error => unsupported s!"selected entry byte {offset}: {reprStr error}"
      if !ELF.checkEntry file image bytes then
        throw (unsupported "entry span is not a complete executable file-backed interval")
      pure (bytes, some image)
  let graph ← (CFG.analyze bytes).mapError (discoveryFailure CFG.defaultProfile)
  let source := match image with
    | none => CFG.Artifact.rawSource bytes graph
    | some image => CFG.Artifact.elfSource file bytes image graph
  return ⟨source, bytes.length, graph.nodes.length, (graph.nodes.filter (·.cutpoint)).length⟩

private def symbolFailure : ELF.FunctionCandidate.Error → Failure
  | .fileSize => unsupported "named ELF must be 64..65536 bytes"
  | .truncated => malformed "truncated named ELF field or table payload"
  | .invalidName => malformed "selected symbol name must be nonempty and contain no NUL"
  | .invalidTable => unsupported "named ELF table layout is outside the complete metadata profile"
  | .missingName => unsupported "selected symbol is absent from complete symbol tables"
  | .duplicateName => unsupported "selected symbol has multiple static or dynamic occurrences"
  | .rejected => unsupported "named complete function or ELF metadata failed production admission"

private def analyzeNamed (profile : CFG.Profile) (data : ByteArray)
    (name namespaceSuffix : String) : Except Failure Candidate := do
  let requested := ELF.FunctionCandidate.fileBytes name.toUTF8
  let input ← (ELF.FunctionCandidate.extractWith profile.maxBytes data requested).mapError symbolFailure
  let graph ← (CFG.analyzeWith profile input.bytes).mapError (discoveryFailure profile)
  let source ← (ELF.FunctionCandidate.sourceWithProfile profile namespaceSuffix
    (ELF.FunctionCandidate.fileBytes data) requested input graph).mapError malformed
  return ⟨source, input.bytes.length,
    graph.nodes.length, (graph.nodes.filter (·.cutpoint)).length⟩

private def inferredNamespace (output : String) : Except Failure String := do
  let path : System.FilePath := output
  let some stem := path.fileStem | throw (malformed "named output requires a filename or --namespace NAME")
  let parts := if path.isAbsolute then [stem]
    else (path.components.dropLast.filter (· != ".")) ++ [stem]
  return String.intercalate "." parts

private inductive Selection where
  | raw
  | entry (span : Nat)
  | symbol (name : String) (namespaceSuffix : Option String) (profile : CFG.Profile)

private structure NamedOptions where
  name : Option String := none
  namespaceSuffix : Option String := none
  maxBytes : Option Nat := none
  maxNodes : Option Nat := none

private def positiveOption (flag value : String) : Except String Nat := do
  let some number := value.toNat? | throw s!"{flag} requires a positive decimal integer"
  if number = 0 then throw s!"{flag} requires a positive decimal integer"
  return number

/-- Options precede the two paths and may occur in any order. Every selected
cap is explicit caller configuration; neither the file nor discovery chooses it. -/
private def namedArguments (options : NamedOptions) : List String →
    Except String (String × String × Selection)
  | flag :: value :: rest => do
    if flag == "--elf-symbol" then
      if options.name.isSome then throw "duplicate --elf-symbol"
      if value.startsWith "--" then throw "--elf-symbol requires a name"
      namedArguments { options with name := some value } rest
    else if flag == "--namespace" then
      if options.namespaceSuffix.isSome then throw "duplicate --namespace"
      if value.startsWith "--" then throw "--namespace requires a suffix"
      namedArguments { options with namespaceSuffix := some value } rest
    else if flag == "--max-bytes" then
      if options.maxBytes.isSome then throw "duplicate --max-bytes"
      let number ← positiveOption flag value
      namedArguments { options with maxBytes := some number } rest
    else if flag == "--max-nodes" then
      if options.maxNodes.isSome then throw "duplicate --max-nodes"
      let number ← positiveOption flag value
      namedArguments { options with maxNodes := some number } rest
    else
      if flag.startsWith "--" then throw s!"unsupported named-import option: {flag}"
      if !rest.isEmpty || value.startsWith "--" then
        throw "named import requires exactly INPUT OUTPUT after its options"
      let some name := options.name | throw "profile and namespace options require --elf-symbol NAME"
      let byteCap := options.maxBytes.getD CFG.defaultProfile.maxBytes
      let nodeCap := options.maxNodes.getD CFG.defaultProfile.maxNodes
      if bounded : byteCap + 15 ≤ 2^64 then
        return (flag, value, .symbol name options.namespaceSuffix ⟨byteCap, nodeCap, bounded⟩)
      else throw "--max-bytes exceeds the supported nonwrapping profile bound"
  | _ => .error "named import requires option values and INPUT OUTPUT"

private def selection (arguments : List String) : Except String (String × String × Selection) :=
  match arguments with
  | ["--elf", length, input, output] =>
    match length.toNat? with
    | some length => .ok (input, output, .entry length)
    | none => .error "--elf requires a decimal span"
  | flag :: _ =>
    if flag ∈ ["--elf-symbol", "--namespace", "--max-bytes", "--max-nodes"] then
      namedArguments {} arguments
    else match arguments with
      | [input, output] => .ok (input, output, .raw)
      | _ => .error "unrecognized arguments"
  | _ => .error "INPUT OUTPUT are required"

def main (arguments : List String) : IO UInt32 := do
  let stderr ← IO.getStderr
  let selected := selection arguments
  if let .error message := selected then
    stderr.putStrLn message
    stderr.putStrLn "usage: edsl-cfg-import [--elf SPAN_BYTES | --elf-symbol NAME [--namespace NAME] [--max-bytes N] [--max-nodes N]] INPUT OBLIGATIONS.lean"
    return 2
  let .ok (input, output, selection) := selected | return 2
  try
    let raw ← IO.FS.readBinFile input
    let analyzed := match selection with
      | .raw => analyze (ELF.FunctionCandidate.fileBytes raw) none
      | .entry span => analyze (ELF.FunctionCandidate.fileBytes raw) (some span)
      | .symbol name suffix profile => do
        let selectedNamespace ← match suffix with
          | some selected => pure selected
          | none => inferredNamespace output
        analyzeNamed profile raw name selectedNamespace
    if let .error failure := analyzed then
      stderr.putStrLn failure.message
      return failure.status
    let .ok candidate := analyzed | return 1
    let path : System.FilePath := output
    if let some parent := path.parent then IO.FS.createDirAll parent
    IO.FS.writeFile path candidate.source
    let absolute ← IO.FS.realPath path
    -- The kernel child owns this lock; do not wrap the CLI in an outer lock.
    let checked ← IO.Process.output { cmd := "flock", args := #[
      "/tmp/edsl-lean-build.lock", "lean", "-j1", "-DwarningAsError=true", absolute.toString] }
    if checked.exitCode != 0 then
      stderr.putStr checked.stdout
      stderr.putStr checked.stderr
      stderr.putStrLn "IMPORT-FAILURE: kernel checking failed; no verified import or defect conclusion"
      return 1
    let stdout ← IO.getStdout
    stdout.putStr checked.stdout
    stdout.putStrLn s!"IMPORTED: {raw.size} literal artifact bytes, {candidate.codeBytes} function bytes, {candidate.nodes} instructions, {candidate.cutpoints} cutpoints; finite code checked; local functional and read-permission proofs remain required; {absolute}"
    return 0
  catch error =>
    stderr.putStrLn s!"IO-FAILURE: {error}; no verified import or defect conclusion"
    return 5
