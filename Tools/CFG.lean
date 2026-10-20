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

private def discoveryFailure : CFG.DiscoveryError → Failure
  | .empty => malformed "empty raw function window"
  | .byteLimit => unsupported "function span exceeds 64 bytes"
  | .instructionLimit => unsupported "function span exceeds 32 static instructions"
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
  let graph ← (CFG.analyze bytes).mapError discoveryFailure
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

private def analyzeNamed (data : ByteArray) (name namespaceSuffix : String) : Except Failure Candidate := do
  let requested := ELF.FunctionCandidate.fileBytes name.toUTF8
  let input ← (ELF.FunctionCandidate.extract data requested).mapError symbolFailure
  let graph ← (CFG.analyze input.bytes).mapError discoveryFailure
  let source ← (ELF.FunctionCandidate.source namespaceSuffix
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
  | symbol (name : String) (namespaceSuffix : Option String)

def main (arguments : List String) : IO UInt32 := do
  let stderr ← IO.getStderr
  let selected := match arguments with
    | [input, output] => some (input, output, Selection.raw)
    | ["--elf", length, input, output] => length.toNat?.map fun length => (input, output, Selection.entry length)
    | ["--elf-symbol", name, input, output] => some (input, output, Selection.symbol name none)
    | ["--elf-symbol", name, "--namespace", suffix, input, output] =>
      some (input, output, Selection.symbol name (some suffix))
    | _ => none
  let some (input, output, selection) := selected | do
    stderr.putStrLn "usage: edsl-cfg-import [--elf SPAN_BYTES | --elf-symbol NAME [--namespace NAME]] INPUT OBLIGATIONS.lean"
    return 2
  try
    let raw ← IO.FS.readBinFile input
    let analyzed := match selection with
      | .raw => analyze (ELF.FunctionCandidate.fileBytes raw) none
      | .entry span => analyze (ELF.FunctionCandidate.fileBytes raw) (some span)
      | .symbol name suffix => do
        let selectedNamespace ← match suffix with
          | some selected => pure selected
          | none => inferredNamespace output
        analyzeNamed raw name selectedNamespace
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
