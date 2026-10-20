/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.ELF.FunctionCandidate
import EDSL.Audit
import EDSL.X86.Sequential.CFGArtifact

namespace EDSL.ELF.FunctionCandidate
open X86 FunctionWindow FunctionSymbol X86.Sequential

private def listLiteral {α : Type} (values : List α) (emit : α → String) : String :=
  "[" ++ String.intercalate ", " (values.map emit) ++ "]"

private def sectionLiteral (sh : Section) : String :=
  s!"⟨{sh.name}, {sh.kind}, {sh.flags}, {sh.address}, {sh.offset}, {sh.size}, " ++
    s!"{sh.link}, {sh.info}, {sh.alignment}, {sh.entrySize}⟩"

private def symbolLiteral (symbol : Symbol) : String :=
  s!"⟨{symbol.nameOffset}, {symbol.info}, {symbol.other}, {symbol.sh}, " ++
    s!"{symbol.value}, {symbol.size}⟩"

private def programLiteral (row : ProgramHeader) : String :=
  let segment := row.segment
  s!"⟨{row.kind}, {row.physicalAddress}, ⟨{segment.offset}, {segment.virtualAddress}, " ++
    s!"{segment.fileSize}, {segment.memorySize}, {segment.flags}, {segment.alignment}⟩⟩"

/-- Small literal definitions keep source parsing independent of file length.
All bytes still occur literally and the complete file is the checked parameter. -/
private def bytesSource (name : String) (bytes : List Byte) : String := Id.run do
  let chunks := (List.range ((bytes.length + 127) / 128)).map fun index =>
    (bytes.drop (index * 128)).take 128
  let mut text := ""
  let mut references := []
  for (chunk, index) in chunks.zipIdx do
    let reference := name ++ "Chunk" ++ toString index
    references := references ++ [reference]
    text := text ++ "def " ++ reference ++ " : List Byte := [" ++
      X86.Sequential.Literals.bytes chunk ++ "]\n"
  return text ++ "def " ++ name ++ " : List Byte := " ++
    listLiteral references id ++ ".flatten\n\n"

private def stringsLiteral (strings : Strings) (bytesName : String) : String :=
  s!"⟨{strings.sectionIndex}, {sectionLiteral strings.sh}, {bytesName}⟩"

private def namespaceLetter (character : Char) : Bool :=
  ('a' ≤ character && character ≤ 'z') ||
  ('A' ≤ character && character ≤ 'Z') || character == '_'

private def namespacePart (part : String) : Bool :=
  match part.toList with
  | [] => false
  | first :: rest => part != "_" && namespaceLetter first &&
      rest.all (fun character => namespaceLetter character ||
        ('0' ≤ character && character ≤ '9'))

/-- Validate ASCII namespace suffixes and quote every component. Raw paths,
external symbol bytes and user text can never become arbitrary Lean commands. -/
def namespaceText (suffix : String) : Except String String :=
  let parts := suffix.splitOn "."
  if !parts.isEmpty && parts.all namespacePart then
    .ok ("EDSL.GeneratedCFG." ++ String.intercalate "."
      (parts.map fun part => "«" ++ part ++ "»"))
  else .error "namespace suffix requires nonempty ASCII identifier components; use --namespace NAME"

/-- Emit data, exact named artifact/CFG checks and an independent local proof
interface. Only validated namespace components enter declaration names; raw symbol
names and metadata remain typed data.
No source/compiler, native OS, functional or resource premise is invented. -/
private def render (profile : CFG.Profile) (scope : String) (file name : List Byte)
    (input : FunctionInput) (graph : CFG.Graph) : String := Id.run do
  let mut text := "import EDSL.ELF.FunctionCandidateFacts\n" ++
    "import EDSL.X86.Sequential.CFGVerification\nimport EDSL.Audit\n\n" ++
    s!"namespace {scope}\nopen X86 X86.Sequential OS.AddressSpace\n" ++
    "set_option autoImplicit false\nset_option warningAsError true\n\n" ++
    "/- Exact static named-function import. Supply an independent specification,\n" ++
    "local invariants/ranks/access obligations and present caller resources.\n" ++
    "Loading/relocations, stable text, native CPU correspondence, CET-disabled\n" ++
    "sequential execution and OS behavior remain explicit model assumptions. -/\n\n"
  text := text ++ s!"def observedProfile : CFG.Profile := ⟨{profile.maxBytes}, {profile.maxNodes}, by decide⟩\n\n"
  text := text ++ bytesSource "observedELF" file ++ bytesSource "observedName" name ++
    bytesSource "observedBytes" input.bytes ++ bytesSource "sectionNameBytes" input.metadata.names.bytes
  for (table, index) in input.metadata.tables.zipIdx do
    text := text ++ bytesSource ("symbolNameBytes" ++ toString index) table.strings.bytes
  let header := input.table.header
  text := text ++ "def observedTable : ELF.FunctionWindow.Table :=\n" ++
    s!"  ⟨⟨{header.osAbi}, {header.entry}, {header.programOffset}, {header.sectionOffset}, " ++
    s!"{header.sectionCount}, {header.sectionNames}⟩, " ++ listLiteral input.table.programs programLiteral ++ "⟩\n\n"
  let tables := input.metadata.tables.zipIdx.map fun (table, index) =>
    s!"⟨{table.sectionIndex}, {sectionLiteral table.sh}, " ++
      listLiteral table.rows symbolLiteral ++ ", " ++
      stringsLiteral table.strings ("symbolNameBytes" ++ toString index) ++ "⟩"
  text := text ++ "def observedMetadata : ELF.FunctionSymbol.Metadata :=\n  ⟨" ++
    listLiteral input.metadata.sections sectionLiteral ++ ", " ++
    stringsLiteral input.metadata.names "sectionNameBytes" ++ ", " ++ listLiteral tables id ++ "⟩\n\n"
  let occurrence := input.function.occurrence
  let window := input.function.window
  text := text ++ "def observedFunction : ELF.FunctionSymbol.Function :=\n" ++
    s!"  ⟨⟨{occurrence.table}, {occurrence.index}, {symbolLiteral occurrence.symbol}⟩, " ++
    s!"{sectionLiteral input.function.sh}, ⟨{window.address}, {window.offset}⟩⟩\n\n" ++
    "def observedInput : ELF.FunctionInput :=\n" ++
    "  ⟨observedTable, observedMetadata, observedFunction, observedBytes⟩\n\n" ++
    "theorem inputChecked : observedInput.checkWith observedProfile.maxBytes observedELF observedName = true := by decide +kernel\n\n" ++
    "theorem binding : ELF.FunctionCandidate.Binding observedInput observedELF observedName observedProfile.maxBytes :=\n" ++
    "  ELF.FunctionCandidate.checked_bindingWith observedProfile.maxBytes observedInput observedELF observedName inputChecked\n\n" ++
    "theorem loadedCode (prior : Space) :\n" ++
    "    CodeAt (toMemory (ELF.install observedELF observedInput.table.image prior))\n" ++
    "      observedInput.function.window.base observedInput.bytes :=\n" ++
    "  ELF.FunctionCandidate.checked_codeWith observedProfile.maxBytes observedInput observedELF observedName inputChecked prior\n\n"
  text := text ++ "def observedGraph : CFG.Graph := " ++ CFG.Artifact.graphLiteral graph ++ "\n\n" ++
    "theorem checked : CFG.checkWith observedProfile observedBytes observedGraph = true := by decide +kernel\n" ++
    "theorem valid : CFG.Valid observedBytes observedGraph observedProfile := CFG.checkWith_sound checked\n\n" ++
    "def LocalObligations (Post : State → Prop) (AllowedRead : State → Read → Prop) :=\n" ++
    "  CFG.Annotations observedBytes observedGraph observedFunction.window.base Post AllowedRead\n\n" ++
    "theorem conditionalExecution (Post : State → Prop)\n" ++
    "    (AllowedRead : State → Read → Prop)\n" ++
    "    (proofs : LocalObligations Post AllowedRead) (initial : State)\n" ++
    "    (admitted : proofs.Inv valid.entry initial) (choices : Choices) :\n" ++
    "    ∃ result, run choices ((observedGraph.maxDepth + 1) *\n" ++
    "        (proofs.rank valid.entry initial + 1)) initial = .ok result ∧\n" ++
    "      Post result.state ∧ result.instructions ≤ (observedGraph.maxDepth + 1) *\n" ++
    "        (proofs.rank valid.entry initial + 1) :=\n" ++
    "  proofs.sound valid admitted choices\n\n" ++
    s!"end {scope}\n\n#audit_edsl\n"
  return text

/-- Namespace validation precedes rendering; every emitted declaration remains
under EDSL so the transitive project audit includes both generated clients. -/
def sourceWithProfile (profile : CFG.Profile) (namespaceSuffix : String) (file name : List Byte)
    (input : FunctionInput) (graph : CFG.Graph) : Except String String := do
  let scope ← namespaceText namespaceSuffix
  return render profile scope file name input graph

/-- Existing callers always emit the original 64-byte/32-node profile. -/
def source (namespaceSuffix : String) (file name : List Byte)
    (input : FunctionInput) (graph : CFG.Graph) : Except String String :=
  sourceWithProfile CFG.defaultProfile namespaceSuffix file name input graph

end EDSL.ELF.FunctionCandidate
