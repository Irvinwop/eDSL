/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.CFGDiscovery
import EDSL.X86.Sequential.CFGVerification
import EDSL.X86.Sequential.Literals
import EDSL.ELF.Loader

namespace EDSL.X86.Sequential.CFG.Artifact

inductive EntryError where
  | unsupportedSpan
  | fetch (offset : Nat) (error : X86.Error)
  deriving DecidableEq, Repr

/-- Select exactly the requested entry span, including any early-return suffix.
Finite CFG checking must close every possible successor within this span. -/
def entryWindow (file : List Byte) (image : ELF.Image) (span : Nat) :
    Except EntryError (List Byte) :=
  if span = 0 ∨ span > 64 then .error .unsupportedSpan
  else
    let memory := OS.AddressSpace.toMemory (ELF.install file image OS.AddressSpace.empty)
    (List.range span).mapM fun offset =>
      (fetchByte memory (ELF.codeAddress image + BitVec.ofNat 64 offset)).mapError (.fetch offset)

def nodeLiteral (node : Node) : String :=
  s!"⟨{node.offset}, {Literals.instruction node.instruction}, " ++
    (if node.cutpoint then "true" else "false") ++ s!", {node.depth}⟩"

def graphLiteral (graph : Graph) : String :=
  "{ nodes := [" ++ String.intercalate ", " (graph.nodes.map nodeLiteral) ++
    s!"], maxDepth := {graph.maxDepth}" ++ " }"

private def imageLiteral (image : ELF.Image) : String :=
  let segments := String.intercalate ", " (image.segments.map fun segment =>
    s!"⟨{segment.offset}, {segment.virtualAddress}, {segment.fileSize}, " ++
      s!"{segment.memorySize}, {segment.flags}, {segment.alignment}⟩")
  s!"⟨{image.entry}, [{segments}]⟩"

private def header : String :=
  "import EDSL.X86.Sequential.CFGArtifact\nimport EDSL.Audit\n\n" ++
  "namespace EDSL.GeneratedCFG\nopen X86 Sequential OS.AddressSpace\n" ++
  "set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n" ++
  "/- Static import: the finite graph is checked below. To establish a task's\n" ++
  "functional contract, supply LocalObligations for an independently fixed\n" ++
  "Post and access predicate, and prove its entry invariant from admitted input.\n" ++
  "Native CPU/kernel conformance and caller resources remain explicit. -/\n\n"

private def graphSource (bytes : List Byte) (graph : Graph) : String :=
  "def observedBytes : List Byte := [" ++ Literals.bytes bytes ++ "]\n\n" ++
  "def observedGraph : CFG.Graph := " ++ graphLiteral graph ++ "\n\n" ++
  "theorem checked : CFG.check observedBytes observedGraph = true := by decide\n" ++
  "theorem valid : CFG.Valid observedBytes observedGraph := CFG.check_sound checked\n\n" ++
  "def LocalObligations (base : Word) (Post : State → Prop)\n" ++
  "    (AllowedRead : State → Read → Prop) :=\n" ++
  "  CFG.Annotations observedBytes observedGraph base Post AllowedRead\n\n" ++
  "theorem conditionalExecution (base : Word) (Post : State → Prop)\n" ++
  "    (AllowedRead : State → Read → Prop)\n" ++
  "    (proofs : LocalObligations base Post AllowedRead) (initial : State)\n" ++
  "    (admitted : proofs.Inv valid.entry initial) (choices : Choices) :\n" ++
  "    ∃ result, run choices ((observedGraph.maxDepth + 1) *\n" ++
  "        (proofs.rank valid.entry initial + 1)) initial = .ok result ∧\n" ++
  "      Post result.state ∧ result.instructions ≤ (observedGraph.maxDepth + 1) *\n" ++
  "        (proofs.rank valid.entry initial + 1) :=\n" ++
  "  proofs.sound valid admitted choices\n\n"

private def containerSource (file bytes : List Byte) (image : ELF.Image) : String :=
  "def observedELF : List Byte := [" ++ Literals.bytes file ++ "]\n\n" ++
  "def observedImage : ELF.Image := " ++ imageLiteral image ++ "\n\n" ++
  "theorem parsedImage : ELF.parse observedELF = .ok observedImage := by rfl\n" ++
  "theorem checkedEntry : ELF.checkEntry observedELF observedImage observedBytes = true := by decide\n\n" ++
  s!"theorem selectedSpan : observedBytes.length = {bytes.length} := by decide\n\n" ++
  "def loadedSpace (prior : Space) := ELF.install observedELF observedImage prior\n\n" ++
  "theorem loaded (prior : Space) (free : ELF.fresh observedImage prior = true) :\n" ++
  "    ELF.load observedELF prior = .ok ⟨observedImage, loadedSpace prior⟩ :=\n" ++
  "  ELF.load_success _ _ _ parsedImage free\n\n" ++
  "theorem loadedCode (prior : Space) :\n" ++
  "    CodeAt (toMemory (loadedSpace prior)) (ELF.codeAddress observedImage) observedBytes :=\n" ++
  "  ELF.checked_entry_code _ _ _ prior checkedEntry\n\n" ++
  "/- The ELF entry denotes a callable function. Native loading, input/stack\n" ++
  "admission, and process startup are separate obligations. -/\n\n"

/-- A complete literal finite-code certificate and a typed local proof interface.
No proof hole or assumed semantic-correctness theorem is emitted. -/
def rawSource (bytes : List Byte) (graph : Graph) : String :=
  header ++ graphSource bytes graph ++ "end EDSL.GeneratedCFG\n\n#audit_edsl\n"

def elfSource (file bytes : List Byte) (image : ELF.Image) (graph : Graph) : String :=
  header ++ graphSource bytes graph ++ containerSource file bytes image ++
    "end EDSL.GeneratedCFG\n\n#audit_edsl\n"

end EDSL.X86.Sequential.CFG.Artifact
