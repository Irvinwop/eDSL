/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.ELF.FunctionCandidateSource
import EDSL.X86.VCGen.Core
import tests.ELFFunctionWindow
import tests.ELFFunctionSymbol
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.ELFFunctionBounds
open X86 X86.Sequential OS.AddressSpace ELF
open ELFFunctionSymbol (le sectionRow symbolRow overwrite putLE)

-- A real ELF64LE fixture, independently encoded using only ELF field offsets.
-- Text occupies [0x80,0xc4); strings [0xd0,0xdf); symbols [0xe0,0x128);
-- section names [0x130,0x159); section headers [0x180,0x2c0).
-- The named extent contains an early RET and complete short-NOP padding, then
-- a final RET. Authentication and CFG partitioning must include its suffix.
def bytes : List Byte :=
  [0xb8, 42, 0, 0, 0, 0xc3] ++ (List.replicate 30 [0x66, 0x90]).flatten ++ [0x90, 0xc3]
def name : List Byte := ELFFunctionSymbol.requested

def fileAt (address flags loadSize symbolSize : Nat) : List Byte :=
  [0x7f, 0x45, 0x4c, 0x46, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] ++
  le 2 2 ++ le 2 62 ++ le 4 1 ++ le 8 address ++ le 8 64 ++ le 8 0x180 ++
  le 4 0 ++ le 2 64 ++ le 2 56 ++ le 2 1 ++ le 2 64 ++ le 2 5 ++ le 2 4 ++
  le 4 1 ++ le 4 flags ++ le 8 0x80 ++ le 8 address ++ le 8 address ++
  le 8 loadSize ++ le 8 loadSize ++ le 8 4096 ++ List.replicate 8 0 ++
  bytes ++ List.replicate 12 0 ++ ELFFunctionSymbol.stringBytes ++ List.replicate 1 0 ++
  symbolRow 0 0 0 0 0 0 ++ symbolRow 1 0x12 0 1 address symbolSize ++
  symbolRow 8 0x12 0 1 (address + 5) 1 ++ List.replicate 8 0 ++
  ELFFunctionSymbol.sectionNames ++ List.replicate 39 0 ++
  sectionRow 0 0 0 0 0 0 0 0 0 0 ++
  sectionRow 1 1 6 address 0x80 68 0 0 16 0 ++
  sectionRow 7 2 0 0 0xe0 72 3 1 8 24 ++
  sectionRow 15 3 0 0 0xd0 15 0 0 1 0 ++
  sectionRow 23 3 0 0 0x130 41 0 0 1 0

-- Untrusted witnesses are written separately from the byte encoders.
def inputAt (address flags loadSize symbolSize : Nat) : FunctionInput :=
  let text : FunctionSymbol.Section := ⟨1, 1, 6, address, 0x80, 68, 0, 0, 16, 0⟩
  let symtab : FunctionSymbol.Section := ⟨7, 2, 0, 0, 0xe0, 72, 3, 1, 8, 24⟩
  let strtab : FunctionSymbol.Section := ⟨15, 3, 0, 0, 0xd0, 15, 0, 0, 1, 0⟩
  let shstrtab : FunctionSymbol.Section := ⟨23, 3, 0, 0, 0x130, 41, 0, 0, 1, 0⟩
  let target : FunctionSymbol.Symbol := ⟨1, 0x12, 0, 1, address, symbolSize⟩
  ⟨⟨⟨0, address, 64, 0x180, 5, 4⟩,
      [⟨1, address, ⟨0x80, address, loadSize, loadSize, flags, 4096⟩⟩]⟩,
    ⟨[default, text, symtab, strtab, shstrtab],
      ⟨4, shstrtab, ELFFunctionSymbol.sectionNames⟩,
      [⟨2, symtab, [default, target, ⟨8, 0x12, 0, 1, address + 5, 1⟩],
        ⟨3, strtab, ELFFunctionSymbol.stringBytes⟩⟩]⟩,
    ⟨⟨2, 1, target⟩, text, ⟨address, 0x80⟩⟩, bytes⟩

def file : List Byte := fileAt 0x400080 5 68 68
def input : FunctionInput := inputAt 0x400080 5 68 68
/-- Caller configuration, independent of extraction or selected input length. -/
def profile : CFG.Profile := ⟨68, 40, by decide⟩

theorem accepted : input.checkWith profile.maxBytes file name = true := by decide +kernel
example : input.check file name = false := by decide +kernel
example : input.checkWith 67 file name = false := by decide +kernel
example : input.checkWith 0 file name = false := by decide +kernel

theorem binding : FunctionCandidate.Binding input file name profile.maxBytes :=
  FunctionCandidate.checked_bindingWith profile.maxBytes input file name accepted

theorem loadedCode (prior : Space) :
    CodeAt (toMemory (ELF.install file input.table.image prior)) input.function.window.base bytes :=
  FunctionCandidate.checked_codeWith profile.maxBytes input file name accepted prior

-- A complete extent is compulsory even though its first RET is at byte five.
example : ({ input with bytes := bytes.take 6 } : FunctionInput).checkWith 68 file name = false :=
  by decide +kernel
-- Byte 66 lies beyond the old 64-byte boundary and after the early RET.
-- Neither named checking nor its executable-code premise can authenticate stale
-- literal bytes there, despite unchanged metadata and an unchanged prefix.
example : input.checkWith 68 (file.set (0x80 + 66) 0xc3) name = false := by decide +kernel
example : ({ input with bytes := bytes.set 66 0xc3 } : FunctionInput).checkWith 68 file name = false :=
  by decide +kernel
example : input.checkWith 68 file [0x68, 0x65, 0x6c, 0x70, 0x65, 0x72] = false := by decide +kernel
example : ({ input with function := { input.function with
    window := ⟨0x400081, 0x80⟩ } } : FunctionInput).checkWith 68 file name = false := by decide +kernel
example : ({ input with function := { input.function with
    window := ⟨0x400080, 0x81⟩ } } : FunctionInput).checkWith 68 file name = false := by decide +kernel

-- Consistent file/witness changes isolate bound and permission checks instead
-- of obtaining accidental rejection from stale metadata fields.
example : (inputAt 0x400080 5 68 67).checkWith 68 (fileAt 0x400080 5 68 67) name = false :=
  by decide +kernel
example : (inputAt (2^47 + 0x80) 5 68 68).checkWith 68
    (fileAt (2^47 + 0x80) 5 68 68) name = false := by decide +kernel
example : (inputAt (2^64 - 32) 5 68 68).checkWith 68
    (fileAt (2^64 - 32) 5 68 68) name = false := by decide +kernel
example : (inputAt 0x400080 4 68 68).checkWith 68 (fileAt 0x400080 4 68 68) name = false :=
  by decide +kernel
example : (inputAt 0x400080 1 68 68).checkWith 68 (fileAt 0x400080 1 68 68) name = false :=
  by decide +kernel
example : (inputAt 0x400080 5 67 68).checkWith 68 (fileAt 0x400080 5 67 68) name = false :=
  by decide +kernel
example : input.checkWith 68 (file.take 703) name = false := by decide +kernel
example : input.checkWith 68 (putLE file 58 2 63) name = false := by decide +kernel
example : input.checkWith 68 (putLE file 0x238 8 16) name = false := by decide +kernel

-- Explicitly enlarging the byte cap preserves the established competing-page
-- and affine LOAD-mapping controls, even where the literal code bytes match.
example : FunctionWindow.checkWith 68 ELFFunctionWindow.sharedPage.1
    ELFFunctionWindow.sharedPage.2 ELFFunctionWindow.window ELFFunctionWindow.bytes = false :=
  by decide +kernel
example : FunctionWindow.checkWith 68 ELFFunctionWindow.partialOverlap.1
    ELFFunctionWindow.partialOverlap.2 ELFFunctionWindow.window ELFFunctionWindow.bytes = false :=
  by decide +kernel
example : FunctionSymbol.checkWith 68 ELFFunctionSymbol.wrongLoadOffset.file
    ELFFunctionSymbol.wrongLoadOffset.table ELFFunctionSymbol.wrongLoadOffset.metadata
    ELFFunctionSymbol.wrongLoadOffset.name ELFFunctionSymbol.wrongLoadOffset.selected
    ELFFunctionSymbol.wrongLoadOffset.bytes = false := by decide +kernel

-- Complete independently described CFG, including the unreachable suffix.
def graph : CFG.Graph := CFG.annotate
  ([⟨0, .legacy (.mov32 .rax 42), false, 0⟩, ⟨5, .legacy .ret, false, 0⟩] ++
    (List.range 30).map (fun i => ⟨6 + 2 * i, .nop .two, false, 0⟩) ++
    [⟨66, .nop .one, false, 0⟩, ⟨67, .legacy .ret, false, 0⟩])

theorem cfgChecked : CFG.checkWith profile bytes graph = true := by decide +kernel
theorem valid : CFG.Valid bytes graph profile := CFG.checkWith_sound cfgChecked
example : CFG.check bytes graph = false := by decide +kernel
example : CFG.checkWith ⟨68, 32, by decide⟩ bytes graph = false := by decide +kernel
example : CFG.checkWith profile bytes { graph with nodes := graph.nodes.take 2 } = false :=
  by decide +kernel
example : CFG.checkWith profile (bytes.set 66 0xc3) graph = false := by decide +kernel

def installed : ELF.Loaded := ⟨input.table.image, ELF.install file input.table.image empty⟩

theorem admitted : input.admitWith 68 file name empty = .ok installed := by
  have namedChecked : FunctionSymbol.checkWith 68 file input.table input.metadata name
      input.function input.bytes = true := accepted
  have windowChecked : FunctionWindow.checkWith 68 file input.table input.function.window
      input.bytes = true := (Bool.and_eq_true_iff.mp namedChecked).2
  simp [FunctionInput.admitWith, FunctionSymbol.admitWith, namedChecked,
    FunctionWindow.admitWith, windowChecked, ELFFunctionSymbol.freshEmpty, installed]

-- These are actual executions of the complete installed text. The independent
-- contract observes the constant result and protected caller return. Static
-- bounds supply no extra execution fuel or permission for a missing stack.
def caller : Space where
  cells address :=
    if address = 0x8001 then some ⟨0x20, readWrite⟩
    else if 0x8000 ≤ address.toNat ∧ address.toNat < 0x8008 then some ⟨0, readWrite⟩
    else none

def initial (prior : Space) : State where
  registers register := if register = .rsp then 0x8000 else 0
  rip := 0x400080
  flags := 0x202
  memory := toMemory (ELF.install file input.table.image prior)

def observed : Option (Word × Word × Word × Nat) := do
  let result ← (Sequential.run (fun _ => false) 2 (initial caller)).toOption
  return (result.state.registers .rax, result.state.rip, result.state.registers .rsp,
    result.instructions)

example : observed = some (42, 0x2000, 0x8008, 2) := by decide +kernel
example : observed ≠ some (43, 0x2000, 0x8008, 2) := by decide +kernel
example : (Sequential.run (fun _ => false) 2 (initial empty)).isOk = false := by decide +kernel

-- The same production VC admission API still requires an independent result
-- contract and caller read authority. A readable stack does not grant the
-- client's AllowedRead policy, and larger static caps prove no postcondition.
def clientCheck (expected : Word) (allowRead : Bool) : Bool :=
  let allowed : State → Read → Prop := fun _ _ => allowRead = true
  let post : VCGen.Contract := fun result =>
    result.state.registers .rax = expected ∧ result.state.rip = 0x2000 ∧
    result.state.registers .rsp = 0x8008 ∧ result.instructions = 2
  letI := VCGen.decidableWP graph 0x400080 allowed (fun _ _ => inferInstance)
    2 valid.entry (initial caller) post (fun _ => inferInstance)
  VCGen.certifyWith profile bytes graph 0x400080 allowed 2 valid.entry (initial caller) post

theorem clientAccepted : clientCheck 42 true = true := by decide +kernel
example : clientCheck 43 true = false := by decide +kernel
example : clientCheck 42 false = false := by decide +kernel

private def data (artifact : List Byte) : ByteArray :=
  ⟨artifact.toArray.map fun byte => byte.toNat.toUInt8⟩

-- Extraction is untrusted execution, separate from the kernel proofs above.
-- Expected bytes are an independent instruction-level contract, not a copy of
-- the extractor's offset/size calculations.
def extractionChecks : List (String × Bool) := [
  ("default rejects 68-byte function", !(FunctionCandidate.extract (data file) name).isOk),
  ("explicit bound extracts full named extent", match FunctionCandidate.extractWith 68 (data file) name with
    | .ok candidate => candidate.bytes ==
        ([0xb8, 42, 0, 0, 0, 0xc3] ++ (List.replicate 30 [0x66, 0x90]).flatten ++ [0x90, 0xc3])
    | .error _ => false),
  ("undersized explicit bound rejects", !(FunctionCandidate.extractWith 67 (data file) name).isOk),
  ("malformed symbol row rejects", !(FunctionCandidate.extractWith 68
    (data (putLE file 0x238 8 16)) name).isOk),
  ("missing execute rejects", !(FunctionCandidate.extractWith 68
    (data (fileAt 0x400080 4 68 68)) name).isOk)]

def run : IO Unit := do
  for (label, passed) in extractionChecks do
    unless passed do throw (IO.userError s!"ELF explicit bound regression: {label}")
  (← IO.getStdout).putStrLn s!"PASS: {extractionChecks.length} explicit named ELF extraction regressions"

end EDSL.Tests.ELFFunctionBounds

#print axioms EDSL.ELF.FunctionWindow.selection_soundWith
#print axioms EDSL.ELF.FunctionWindow.selected_segmentWith
#print axioms EDSL.ELF.FunctionSymbol.admitted_soundWith
#print axioms EDSL.ELF.FunctionSymbol.admitted_current_codeWith
#print axioms EDSL.Tests.ELFFunctionBounds.binding
#print axioms EDSL.Tests.ELFFunctionBounds.loadedCode
#print axioms EDSL.Tests.ELFFunctionBounds.valid
#print axioms EDSL.Tests.ELFFunctionBounds.clientAccepted
#audit_edsl
