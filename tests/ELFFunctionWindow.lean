/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.ELF.FunctionWindow
import EDSL.X86.VCGen.Core
import EDSL.Audit

namespace EDSL.Tests.ELFFunctionWindow
open X86 OS.AddressSpace ELF.FunctionWindow

-- Independently laid out ELF: RX text at file 256 / VA 0x400100, RW data at
-- file 512 / VA 0x402200, one NOTE and a null section table at file 576.
-- Entry precedes the callable window. Data deliberately repeats its bytes.
private def little (width value : Nat) : List Byte :=
  (List.range width).map fun index => BitVec.ofNat 8 (value / 256^index)

private def row (kind flags offset address fileSize memorySize alignment : Nat) : List Byte :=
  little 4 kind ++ little 4 flags ++ little 8 offset ++ little 8 address ++
  little 8 address ++ little 8 fileSize ++ little 8 memorySize ++ little 8 alignment

def file : List Byte :=
  [0x7f, 0x45, 0x4c, 0x46, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    2, 0, 62, 0, 1, 0, 0, 0, 0, 1, 0x40, 0, 0, 0, 0, 0,
    64, 0, 0, 0, 0, 0, 0, 0, 64, 2, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 64, 0, 56, 0, 3, 0, 64, 0, 1, 0, 0, 0] ++
  row 1 5 256 0x400100 16 32 4096 ++
  row 1 6 512 0x402200 16 32 4096 ++
  row 4 4 544 0x400220 16 16 4 ++ List.replicate 24 0 ++
  [0x90, 0x90, 0x90, 0x90, 0x48, 0x89, 0xf8, 0xc3,
    0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90] ++
  List.replicate 240 0 ++ [0x48, 0x89, 0xf8, 0xc3] ++ List.replicate 124 0

def table : Table := ⟨⟨0, 0x400100, 64, 576, 1, 0⟩, [
  ⟨1, 0x400100, ⟨256, 0x400100, 16, 32, 5, 4096⟩⟩,
  ⟨1, 0x402200, ⟨512, 0x402200, 16, 32, 6, 4096⟩⟩,
  ⟨4, 0x400220, ⟨544, 0x400220, 16, 16, 4, 4⟩⟩]⟩

def window : Window := ⟨0x400104, 260⟩
def bytes : List Byte := [0x48, 0x89, 0xf8, 0xc3] -- mov rax,rdi; ret

theorem accepted : check file table window bytes = true := by decide +kernel

-- A real modeled call/return checks arbitrary-address binding, instruction
-- decoding, the caller return stack, executable permissions and caller framing.
def caller : Space where
  cells address :=
    if address = 0x8001 then some ⟨0x20, readWrite⟩
    else if 0x8000 ≤ address.toNat ∧ address.toNat < 0x8008 then some ⟨0, readWrite⟩
    else if address = 0x10000 then some ⟨0xa5, inaccessible⟩ else none

def observed : Option (Word × Word × Word × Nat × Option Byte) := do
  let loaded ← (admit file table window bytes caller).toOption
  let initial : State := {
    registers := fun register => if register = .rdi then 0xfedcba9876543210
      else if register = .rsp then 0x8000 else 0
    rip := window.base
    flags := 0x202
    memory := toMemory loaded.space }
  let result ← (Sequential.run (fun _ => false) 2 initial).toOption
  return (result.state.registers .rax, result.state.rip, result.state.registers .rsp,
    result.instructions, contents loaded.space 0x10000)

example : observed = some (0xfedcba9876543210, 0x2000, 0x8008, 2, some 0xa5) := by
  decide +kernel

-- Truncation of the header, a program row, a selected byte, or the declared
-- section table must fail, even if another part still contains the code bytes.
example : check (file.take 63) table window bytes = false := by decide +kernel
example : check (file.take 210) table window bytes = false := by decide +kernel
example : check (file.take 263) table window bytes = false := by decide +kernel
example : check (file.take 639) table window bytes = false := by decide +kernel

-- The data bytes match, but the data LOAD has no execute permission.
example : check file table ⟨0x402200, 512⟩ bytes = false := by decide +kernel
-- Both intervals contain the same bytes; only one has the selected VA mapping.
example : check file table { window with offset := 512 } bytes = false := by decide +kernel
-- Bind actual file bytes, rather than accepting a stale extractor's window.
example : check (file.set 262 0xf0) table window bytes = false := by decide +kernel
example : check file table window [0x48, 0x89, 0xf0, 0xc3] = false := by decide +kernel
-- A matching zero BSS byte still cannot extend the file-backed text interval.
example : check file table ⟨0x40010f, 271⟩ [0x90, 0] = false := by decide +kernel
-- Declared PHDR count must account for every supplied mapping witness.
example : check (file.set 56 2) table window bytes = false := by decide +kernel
-- Mutation outside the selected source interval can invalidate LOAD metadata.
example : check (file.set 68 4) table window bytes = false := by decide +kernel

-- Keep witness and source permissions in agreement: execute-only LOADs cannot
-- use the model's always-readable Segment.permissions as a fallback.
def executeOnly : List Byte × Table :=
  (file.set 68 1,
    { table with programs := table.programs.set 0 ⟨1, 0x400100, ⟨256, 0x400100, 16, 32, 1, 4096⟩⟩ })

example : check executeOnly.1 executeOnly.2 window bytes = false := by decide +kernel

-- An exactly matched but unsupported row kind is not treated as inert data.
def unknownMetadata : List Byte × Table :=
  (file.set 176 7,
    { table with programs := table.programs.set 2 ⟨7, 0x400220, ⟨544, 0x400220, 16, 16, 4, 4⟩⟩ })

example : check unknownMetadata.1 unknownMetadata.2 window bytes = false := by decide +kernel

private def replaceNat (data : List Byte) (offset width value : Nat) : List Byte :=
  ((little width value).zipIdx).foldl (fun result (byte, index) =>
    result.set (offset + index) byte) data

-- Move the complete second LOAD, in both file metadata and witness. This
-- prevents field mismatch from masking the page-collision validation itself.
private def moveData (address : Nat) : List Byte × Table :=
  (replaceNat (replaceNat file 136 8 address) 144 8 address,
    { table with programs := [
      ⟨1, 0x400100, ⟨256, 0x400100, 16, 32, 5, 4096⟩⟩,
      ⟨1, address, ⟨512, address, 16, 32, 6, 1⟩⟩,
      ⟨4, 0x400220, ⟨544, 0x400220, 16, 16, 4, 4⟩⟩] })

-- Disjoint bytes can share an OS page. Alignment=1 still requires page-offset
-- congruence through Segment.valid; the same-page test preserves congruence.
def sharedPage : List Byte × Table :=
  let (data, witness) := moveData 0x400200
  (replaceNat data 168 8 1, witness)

example : check sharedPage.1 sharedPage.2 window bytes = false := by decide +kernel

-- A competing LOAD partly covers the selected function, with consistent
-- file/VA page offsets, so even a one-covering-segment-only test would miss it.
def partialOverlap : List Byte × Table :=
  let address := 0x400106
  let data := replaceNat (replaceNat (replaceNat (replaceNat file
    128 8 262) 136 8 address) 144 8 address) 168 8 1
  (data, { table with programs := [
    ⟨1, 0x400100, ⟨256, 0x400100, 16, 32, 5, 4096⟩⟩,
    ⟨1, address, ⟨262, address, 16, 32, 6, 1⟩⟩,
    ⟨4, 0x400220, ⟨544, 0x400220, 16, 16, 4, 4⟩⟩] })

example : check partialOverlap.1 partialOverlap.2 window bytes = false := by decide +kernel

-- The declared whole-file bound is unchanged from the legacy profile.
example : check (file ++ List.replicate 65536 0) table window bytes = false := by decide +kernel

def collision : Space where
  cells address := if address = 0x400000 then some ⟨0x5a, inaccessible⟩ else none

def collisionRejected : Bool :=
  match admit file table window bytes collision with
  | .error .mappingCollision => true
  | _ => false

example : collisionRejected = true := by decide +kernel

-- Typed generic composition: the ELF bridge supplies precisely the CodeAt
-- premise used by the production Sequential VC generator. ABI, read authority,
-- the VC, and any post-installation text preservation remain explicit.
theorem vcgen_composition {artifact code : List Byte} {metadata : Table} {selected : Window}
    {prior : Space} {loaded : ELF.Loaded} {initial : State}
    (admitted : admit artifact metadata selected code prior = .ok loaded)
    (unchanged : TextUnchanged (toMemory loaded.space) initial.memory selected code.length)
    {graph : Sequential.CFG.Graph} (valid : Sequential.CFG.Valid code graph)
    {AllowedRead : State → Sequential.Read → Prop} {fuel : Nat} {node : graph.Index}
    {Post : VCGen.Contract}
    (pc : initial.rip = selected.base + BitVec.ofNat 64 (graph.node node).offset)
    (vc : VCGen.wp graph selected.base AllowedRead fuel node initial Post)
    (choices : Sequential.Choices) :
    ∃ result, Sequential.run choices fuel initial = .ok result ∧ Post result ∧
      result.instructions ≤ fuel ∧ VCGen.CheckedTrace AllowedRead choices initial result :=
  VCGen.run_sound valid (admitted_current_code admitted unchanged) pc vc choices

end EDSL.Tests.ELFFunctionWindow

#check @EDSL.ELF.FunctionWindow.selection_sound
#check @EDSL.ELF.FunctionWindow.admitted_sound
#check @EDSL.ELF.FunctionWindow.admitted_current_code
#print axioms EDSL.ELF.FunctionWindow.selection_sound
#print axioms EDSL.ELF.FunctionWindow.selected_segment
#print axioms EDSL.ELF.FunctionWindow.admitted_sound
#print axioms EDSL.ELF.FunctionWindow.admitted_current_code
#print axioms EDSL.Tests.ELFFunctionWindow.vcgen_composition
#audit_edsl
