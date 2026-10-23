/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.FrozenFunction
import EDSL.X86.VCGen.MixedCFG

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Complete frozen row40 `c_counter_worker` windows, with typed arithmetic-RMW
structural certificates and separate complete-file/name/extent checks. The
existing mixed checker authenticates every instruction and successor against
the bytes; the supplied graph annotations have no independent authority.

This is static admission only. It establishes no function certification,
execution, RMW count, ABI, progress, fairness, loaded-resource authenticity,
lifetime, physical OS or compiler refinement, or corpus credit. Both workers
return void; no RAX or old-word result contract is imposed. ENDBR64 uses the
existing CET/IBT-disabled model and NOP13 the existing exact-padding model;
structural admission does not establish correspondence to physical hardware.
-/

namespace EDSL.Corpus.V1.CounterMixedGraphs
open X86 X86.VCGen.MixedCFG

abbrev Compiler := FrozenFunction.Compiler
abbrev file := FrozenFunction.file

/-- Exact ELF name `c_counter_worker`, without the terminating NUL. -/
def name : List Byte := [99,95,99,111,117,110,116,101,114,95,119,111,114,107,101,114]

/-- Entire declared extents, including both GCC RETs and Clang's single NOP13. -/
def bytes : Compiler → List Byte
  | .defaultGCC =>
    [0xf3,0x0f,0x1e,0xfa,0x85,0xf6,0x74,0x27,0x8d,0x46,0xff,
      0x40,0xf6,0xc6,0x01,0x74,0x0f,0xf0,0x48,0x83,0x07,0x01,
      0x89,0xc6,0x85,0xc0,0x74,0x14,0x0f,0x1f,0x40,0x00,
      0xf0,0x48,0x83,0x07,0x01,0xf0,0x48,0x83,0x07,0x01,
      0x83,0xee,0x02,0x75,0xf1,0xc3,0xc3]
  | .defaultClang =>
    [0x85,0xf6,0x74,0x51,0x89,0xf1,0x89,0xf0,0x83,0xe1,0x07,
      0x74,0x11,0x31,0xd2,0x90,0xf0,0x48,0xff,0x07,0xff,0xc2,
      0x39,0xd1,0x75,0xf6,0x89,0xf0,0x29,0xd0,0x83,0xfe,0x08,
      0x72,0x32,0x66,0x66,0x66,0x66,0x2e,0x0f,0x1f,0x84,0,0,0,0,0,
      0xf0,0x48,0xff,0x07,0xf0,0x48,0xff,0x07,
      0xf0,0x48,0xff,0x07,0xf0,0x48,0xff,0x07,
      0xf0,0x48,0xff,0x07,0xf0,0x48,0xff,0x07,
      0xf0,0x48,0xff,0x07,0xf0,0x48,0xff,0x07,
      0x83,0xc0,0xf8,0x75,0xdb,0xc3]

/-- Fixed static caps, chosen separately from the byte and graph proposals. -/
def caps : Compiler → Caps
  | .defaultGCC => ⟨64, 32, by decide +kernel⟩
  | .defaultClang => ⟨128, 32, by decide +kernel⟩

/-- Untrusted hints from the existing complete static symbol tables. The
named check authenticates the entire declared extents against the full files. -/
def function : Compiler → ELF.FunctionSymbol.Function
  | .defaultGCC => {
      occurrence := { table := 27, index := 134, symbol := {
        nameOffset := 2056, info := 18, other := 0, sh := 14, value := 4207440, size := 49 } }
      sh := GCC.sh14
      window := { address := 4207440, offset := 13136 } }
  | .defaultClang => {
      occurrence := { table := 26, index := 111, symbol := {
        nameOffset := 1823, info := 18, other := 0, sh := 13, value := 4201344, size := 86 } }
      sh := Clang.sh13
      window := { address := 4201344, offset := 7040 } }

/-- Reuse each original file table and metadata; only the selected hints and
complete byte window change. No ELF is reconstructed for these instances. -/
def input (compiler : Compiler) : ELF.FunctionInput := {
  ArithmeticWindows.input compiler with function := function compiler, bytes := bytes compiler }

/-- Real LOCK ADD-imm8 tag; it has no old-word destination. -/
def addOne : OS.TSO64.Decoded .arithmetic := .locked (.addImm8 {
  rex := 0x48, modrm := 0x07, imm8 := 1
  rexSupported := by decide +kernel
  indirect := by decide +kernel
  groupZero := by decide +kernel })

/-- Real four-byte LOCK INC tag, retaining its distinct instruction family. -/
def incOne : OS.TSO64.Decoded .arithmetic := .locked (.inc {
  rex := 0x48, modrm := 0x07
  rexSupported := by decide +kernel
  indirect := by decide +kernel
  groupZero := by decide +kernel })

/-- Complete typed proposals. Cuts and depths prove only finite acyclic
interiors; each locked site's retired continuation remains a real graph edge. -/
def graph : Compiler → Graph .arithmetic
  | .defaultGCC => ⟨[
    ⟨0, .ordinary .endbr64IbtDisabled, true, 17⟩,
    ⟨4, .ordinary (.test32 .rsi .rsi false), false, 16⟩,
    ⟨6, .ordinary (.je 0x27), false, 15⟩,
    ⟨8, .ordinary (.lea32 .rax (.baseDisp8 .rsi 0xff) false), false, 14⟩,
    ⟨11, .ordinary (.testImm8 .rsi 1 true), false, 13⟩,
    ⟨15, .ordinary (.je 0x0f), false, 12⟩,
    ⟨17, addOne, false, 11⟩,
    ⟨22, .ordinary (.movReg32 .rsi .rax), false, 10⟩,
    ⟨24, .ordinary (.test32 .rax .rax false), false, 9⟩,
    ⟨26, .ordinary (.je 0x14), false, 8⟩,
    ⟨28, .ordinary (.nop .four), false, 7⟩,
    ⟨32, addOne, true, 6⟩,
    ⟨37, addOne, false, 5⟩,
    ⟨42, .ordinary (.subImm32 .rsi 2 false), false, 4⟩,
    ⟨45, .ordinary (.legacy (.jnz 0xf1)), false, 3⟩,
    ⟨47, .ordinary (.legacy .ret), false, 2⟩,
    ⟨48, .ordinary (.legacy .ret), false, 1⟩], 17⟩
  | .defaultClang => ⟨[
    ⟨0, .ordinary (.test32 .rsi .rsi false), true, 28⟩,
    ⟨2, .ordinary (.je 0x51), false, 27⟩,
    ⟨4, .ordinary (.movReg32 .rcx .rsi), false, 26⟩,
    ⟨6, .ordinary (.legacy .movEaxEsi), false, 25⟩,
    ⟨8, .ordinary (.logicalImm32 .band .rcx 7 false), false, 24⟩,
    ⟨11, .ordinary (.je 0x11), false, 23⟩,
    ⟨13, .ordinary (.xorSelf32 .rdx), false, 22⟩,
    ⟨15, .ordinary (.nop .one), false, 21⟩,
    ⟨16, incOne, true, 20⟩,
    ⟨20, .ordinary (.inc32 .rdx false), false, 19⟩,
    ⟨22, .ordinary (.cmp32 .rcx .rdx false), false, 18⟩,
    ⟨24, .ordinary (.legacy (.jnz 0xf6)), false, 17⟩,
    ⟨26, .ordinary (.legacy .movEaxEsi), false, 16⟩,
    ⟨28, .ordinary (.subReg32 .rax .rdx false), false, 15⟩,
    ⟨30, .ordinary (.cmpImm32 .rsi 8 false), false, 14⟩,
    ⟨33, .ordinary (.jcc .below 0x32), false, 13⟩,
    ⟨35, .ordinary (.nop .thirteen), false, 12⟩,
    ⟨48, incOne, true, 11⟩,
    ⟨52, incOne, false, 10⟩,
    ⟨56, incOne, false, 9⟩,
    ⟨60, incOne, false, 8⟩,
    ⟨64, incOne, false, 7⟩,
    ⟨68, incOne, false, 6⟩,
    ⟨72, incOne, false, 5⟩,
    ⟨76, incOne, false, 4⟩,
    ⟨80, .ordinary (.addImm32 .rax 0xf8 false), false, 3⟩,
    ⟨83, .ordinary (.legacy (.jnz 0xdb)), false, 2⟩,
    ⟨85, .ordinary (.legacy .ret), false, 1⟩], 28⟩

/-- Authenticate the entire partition and actual decoded tags, with explicit
arithmetic family and fixed caps, using the independent production checker. -/
theorem checked (compiler : Compiler) :
    checkWith .arithmetic (caps compiler) (bytes compiler) (graph compiler) = true := by
  cases compiler <;> decide +kernel

theorem structural (compiler : Compiler) :
    Valid .arithmetic (caps compiler) (input compiler).bytes (graph compiler) :=
  checkWith_sound (checked compiler)

/-- Bind the requested name and complete extent to the original complete
literal ELF. Reuse its checked metadata, layout and absolute byte lookups. -/
theorem namedChecked (compiler : Compiler) :
    (input compiler).checkWith (caps compiler).maxBytes (file compiler) name = true := by
  cases compiler with
  | defaultGCC =>
    change ELF.FunctionSymbol.checkWith 64 GCC.file GCC.table GCC.metadata name
      (function .defaultGCC) (bytes .defaultGCC) = true
    unfold ELF.FunctionSymbol.checkWith
    rw [GCC.metadataAccepted]
    unfold ELF.FunctionWindow.checkWith
    have offset : (function .defaultGCC).window.offset = 13136 := rfl
    rw [GCC.layoutAccepted, offset, GCC.fileDropChunks 13136 (by decide +kernel)]
    simp only [GCC.fileLength, ELF.checkCode, X86.fetchByte, OS.AddressSpace.toMemory,
      ELF.install, ELF.segmentCell, GCC.fileByteChunks]
    decide +kernel
  | defaultClang =>
    change ELF.FunctionSymbol.checkWith 128 Clang.file Clang.table Clang.metadata name
      (function .defaultClang) (bytes .defaultClang) = true
    unfold ELF.FunctionSymbol.checkWith
    rw [Clang.metadataAccepted]
    unfold ELF.FunctionWindow.checkWith
    have offset : (function .defaultClang).window.offset = 7040 := rfl
    rw [Clang.layoutAccepted, offset, Clang.fileDropAt 7040 (by decide +kernel)]
    simp only [Clang.fileLength, ELF.checkCode, X86.fetchByte, OS.AddressSpace.toMemory,
      ELF.install, ELF.segmentCell, FrozenFunction.clangFileByte]
    decide +kernel

/-- Static packaging only: complete named-file admission and mixed structural
admission share exactly the same caller-selected byte cap. No installation or
current runtime authenticity is a consequence of these two proof fields. -/
structure NamedValid (family : OS.TSO64.RMWFamily) (caps : Caps) (file name : List Byte)
    (input : ELF.FunctionInput) (graph : Graph family) : Prop where
  named : input.checkWith caps.maxBytes file name = true
  structural : Valid family caps input.bytes graph

/-- The complete frozen named windows with their arithmetic structural proofs. -/
theorem namedValid (compiler : Compiler) :
    NamedValid .arithmetic (caps compiler) (file compiler) name (input compiler) (graph compiler) :=
  ⟨namedChecked compiler, structural compiler⟩

#print axioms checked
#print axioms structural
#print axioms namedChecked
#print axioms namedValid
end EDSL.Corpus.V1.CounterMixedGraphs
#audit_edsl
