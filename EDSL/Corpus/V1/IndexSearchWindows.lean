/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.FrozenFunction

set_option autoImplicit false
set_option warningAsError true

/-! Complete unchanged row21/25 function windows. Kernel file/name/extent
authentication is separate from decoding, program semantics and corpus credit. -/

namespace EDSL.Corpus.V1.IndexSearchWindows
open X86 ELF.FunctionSymbol

abbrev Compiler := FrozenFunction.Compiler
abbrev file := FrozenFunction.file

inductive Operation where
  | byte | u32
  deriving DecidableEq, Repr

def name : Operation → List Byte
  | .byte => [99,95,109,101,109,99,104,114,95,105,110,100,101,120]
  | .u32 => [99,95,108,105,110,101,97,114,95,115,101,97,114,99,104,95,117,51,50]

/-- The two element widths share each compiler's complete loop topology.
Only the comparison opcode and SIB scale differ. Every padding/return byte
is included; the full-file check below authenticates both complete windows. -/
def bytes (compiler : Compiler) (operation : Operation) : List Byte :=
  match compiler with
  | .defaultGCC =>
    ([0xf3,0x0f,0x1e,0xfa,0x48,0x85,0xf6,0x74,0x17,0x31,0xc0,0xeb,0x0c,0x0f,0x1f,0x00,
      0x48,0x83,0xc0,0x01,0x48,0x39,0xc6,0x74,0x07] : List Byte) ++
      ((match operation with | .byte => [0x38,0x14,0x07] | .u32 => [0x39,0x14,0x87]) : List Byte) ++
      ([0x75,0xf2,0xc3,0x90,0x48,0xc7,0xc0,0xff,0xff,0xff,0xff,0xc3] : List Byte)
  | .defaultClang =>
    ([0x48,0xc7,0xc0,0xff,0xff,0xff,0xff,0x48,0x85,0xf6,0x74,0x11,0x31,0xc9,0x66,0x90] : List Byte) ++
      ((match operation with | .byte => [0x38,0x14,0x0f] | .u32 => [0x39,0x14,0x8f]) : List Byte) ++
      ([0x74,0x09,0x48,0xff,0xc1,0x48,0x39,0xce,0x75,0xf3,0xc3,0x48,0x89,0xc8,0xc3] : List Byte)

def symbolIndex (compiler : Compiler) (operation : Operation) :
    Fin (FrozenFunction.symbols compiler).rows.length :=
  match compiler, operation with
  | .defaultGCC, .byte => ⟨116, by decide +kernel⟩
  | .defaultGCC, .u32 => ⟨126, by decide +kernel⟩
  | .defaultClang, .byte => ⟨93, by decide +kernel⟩
  | .defaultClang, .u32 => ⟨103, by decide +kernel⟩

def function (compiler : Compiler) (operation : Operation) : Function :=
  FrozenFunction.function compiler (symbolIndex compiler operation)

def input (compiler : Compiler) (operation : Operation) : FunctionInput :=
  FrozenFunction.input compiler (symbolIndex compiler operation) (bytes compiler operation)

theorem body (compiler : Compiler) (operation : Operation) :
    (input compiler operation).bytes = bytes compiler operation := rfl

/-- Authenticate all four names and complete extents against the same full
literal files and previously checked metadata, with no host extractor premise. -/
theorem checked (compiler : Compiler) (operation : Operation) :
    (input compiler operation).check (file compiler) (name operation) = true := by
  cases compiler with
  | defaultGCC =>
    change check GCC.file GCC.table GCC.metadata (name operation) (function .defaultGCC operation)
      (bytes .defaultGCC operation) = true
    unfold check
    rw [GCC.metadataAccepted]
    unfold ELF.FunctionWindow.check
    have bounded : (function .defaultGCC operation).window.offset ≤ 41016 := by
      cases operation <;> decide +kernel
    rw [GCC.layoutAccepted, GCC.fileDropChunks _ bounded]
    simp only [GCC.fileLength, ELF.checkCode, X86.fetchByte, OS.AddressSpace.toMemory,
      ELF.install, ELF.segmentCell, GCC.fileByteChunks]
    cases operation <;> decide +kernel
  | defaultClang =>
    change check Clang.file Clang.table Clang.metadata (name operation) (function .defaultClang operation)
      (bytes .defaultClang operation) = true
    unfold check
    rw [Clang.metadataAccepted]
    unfold ELF.FunctionWindow.check
    have bounded : (function .defaultClang operation).window.offset ≤ 44240 := by
      cases operation <;> decide +kernel
    rw [Clang.layoutAccepted, Clang.fileDropAt _ bounded]
    simp only [Clang.fileLength, ELF.checkCode, X86.fetchByte, OS.AddressSpace.toMemory,
      ELF.install, ELF.segmentCell, FrozenFunction.clangFileByte]
    cases operation <;> decide +kernel

#print axioms body
#print axioms checked
end EDSL.Corpus.V1.IndexSearchWindows
#audit_edsl
