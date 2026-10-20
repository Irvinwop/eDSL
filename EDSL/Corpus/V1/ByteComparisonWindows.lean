/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.FrozenFunction

set_option autoImplicit false
set_option warningAsError true

/-! Complete unchanged row19 windows. File/name/extent authentication is
separate from decoding, independent result contracts and corpus credit. -/

namespace EDSL.Corpus.V1.ByteComparisonWindows
open X86 ELF.FunctionSymbol

abbrev Compiler := FrozenFunction.Compiler
abbrev file := FrozenFunction.file

def name : List Byte := [99,95,109,101,109,99,109,112,95,98,121,116,101,115]

def bytes : Compiler → List Byte
  | .defaultGCC => [0xf3,0x0f,0x1e,0xfa,0x48,0x85,0xd2,0x74,0x27,0x31,0xc0,0xeb,0x0c,0x0f,0x1f,0x00,0x48,0x83,0xc0,0x01,0x48,0x39,0xc2,0x74,0x17,0x0f,0xb6,0x0c,0x07,0x44,0x0f,0xb6,0x04,0x06,0x44,0x38,0xc1,0x74,0xe9,0x0f,0xb6,0xc1,0x44,0x29,0xc0,0xc3,0x66,0x90,0x31,0xc0,0xc3]
  | .defaultClang => [0x48,0x85,0xd2,0x74,0x21,0x31,0xc9,0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00,0x0f,0xb6,0x04,0x0f,0x44,0x0f,0xb6,0x04,0x0e,0x44,0x38,0xc0,0x75,0x0b,0x48,0xff,0xc1,0x48,0x39,0xca,0x75,0xea,0x31,0xc0,0xc3,0x44,0x29,0xc0,0xc3]

def symbolIndex (compiler : Compiler) : Fin (FrozenFunction.symbols compiler).rows.length :=
  match compiler with
  | .defaultGCC => ⟨85, by decide +kernel⟩
  | .defaultClang => ⟨59, by decide +kernel⟩

def function (compiler : Compiler) : Function :=
  FrozenFunction.function compiler (symbolIndex compiler)

def input (compiler : Compiler) : FunctionInput :=
  FrozenFunction.input compiler (symbolIndex compiler) (bytes compiler)

theorem body (compiler : Compiler) : (input compiler).bytes = bytes compiler := rfl

/-- The original complete-file checker authenticates both requested names,
unique entire extents and executable mappings; metadata hints grant no proof. -/
theorem checked (compiler : Compiler) :
    (input compiler).check (file compiler) name = true := by
  cases compiler with
  | defaultGCC =>
    change check GCC.file GCC.table GCC.metadata name (function .defaultGCC)
      (bytes .defaultGCC) = true
    unfold check
    rw [GCC.metadataAccepted]
    unfold ELF.FunctionWindow.check
    have bounded : (function .defaultGCC).window.offset ≤ 41016 := by decide +kernel
    rw [GCC.layoutAccepted, GCC.fileDropChunks _ bounded]
    simp only [GCC.fileLength, ELF.checkCode, X86.fetchByte, OS.AddressSpace.toMemory,
      ELF.install, ELF.segmentCell, GCC.fileByteChunks]
    decide +kernel
  | defaultClang =>
    change check Clang.file Clang.table Clang.metadata name (function .defaultClang)
      (bytes .defaultClang) = true
    unfold check
    rw [Clang.metadataAccepted]
    unfold ELF.FunctionWindow.check
    have bounded : (function .defaultClang).window.offset ≤ 44240 := by decide +kernel
    rw [Clang.layoutAccepted, Clang.fileDropAt _ bounded]
    simp only [Clang.fileLength, ELF.checkCode, X86.fetchByte, OS.AddressSpace.toMemory,
      ELF.install, ELF.segmentCell, FrozenFunction.clangFileByte]
    decide +kernel

#print axioms body
#print axioms checked
end EDSL.Corpus.V1.ByteComparisonWindows
#audit_edsl
