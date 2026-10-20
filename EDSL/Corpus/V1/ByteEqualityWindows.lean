/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.FrozenFunction

set_option autoImplicit false
set_option warningAsError true

/-! Complete unchanged row20 windows. File/name/extent authentication is
separate from decoding, independent result contracts and corpus credit. -/

namespace EDSL.Corpus.V1.ByteEqualityWindows
open X86 ELF.FunctionSymbol

abbrev Compiler := FrozenFunction.Compiler
abbrev file := FrozenFunction.file

def name : List Byte := [99,95,98,121,116,101,115,95,101,113,117,97,108]

def bytes : Compiler → List Byte
  | .defaultGCC => [0xf3,0x0f,0x1e,0xfa,0x48,0x85,0xd2,0x74,0x1f,0x31,0xc0,0xeb,0x0c,0x0f,0x1f,0,0x48,0x83,0xc0,1,0x48,0x39,0xc2,0x74,0x0f,0x0f,0xb6,0x0c,6,0x38,0x0c,7,0x74,0xee,0x31,0xc0,0xc3,0x0f,0x1f,0,0xb8,1,0,0,0,0xc3]
  | .defaultClang => [0x48,0x85,0xd2,0x74,0x39,0x0f,0xb6,7,0x3a,6,0x75,0x35,0xb9,1,0,0,0,0x66,0x66,0x66,0x66,0x66,0x66,0x2e,0x0f,0x1f,0x84,0,0,0,0,0,0x48,0x89,0xc8,0x48,0x39,0xca,0x74,0x0f,0x44,0x0f,0xb6,4,7,0x48,0x8d,0x48,1,0x44,0x3a,4,6,0x74,0xe9,0x48,0x39,0xd0,0x0f,0x93,0xc0,0xc3,0xb0,1,0xc3,0x31,0xc0,0xc3]

def symbolIndex (compiler : Compiler) : Fin (FrozenFunction.symbols compiler).rows.length :=
  match compiler with
  | .defaultGCC => ⟨110, by decide +kernel⟩
  | .defaultClang => ⟨86, by decide +kernel⟩

def function (compiler : Compiler) : Function :=
  FrozenFunction.function compiler (symbolIndex compiler)

def input (compiler : Compiler) : FunctionInput :=
  FrozenFunction.input compiler (symbolIndex compiler) (bytes compiler)

def maxBytes : Compiler → Nat
  | .defaultGCC => 64
  | .defaultClang => 128

theorem body (compiler : Compiler) : (input compiler).bytes = bytes compiler := rfl

/-- The original complete-file checker authenticates both requested names,
unique entire extents and executable mappings; metadata hints grant no proof. -/
theorem checked (compiler : Compiler) :
    (input compiler).checkWith (maxBytes compiler) (file compiler) name = true := by
  cases compiler with
  | defaultGCC =>
    change checkWith 64 GCC.file GCC.table GCC.metadata name (function .defaultGCC)
      (bytes .defaultGCC) = true
    unfold checkWith
    rw [GCC.metadataAccepted]
    change (true && decide ((function .defaultGCC).Contract GCC.metadata name
      (bytes .defaultGCC).length) &&
      (ELF.FunctionWindow.checkLayout GCC.file GCC.table &&
       decide ((function .defaultGCC).window.BoundsWith 64 GCC.file.length (bytes .defaultGCC).length) &&
       GCC.table.image.segments.any (fun segment =>
         decide ((function .defaultGCC).window.CoveredBy (bytes .defaultGCC).length segment)) &&
       decide ((GCC.file.drop (function .defaultGCC).window.offset).take (bytes .defaultGCC).length =
         bytes .defaultGCC) &&
       ELF.checkCode (OS.AddressSpace.toMemory (ELF.install GCC.file GCC.table.image OS.AddressSpace.empty))
         (function .defaultGCC).window.base (bytes .defaultGCC))) = true
    have bounded : (function .defaultGCC).window.offset ≤ 41016 := by decide +kernel
    rw [GCC.layoutAccepted, GCC.fileDropChunks _ bounded]
    simp only [GCC.fileLength, ELF.checkCode, X86.fetchByte, OS.AddressSpace.toMemory,
      ELF.install, ELF.segmentCell, GCC.fileByteChunks]
    decide +kernel
  | defaultClang =>
    change checkWith 128 Clang.file Clang.table Clang.metadata name (function .defaultClang)
      (bytes .defaultClang) = true
    unfold checkWith
    rw [Clang.metadataAccepted]
    change (true && decide ((function .defaultClang).Contract Clang.metadata name
      (bytes .defaultClang).length) &&
      (ELF.FunctionWindow.checkLayout Clang.file Clang.table &&
       decide ((function .defaultClang).window.BoundsWith 128 Clang.file.length (bytes .defaultClang).length) &&
       Clang.table.image.segments.any (fun segment =>
         decide ((function .defaultClang).window.CoveredBy (bytes .defaultClang).length segment)) &&
       decide ((Clang.file.drop (function .defaultClang).window.offset).take (bytes .defaultClang).length =
         bytes .defaultClang) &&
       ELF.checkCode (OS.AddressSpace.toMemory (ELF.install Clang.file Clang.table.image OS.AddressSpace.empty))
         (function .defaultClang).window.base (bytes .defaultClang))) = true
    have bounded : (function .defaultClang).window.offset ≤ 44240 := by decide +kernel
    rw [Clang.layoutAccepted, Clang.fileDropAt _ bounded]
    simp only [Clang.fileLength, ELF.checkCode, X86.fetchByte, OS.AddressSpace.toMemory,
      ELF.install, ELF.segmentCell, FrozenFunction.clangFileByte]
    decide +kernel

#print axioms body
#print axioms checked
end EDSL.Corpus.V1.ByteEqualityWindows
#audit_edsl
