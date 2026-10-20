/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.Certificate
import EDSL.Corpus.V1.GCC
import EDSL.Corpus.V1.Clang
import EDSL.X86.VCGen.CompilerComparisons

/-!
Exact complete `c_clamp_i32` named windows from the two frozen compiler files.
This data adapter checks file, symbol, extent and executable image bytes only.
Mathematical behavior, current-resource admission and corpus credit require
separate proofs.
-/

namespace EDSL.Corpus.V1.ClampWindows
open X86 ELF.FunctionSymbol

abbrev Compiler := X86.VCGen.CompilerComparisons.Compiler

def file : Compiler → List Byte
  | .defaultGCC => GCC.file
  | .defaultClang => Clang.file

/-- The exact ELF byte name `c_clamp_i32`, without its terminating NUL. -/
def name : List Byte := [99,95,99,108,97,109,112,95,105,51,50]

/-- Complete symbol extents, retaining GCC's original ENDBR64. -/
def bytes : Compiler → List Byte
  | .defaultGCC => [0xf3,0x0f,0x1e,0xfa,0x39,0xd7,0x89,0xf0,0x0f,0x4e,0xd7,
      0x39,0xf7,0x0f,0x4d,0xc2,0xc3]
  | .defaultClang => [0x89,0xd0,0x39,0xd7,0x0f,0x4c,0xc7,0x39,0xf7,0x0f,0x4c,0xc6,0xc3]

/-- Untrusted row/section/window hints, validated by `checked` against the
complete shared literal file and all of its symbol tables. Name offsets come
from the frozen files' actual static symbol rows and linked string tables. -/
def function : Compiler → Function
  | .defaultGCC => {
      occurrence := { table := 27, index := 128, symbol := {
        nameOffset := 1958, info := 18, other := 0, sh := 14, value := 4205872, size := 17 } }
      sh := GCC.sh14
      window := { address := 4205872, offset := 11568 } }
  | .defaultClang => {
      occurrence := { table := 26, index := 105, symbol := {
        nameOffset := 1725, info := 18, other := 0, sh := 13, value := 4199120, size := 13 } }
      sh := Clang.sh13
      window := { address := 4199120, offset := 4816 } }

/-- Reuse each compiler's complete file, program table and metadata without
duplicating their data or their validation. -/
def input (compiler : Compiler) : FunctionInput := {
  table := match compiler with
    | .defaultGCC => GCC.table
    | .defaultClang => Clang.table
  metadata := match compiler with
    | .defaultGCC => GCC.metadata
    | .defaultClang => Clang.metadata
  function := function compiler
  bytes := bytes compiler }

theorem body (compiler : Compiler) : (input compiler).bytes = bytes compiler := rfl

private theorem clangFileByte (offset : Nat) :
    Clang.file[offset]? = if offset < 44240 then
      (((Clang.chunks.drop (offset / 128)).flatten).drop (offset % 128))[0]? else none := by
  by_cases inside : offset < 44240
  · rw [ite_eq_left inside]
    have dropped := congrArg (fun source : List Byte => source[0]?)
      (Clang.fileDropAt offset (by omega))
    simpa only [List.getElem?_drop, Nat.add_zero] using dropped
  · rw [ite_eq_right inside]
    exact List.getElem?_eq_none (by rw [Clang.fileLength]; omega)

/-- Exact name uniqueness, global FUNC identity, whole declared size, address,
file offset and bytes under the existing bounded ELF profile. The shared
metadata/layout theorems are reused, not recomputed for the new name. -/
theorem checked (compiler : Compiler) :
    (input compiler).check (file compiler) name = true := by
  cases compiler with
  | defaultGCC =>
    change check GCC.file GCC.table GCC.metadata name (function .defaultGCC)
      (bytes .defaultGCC) = true
    unfold check
    rw [GCC.metadataAccepted]
    unfold ELF.FunctionWindow.check
    have offset : (function .defaultGCC).window.offset = 11568 := rfl
    rw [GCC.layoutAccepted, offset, GCC.fileDropChunks 11568 (by decide +kernel)]
    simp only [GCC.fileLength]
    simp only [ELF.checkCode, X86.fetchByte, OS.AddressSpace.toMemory,
      ELF.install, ELF.segmentCell, GCC.fileByteChunks]
    decide +kernel
  | defaultClang =>
    change check Clang.file Clang.table Clang.metadata name (function .defaultClang)
      (bytes .defaultClang) = true
    unfold check
    rw [Clang.metadataAccepted]
    unfold ELF.FunctionWindow.check
    have offset : (function .defaultClang).window.offset = 4816 := rfl
    rw [Clang.layoutAccepted, offset, Clang.fileDropAt 4816 (by decide +kernel)]
    simp only [Clang.fileLength]
    simp only [ELF.checkCode, X86.fetchByte, OS.AddressSpace.toMemory,
      ELF.install, ELF.segmentCell, clangFileByte]
    decide +kernel

#print axioms body
#print axioms checked
end EDSL.Corpus.V1.ClampWindows
#audit_edsl
