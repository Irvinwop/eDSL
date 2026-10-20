/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.Certificate
import EDSL.Corpus.V1.GCC
import EDSL.Corpus.V1.Clang
import EDSL.X86.VCGen.CompilerComparisons

/-!
Exact complete named windows from the two ordinary frozen compiler files.
This data adapter checks file, symbol, extent and executable image bytes only.
Mathematical behavior and current-resource admission require separate proofs.
-/

namespace EDSL.Corpus.V1.ArithmeticWindows
open X86 ELF.FunctionSymbol

abbrev Compiler := X86.VCGen.CompilerComparisons.Compiler

def file : Compiler → List Byte
  | .defaultGCC => GCC.file
  | .defaultClang => Clang.file

/-- The exact ELF byte name `c_add_mod64`, without its terminating NUL. -/
def name : List Byte := [99,95,97,100,100,95,109,111,100,54,52]

/-- Complete symbol extents, retaining GCC's original ENDBR64. -/
def bytes : Compiler → List Byte
  | .defaultGCC => [0xf3,0x0f,0x1e,0xfa,0x48,0x8d,0x04,0x37,0xc3]
  | .defaultClang => [0x48,0x8d,0x04,0x37,0xc3]

/-- Untrusted row/section/window hints, validated by `checked` against the
complete shared literal file and all of its symbol tables. -/
def function : Compiler → Function
  | .defaultGCC => {
      occurrence := { table := 27, index := 131, symbol := {
        nameOffset := 2010, info := 18, other := 0, sh := 14, value := 4205984, size := 9 } }
      sh := GCC.sh14
      window := { address := 4205984, offset := 11680 } }
  | .defaultClang => {
      occurrence := { table := 26, index := 108, symbol := {
        nameOffset := 1777, info := 18, other := 0, sh := 13, value := 4199200, size := 5 } }
      sh := Clang.sh13
      window := { address := 4199200, offset := 4896 } }

/-- Each compiler's functions reuse its complete file, program table and
metadata; adding a window does not duplicate the file or metadata validation. -/
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
    have offset : (function .defaultGCC).window.offset = 11680 := rfl
    rw [GCC.layoutAccepted, offset, GCC.fileDropChunks 11680 (by decide +kernel)]
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
    have offset : (function .defaultClang).window.offset = 4896 := rfl
    rw [Clang.layoutAccepted, offset, Clang.fileDropAt 4896 (by decide +kernel)]
    simp only [Clang.fileLength]
    simp only [ELF.checkCode, X86.fetchByte, OS.AddressSpace.toMemory,
      ELF.install, ELF.segmentCell, clangFileByte]
    decide +kernel

#print axioms body
#print axioms checked
end EDSL.Corpus.V1.ArithmeticWindows
#audit_edsl
