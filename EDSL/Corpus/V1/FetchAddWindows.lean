/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.ArithmeticWindows

/-!
Exact complete `c_atomic_fetch_add64` named windows from the two frozen files.
This data adapter checks file, symbol, extent and executable image bytes only.
It supplies no mathematical, OS, synchronization, resource-admission or score
claim, and does not certify frozen concurrent execution.
-/

namespace EDSL.Corpus.V1.FetchAddWindows
open X86 ELF.FunctionSymbol

abbrev Compiler := X86.VCGen.CompilerComparisons.Compiler

/-- Reuse the complete shared frozen files. -/
def file : Compiler → List Byte := ArithmeticWindows.file

/-- The exact ASCII ELF name `c_atomic_fetch_add64`, without its terminating NUL. -/
def name : List Byte := [99,95,97,116,111,109,105,99,95,102,101,116,99,104,95,97,100,100,54,52]

/-- Complete symbol extents, retaining GCC's original ENDBR64. -/
def bytes : Compiler → List Byte
  | .defaultGCC => [0xf3,0x0f,0x1e,0xfa,0x48,0x89,0xf0,0xf0,0x48,0x0f,0xc1,0x07,0xc3]
  | .defaultClang => [0x48,0x89,0xf0,0xf0,0x48,0x0f,0xc1,0x07,0xc3]

/-- Untrusted hints from the actual frozen ELF rows and linked string tables.
`checked` authenticates them against the complete shared literal files and all
their symbol tables, including uniqueness of the requested name. -/
def function : Compiler → Function
  | .defaultGCC => {
      occurrence := { table := 27, index := 78, symbol := {
        nameOffset := 1156, info := 18, other := 0, sh := 14, value := 4207232, size := 13 } }
      sh := GCC.sh14
      window := { address := 4207232, offset := 12928 } }
  | .defaultClang => {
      occurrence := { table := 26, index := 54, symbol := {
        nameOffset := 913, info := 18, other := 0, sh := 13, value := 4201136, size := 9 } }
      sh := Clang.sh13
      window := { address := 4201136, offset := 6832 } }

/-- Reuse the shared program table and metadata, replacing only the selected
function and its complete bytes. -/
def input (compiler : Compiler) : FunctionInput := {
  ArithmeticWindows.input compiler with
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

/-- Exact unique global FUNC identity, entire declared extent, address, file
offset and executable image bytes under the existing bounded ELF profile.
Shared metadata/layout proofs are reused; no behavior is inferred from them. -/
theorem checked (compiler : Compiler) :
    (input compiler).check (file compiler) name = true := by
  cases compiler with
  | defaultGCC =>
    change check GCC.file GCC.table GCC.metadata name (function .defaultGCC)
      (bytes .defaultGCC) = true
    unfold check
    rw [GCC.metadataAccepted]
    unfold ELF.FunctionWindow.check
    have offset : (function .defaultGCC).window.offset = 12928 := rfl
    rw [GCC.layoutAccepted, offset, GCC.fileDropChunks 12928 (by decide +kernel)]
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
    have offset : (function .defaultClang).window.offset = 6832 := rfl
    rw [Clang.layoutAccepted, offset, Clang.fileDropAt 6832 (by decide +kernel)]
    simp only [Clang.fileLength]
    simp only [ELF.checkCode, X86.fetchByte, OS.AddressSpace.toMemory,
      ELF.install, ELF.segmentCell, clangFileByte]
    decide +kernel

#print axioms body
#print axioms checked
end EDSL.Corpus.V1.FetchAddWindows
#audit_edsl
