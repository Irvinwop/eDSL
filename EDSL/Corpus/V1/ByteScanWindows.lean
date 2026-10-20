/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.ArithmeticWindows

set_option autoImplicit false
set_option warningAsError true

/-! Complete named `c_strnlen_bytes` windows in the unchanged frozen files.
These checks authenticate file metadata and executable bytes, not behavior. -/

namespace EDSL.Corpus.V1.ByteScanWindows
open X86 ELF.FunctionSymbol

abbrev Compiler := ArithmeticWindows.Compiler
def file : Compiler → List Byte := ArithmeticWindows.file
def name : List Byte := [99,95,115,116,114,110,108,101,110,95,98,121,116,101,115]

/-- Whole symbol extents, including GCC ENDBR64 and Clang's nine-byte NOP. -/
def bytes : Compiler → List Byte
  | .defaultGCC => [0xf3,0x0f,0x1e,0xfa,0x48,0x89,0xf0,0x31,0xd2,0x48,0x85,0xf6,
      0x75,0x0b,0xc3,0x90,0x48,0x83,0xc2,0x01,0x48,0x39,0xd0,0x74,0x09,
      0x80,0x3c,0x17,0x00,0x75,0xf1,0x48,0x89,0xd0,0xc3]
  | .defaultClang => [0x31,0xc0,0x48,0x85,0xf6,0x74,0x1a,
      0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00,
      0x80,0x3c,0x07,0x00,0x74,0x0b,0x48,0xff,0xc0,0x48,0x39,0xc6,0x75,0xf2,
      0x48,0x89,0xf0,0xc3]

/-- Native extraction supplies only untrusted hints; `checked` authenticates
the unique name, exact STT_FUNC row, full extent and mapping. -/
def function : Compiler → Function
  | .defaultGCC => {
      occurrence := { table := 27, index := 123, symbol := {
        nameOffset := 1867, info := 18, other := 0, sh := 14, value := 4206432, size := 35 } }
      sh := GCC.sh14
      window := { address := 4206432, offset := 12128 } }
  | .defaultClang => {
      occurrence := { table := 26, index := 100, symbol := {
        nameOffset := 1634, info := 18, other := 0, sh := 13, value := 4199584, size := 34 } }
      sh := Clang.sh13
      window := { address := 4199584, offset := 5280 } }

def kernelFunctionInput (compiler : Compiler) : FunctionInput := {
  ArithmeticWindows.input compiler with
  function := function compiler
  bytes := bytes compiler }

abbrev input := kernelFunctionInput

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

/-- Kernel authentication against the complete shared literal ELFs. Shared
metadata/layout and chunk-index theorems avoid copying or rechecking a file. -/
theorem checked (compiler : Compiler) :
    (kernelFunctionInput compiler).check (file compiler) name = true := by
  cases compiler with
  | defaultGCC =>
    change check GCC.file GCC.table GCC.metadata name (function .defaultGCC)
      (bytes .defaultGCC) = true
    unfold check
    rw [GCC.metadataAccepted]
    unfold ELF.FunctionWindow.check
    have offset : (function .defaultGCC).window.offset = 12128 := rfl
    rw [GCC.layoutAccepted, offset, GCC.fileDropChunks 12128 (by decide +kernel)]
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
    have offset : (function .defaultClang).window.offset = 5280 := rfl
    rw [Clang.layoutAccepted, offset, Clang.fileDropAt 5280 (by decide +kernel)]
    simp only [Clang.fileLength]
    simp only [ELF.checkCode, X86.fetchByte, OS.AddressSpace.toMemory,
      ELF.install, ELF.segmentCell, clangFileByte]
    decide +kernel

#print axioms body
#print axioms checked
end EDSL.Corpus.V1.ByteScanWindows
#audit_edsl
