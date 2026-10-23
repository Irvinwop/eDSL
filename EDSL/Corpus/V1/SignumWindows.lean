/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.SignumCode
import EDSL.Corpus.V1.FrozenFunction

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-! Complete unchanged `c_sign_i32` windows in the frozen GCC/Clang ELF files.
Row indices supply untrusted selection hints; the production checker binds
them to the shared full-file metadata, exact extent and executable bytes. -/

namespace EDSL.Corpus.V1.SignumWindows
open X86 ELF.FunctionSymbol

abbrev Compiler := SignumCode.Compiler
abbrev bytes := SignumCode.bytes
abbrev spec := SignumCode.spec
abbrev file := FrozenFunction.file

/-- The complete requested ELF byte name, without its terminating NUL. -/
def name : List Byte := [99,95,115,105,103,110,95,105,51,50]

/-- Untrusted static symbol-table row hints from the frozen files.
GCC: address 4205952, offset 11648, size 17; Clang: 4199184, 4880, size 15.
The checked function input below must authenticate every selected property. -/
def symbolIndex : (compiler : Compiler) → Fin (FrozenFunction.symbols compiler).rows.length
  | .defaultGCC => ⟨74, by decide +kernel⟩
  | .defaultClang => ⟨50, by decide +kernel⟩

def function (compiler : Compiler) : Function :=
  FrozenFunction.function compiler (symbolIndex compiler)

def input (compiler : Compiler) : FunctionInput :=
  FrozenFunction.input compiler (symbolIndex compiler) (bytes compiler)

/-- Authenticate the complete file, unique exact name, whole declared symbol
extent and executable LOAD mapping through the shared metadata/layout proofs.
GCC's original ENDBR64 stays in its full extent. File binding alone supplies
no execution, functional-correctness or current-resource admission claim. -/
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

#print axioms checked
end EDSL.Corpus.V1.SignumWindows
#audit_edsl
