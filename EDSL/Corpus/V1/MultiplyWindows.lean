/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.MultiplyCode
import EDSL.Corpus.V1.FrozenFunction

set_option autoImplicit false
set_option warningAsError true

/-! Complete unchanged `c_mul_mod64` windows in the frozen GCC/Clang ELF files.
Row selection supplies hints; the production checker authenticates them against
the shared full-file metadata, declared extent and executable mapping. -/

namespace EDSL.Corpus.V1.MultiplyWindows
open X86 ELF.FunctionSymbol

abbrev Compiler := MultiplyCode.Compiler
abbrev bytes := MultiplyCode.bytes
abbrev spec := MultiplyCode.spec
abbrev file := FrozenFunction.file

/-- The complete requested ELF byte name, without its terminating NUL. -/
def name : List Byte := [99,95,109,117,108,95,109,111,100,54,52]

/-- Static symbol-table row indices from the existing frozen Lean rows and
read-only ELF inspection. These indices are untrusted selection hints.
GCC: address 4206000, offset 11696, size 12; Clang: 4199216, 4912, size 8. -/
def symbolIndex : (compiler : Compiler) → Fin (FrozenFunction.symbols compiler).rows.length
  | .defaultGCC => ⟨114, by decide +kernel⟩
  | .defaultClang => ⟨91, by decide +kernel⟩

def function (compiler : Compiler) : Function :=
  FrozenFunction.function compiler (symbolIndex compiler)

def input (compiler : Compiler) : FunctionInput :=
  FrozenFunction.input compiler (symbolIndex compiler) (bytes compiler)

/-- Authenticate the unchanged complete file, unique exact name, full declared
symbol extent and executable LOAD bytes using shared metadata/layout proofs.
GCC's original ENDBR64 remains in the extent. This binds an artifact; it supplies
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
end EDSL.Corpus.V1.MultiplyWindows
#audit_edsl
