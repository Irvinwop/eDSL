/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.AverageCode
import EDSL.Corpus.V1.FrozenFunction

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Corpus.V1.AverageWindows
open X86 ELF.FunctionSymbol

abbrev Compiler := AverageCode.Compiler
abbrev bytes := AverageCode.bytes
abbrev file := FrozenFunction.file

/-- The complete requested ELF symbol name, without its terminating NUL. -/
def name : List Byte := [99,95,97,118,101,114,97,103,101,95,117,54,52]

def symbolIndex : (compiler : Compiler) → Fin (FrozenFunction.symbols compiler).rows.length
  | .defaultGCC => ⟨71, by decide +kernel⟩
  | .defaultClang => ⟨47, by decide +kernel⟩

def function (compiler : Compiler) : Function :=
  FrozenFunction.function compiler (symbolIndex compiler)

def input (compiler : Compiler) : FunctionInput :=
  FrozenFunction.input compiler (symbolIndex compiler) (bytes compiler)

/-- Authenticate the complete unchanged file, exact function name, full symbol
extent and executable mapping together. The selected function is distinct from
the ELF entry point. This theorem supplies artifact binding, not behavior. -/
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
end EDSL.Corpus.V1.AverageWindows
#audit_edsl
