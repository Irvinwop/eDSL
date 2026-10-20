/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.UnaryCode
import EDSL.Corpus.V1.FrozenFunction

set_option autoImplicit false
set_option warningAsError true

/-! Complete unchanged abs/byte-reversal windows in the frozen ELF files.
File identity is independent of the functional body proofs. Row selection is
untrusted until the production checker authenticates the whole named extent. -/

namespace EDSL.Corpus.V1.UnaryWindows
open X86 ELF.FunctionSymbol

abbrev Compiler := UnaryCode.Compiler
abbrev Operation := UnaryCode.Operation
abbrev bytes := UnaryCode.bytes
abbrev spec := UnaryCode.spec
abbrev file := FrozenFunction.file

/-- Exact non-NUL ELF names from the immutable corpus manifest. -/
def name : Operation → List Byte
  | .absSigned32 => [99,95,97,98,115,95,105,51,50]
  | .byteSwap64 => [99,95,98,121,116,101,115,119,97,112,54,52]

def symbolIndex (compiler : Compiler) (operation : Operation) :
    Fin (FrozenFunction.symbols compiler).rows.length :=
  match compiler, operation with
  | .defaultGCC, .absSigned32 => ⟨103, by decide +kernel⟩
  | .defaultGCC, .byteSwap64 => ⟨139, by decide +kernel⟩
  | .defaultClang, .absSigned32 => ⟨79, by decide +kernel⟩
  | .defaultClang, .byteSwap64 => ⟨115, by decide +kernel⟩

def function (compiler : Compiler) (operation : Operation) : Function :=
  FrozenFunction.function compiler (symbolIndex compiler operation)

def input (compiler : Compiler) (operation : Operation) : FunctionInput :=
  FrozenFunction.input compiler (symbolIndex compiler operation) (bytes compiler operation)

theorem body (compiler : Compiler) (operation : Operation) :
    (input compiler operation).bytes = bytes compiler operation := rfl

/-- All four complete files/names/extents, including GCC's original ENDBR64,
are checked against shared authenticated metadata and executable LOAD bytes.
No extractor output or execution/result premise authenticates this binding. -/
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

#print axioms checked
end EDSL.Corpus.V1.UnaryWindows
#audit_edsl
