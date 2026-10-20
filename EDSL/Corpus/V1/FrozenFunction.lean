/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.ArithmeticWindows

set_option autoImplicit false
set_option warningAsError true

/-! Reuse the authenticated full-file metadata for further frozen functions.
Selecting a row constructs untrusted hints; `FunctionInput.check` must still
authenticate its requested name, complete extent, mapping and actual bytes. -/

namespace EDSL.Corpus.V1.FrozenFunction
open X86 ELF.FunctionSymbol

abbrev Compiler := ArithmeticWindows.Compiler
abbrev file := ArithmeticWindows.file

def symbols : Compiler → Symbols
  | .defaultGCC => GCC.symbols27
  | .defaultClang => Clang.symbols26

def text : Compiler → Section
  | .defaultGCC => GCC.sh14
  | .defaultClang => Clang.sh13

/-- A bounded row in the shared static symbol table. The final checker rejects
nontext, nonfunction or wrongly named rows; row selection itself proves none
of those properties and supplies no semantic contract. -/
def function (compiler : Compiler) (index : Fin (symbols compiler).rows.length) : Function :=
  let symbol := (symbols compiler).rows[index]
  { occurrence := ⟨(symbols compiler).sectionIndex, index.val, symbol⟩
    sh := text compiler
    window := ⟨symbol.value, (text compiler).offset + (symbol.value - (text compiler).address)⟩ }

def input (compiler : Compiler) (index : Fin (symbols compiler).rows.length)
    (bytes : List Byte) : FunctionInput :=
  { ArithmeticWindows.input compiler with function := function compiler index, bytes := bytes }

/-- Shared bounded lookup normalization for the complete Clang literal.
Out-of-file offsets remain absent. This does not validate a selected window. -/
theorem clangFileByte (offset : Nat) :
    Clang.file[offset]? = if offset < 44240 then
      (((Clang.chunks.drop (offset / 128)).flatten).drop (offset % 128))[0]? else none := by
  by_cases inside : offset < 44240
  · rw [ite_eq_left inside]
    have dropped := congrArg (fun source : List Byte => source[0]?)
      (Clang.fileDropAt offset (by omega))
    simpa only [List.getElem?_drop, Nat.add_zero] using dropped
  · rw [ite_eq_right inside]
    exact List.getElem?_eq_none (by rw [Clang.fileLength]; omega)

#print axioms function
#print axioms input
#print axioms clangFileByte
end EDSL.Corpus.V1.FrozenFunction
#audit_edsl
