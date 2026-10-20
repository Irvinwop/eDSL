/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.ELF.FunctionSymbol

namespace EDSL.ELF
open X86 OS.AddressSpace

/-- Untrusted data for a named complete ELF function. The complete file and
requested name remain external parameters of the checker and admission. -/
structure FunctionInput where
  table : FunctionWindow.Table
  metadata : FunctionSymbol.Metadata
  function : FunctionSymbol.Function
  bytes : List Byte

def FunctionInput.checkWith (maxBytes : Nat) (input : FunctionInput) (file name : List Byte) : Bool :=
  FunctionSymbol.checkWith maxBytes file input.table input.metadata name input.function input.bytes

/-- Keep the default named checker at the public definition head. Literal-file
clients can unfold it without comparing default and explicit-bound checkers
over a complete closed ELF. The explicit variant remains opt-in. -/
def FunctionInput.check (input : FunctionInput) (file name : List Byte) : Bool :=
  FunctionSymbol.check file input.table input.metadata name input.function input.bytes

/-- Convert default input checks without elaborating closed file literals while
unifying the two transparent checker wrappers. The equality is proved once on
arbitrary inputs; it changes neither admission nor the selected byte bound. -/
theorem FunctionInput.check_eq_symbol (input : FunctionInput) (file name : List Byte) :
    input.check file name =
      FunctionSymbol.check file input.table input.metadata name input.function input.bytes := rfl

def FunctionInput.admitWith (maxBytes : Nat) (input : FunctionInput) (file name : List Byte)
    (prior : Space) : Except Error Loaded :=
  FunctionSymbol.admitWith maxBytes file input.table input.metadata name input.function input.bytes prior

def FunctionInput.admit (input : FunctionInput) (file name : List Byte) (prior : Space) :
    Except Error Loaded :=
  FunctionSymbol.admit file input.table input.metadata name input.function input.bytes prior

end EDSL.ELF
