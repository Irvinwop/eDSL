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

def FunctionInput.check (input : FunctionInput) (file name : List Byte) : Bool :=
  FunctionSymbol.check file input.table input.metadata name input.function input.bytes

def FunctionInput.admit (input : FunctionInput) (file name : List Byte) (prior : Space) :
    Except Error Loaded :=
  FunctionSymbol.admit file input.table input.metadata name input.function input.bytes prior

end EDSL.ELF
