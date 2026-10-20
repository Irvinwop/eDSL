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

/-- Transparent default wrapper keeps generated default proofs directly usable
by existing input/caller interfaces without normalizing a closed ELF checker. -/
abbrev FunctionInput.check (input : FunctionInput) (file name : List Byte) : Bool :=
  input.checkWith 64 file name

def FunctionInput.admitWith (maxBytes : Nat) (input : FunctionInput) (file name : List Byte)
    (prior : Space) : Except Error Loaded :=
  FunctionSymbol.admitWith maxBytes file input.table input.metadata name input.function input.bytes prior

def FunctionInput.admit (input : FunctionInput) (file name : List Byte) (prior : Space) :
    Except Error Loaded :=
  FunctionSymbol.admit file input.table input.metadata name input.function input.bytes prior

end EDSL.ELF
