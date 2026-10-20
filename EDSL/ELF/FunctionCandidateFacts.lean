/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.ELF.FunctionInput

namespace EDSL.ELF.FunctionCandidate
open X86

/-- The production checker conclusion, parameterized before closed literals are
substituted. Generated proofs need no candidate parser or source emitter. -/
def Binding (input : FunctionInput) (file name : List Byte) (maxBytes : Nat := 64) : Prop :=
  FunctionSymbol.CheckedMetadata file input.table.header input.metadata ∧
  input.function.Contract input.metadata name input.bytes.length ∧
  FunctionWindow.Layout file input.table ∧
  FunctionWindow.Selection file input.table.image input.function.window input.bytes maxBytes

theorem checked_bindingWith (maxBytes : Nat) (input : FunctionInput) (file name : List Byte)
    (checked : input.checkWith maxBytes file name = true) : Binding input file name maxBytes :=
  FunctionSymbol.checked_soundWith checked

theorem checked_codeWith (maxBytes : Nat) (input : FunctionInput) (file name : List Byte)
    (checked : input.checkWith maxBytes file name = true) (prior : OS.AddressSpace.Space) :
    CodeAt (OS.AddressSpace.toMemory (ELF.install file input.table.image prior))
      input.function.window.base input.bytes :=
  FunctionWindow.checked_codeWith (Bool.and_eq_true_iff.mp checked).2 prior

theorem checked_binding (input : FunctionInput) (file name : List Byte)
    (checked : input.check file name = true) : Binding input file name :=
  checked_bindingWith 64 input file name checked

theorem checked_code (input : FunctionInput) (file name : List Byte)
    (checked : input.check file name = true) (prior : OS.AddressSpace.Space) :
    CodeAt (OS.AddressSpace.toMemory (ELF.install file input.table.image prior))
      input.function.window.base input.bytes :=
  checked_codeWith 64 input file name checked prior

end EDSL.ELF.FunctionCandidate
