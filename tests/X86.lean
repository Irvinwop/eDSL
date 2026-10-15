/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL

namespace EDSL.Tests
open X86 Examples.Compiler.Increment

/-- Catches zero-extending an 8-bit negative LEA displacement. -/
theorem signed_displacement (input : Word) :
    ((executeLea (witnessEntry input) 0xff).registers .rax) =
      ((input.setWidth 32) - 1).setWidth 64 := by
  simp only [executeLea, State.writeRegister, witnessEntry]
  bv_decide

def noExecute : State :=
  { witnessEntry 0 with memory := { witnessMemory with executable := fun _ => false } }

example : run 2 noExecute = .error (.inaccessibleInstruction 4096) := by rfl

def noStack : State :=
  { witnessEntry 0 with memory := { witnessMemory with read := fun address =>
      if address = 32768 then none else witnessMemory.read address } }

example : run 2 noStack = .error (.inaccessibleStack 32768) := by rfl

def badReturnMemory : Memory where
  read address :=
    match address.toNat with
    | 32769 => some 0
    | 32773 => some 0x80
    | _ => witnessMemory.read address
  executable := witnessMemory.executable

def badReturn : State := { witnessEntry 0 with memory := badReturnMemory }

example : run 2 badReturn = .error (.noncanonicalReturn 0x800000000000) := by rfl

example : run 1 (witnessEntry 0) = .error .exhaustedFuel := by rfl

end EDSL.Tests

#audit_edsl
