/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Examples.Compiler.IncrementLoop
import EDSL.Examples.Compiler.Increment
import EDSL.Audit

namespace EDSL.Tests.ControlFlow
open X86 Examples.Compiler

def memory : Memory where
  read address := if 4096 ≤ address.toNat ∧ address.toNat < 4106 then
    IncrementLoop.bytes[address.toNat - 4096]? else Increment.witnessMemory.read address
  executable address := decide (4096 ≤ address.toNat ∧ address.toNat < 4106)

def entry (value count : Word) : State :=
  { Increment.witnessEntry value with
    memory := memory
    registers := fun register => if register = .rdi then value else if register = .rcx then count
      else if register = .rsp then 32768 else 0xfaded000000000000
    flags := 0x8d7 }

theorem code : CodeAt memory 4096 IncrementLoop.bytes := by
  refine ⟨by decide, ?_⟩
  intro offset byte present
  match offset with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 =>
    simp [IncrementLoop.bytes] at present
    subst byte
    rfl
  | offset + 10 => simp [IncrementLoop.bytes] at present

/-- Satisfiable entry for every 64-bit value/count, rather than only a finite
test range or an assumed loop invariant. -/
theorem every_input_executes (value count : Word) :
    Executes (entry value count) (IncrementLoop.finalState (entry value count) 8192)
      (IncrementLoop.cost count.toNat) :=
  IncrementLoop.actual_bytes_correct (entry value count) 8192 code (by rfl) (by rfl)

def observe (value count : Word) (fuel : Nat) : Option (Word × Word × Word × Word × Word × Nat) := do
  let result ← (run fuel (entry value count)).toOption
  return (result.state.registers .rax, result.state.registers .rcx, result.state.rip,
    result.state.registers .rsp, result.state.flags, result.instructions)

example : observe 0xdeadbeefffffffff 0 3 = some (0xffffffff, 0, 8192, 32776, 0x8d7, 3) := by decide
example : observe 0xffffffff 1 5 = some (0, 0, 8192, 32776, 0x8d7, 5) := by decide
example : observe 0xfffffffe 3 9 = some (1, 0, 8192, 32776, 0x8d7, 9) := by decide
example : run 8 (entry 0 3) = .error .exhaustedFuel := by rfl

-- RCX is 64-bit; low32 zero must not select JRCXZ's exit edge.
example : run 3 (entry 0 0x100000000) = .error .exhaustedFuel := by rfl
-- A full-width decrement remains nonzero here. LOOP never tests/changes ZF.
example : (executeLoop { entry 0 0x100000001 with rip := 4103 } 0xfb).toOption.map
    (fun state => (state.registers .rcx, state.rip, state.flags)) =
    some (0x100000000, 4100, 0x8d7) := by decide
-- Without the entry guard, a zero counter wraps before testing.
example : (executeLoop { entry 0 0 with rip := 4103 } 0xfb).toOption.map
    (fun state => (state.registers .rcx, state.rip)) = some (0xffffffffffffffff, 4100) := by decide

example : (executeJrcxz (entry 0 0) 0xfc).toOption.map State.rip = some 4094 := by decide
example : executeJrcxz { entry 0 0 with rip := 0x7ffffffffffe } 1 =
    .error (.noncanonicalBranch 0x800000000001) := by rfl
example : (executeJrcxz { entry 0 1 with rip := 0x7ffffffffffe } 1).toOption.map State.rip =
    some 0x800000000000 := by decide

-- Address-size overrides are rejected, so this proof never silently uses ECX.
def prefixed : State := { entry 0 0 with memory := {
  read := fun address => if address = 4096 then some 0x67 else memory.read address
  executable := memory.executable } }
example : step prefixed = .error (.unsupportedOpcode 0x67) := by rfl

-- LEA's signed displacement affects only the low32 arithmetic result; writing
-- EAX must still clear the upper half even when the old RAX had high bits.
example : (executeLeaRax { entry 0 0 with registers := fun _ => 0xdeadbeef00000000 } 0xff).registers .rax =
    0xffffffff := by decide

def truncatedBranch : State := { entry 0 1 with memory := {
  read := fun address => if address = 4096 then some 0xe3 else none
  executable := fun _ => true } }
example : step truncatedBranch = .error (.inaccessibleInstruction 4097) := by rfl

end EDSL.Tests.ControlFlow

#audit_edsl
