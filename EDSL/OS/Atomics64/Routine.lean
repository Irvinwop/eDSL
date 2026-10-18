/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Atomics64.Machine
import EDSL.X86.LockedLogical64.Execution
import EDSL.X86.Buffer
import EDSL.Logical64.Algebra

namespace EDSL.OS.Atomics64
open X86 AddressSpace

namespace Routine
open X86.LockedLogical64

/-- Discarded-result full64 OR; no old-word return in RAX. -/
def bytes : List Byte := [0xf0, 0x48, 0x09, 0x37, 0xc3]

def returned (initial : X86.State) (returnAddress : Word) : X86.State :=
  { initial.writeRegister .rsp (initial.registers .rsp + 8) with rip := returnAddress }

def result (initial : X86.State) (after : Atomics64.State) (event : Event)
    (af : Bool) (returnAddress : Word) : Result :=
  ⟨returned (afterOr initial (toMemory after.legacy.shared.resources.space)
      event.logical.event.after af) returnAddress,
    2, [event.logical], [.rmw8 (initial.registers .rdi), .stack8 (initial.registers .rsp)]⟩

theorem first_code {memory : Memory} {base : Word} (code : CodeAt memory base bytes) :
    CodeAt memory base Instruction.orRdiRsi.bytes := by
  refine ⟨by
    change base.toNat + 4 ≤ 2^64
    have bound := code.1
    change base.toNat + 5 ≤ 2^64 at bound
    omega, ?_⟩
  intro offset byte present
  apply code.2 offset byte
  match offset with
  | 0 | 1 | 2 | 3 => simpa [Instruction.bytes, bytes] using present
  | offset + 4 => simp [Instruction.bytes] at present

theorem return_code {memory : Memory} {base : Word} (code : CodeAt memory base bytes) :
    CodeAt memory (base + 4) Instruction.ret.bytes := by
  apply code.window 4
  · decide
  · have bound := code.1
    change base.toNat + 5 ≤ 2^64 at bound
    omega
  · intro index byte present
    match index with
    | 0 => simpa [Instruction.bytes, bytes] using present
    | index + 1 => simp [Instruction.bytes] at present

/-- The exact five bytes execute two actual instructions, emitting exactly
the checked OS event. Every AF stream is admitted; code and the actual current
caller slot must be disjoint from the complete eight-byte target. -/
theorem execution (state : Atomics64.State) (actor : Nat) (identifier : HandleId64)
    (changed : Atomics64.State × Event) (handle : Handle) (cell : Atomics64.Cell)
    (initial : X86.State) (choices : Choices) (returnAddress : Word)
    (success : logicalDiscard state actor identifier (initial.registers .rsi) = .ok changed)
    (authorized : authorize state actor identifier = .ok (handle, cell))
    (memory : initial.memory = toMemory state.legacy.shared.resources.space)
    (operand : initial.registers .rdi = cell.address)
    (code : CodeAt initial.memory initial.rip bytes)
    (codeDisjoint : QWordDisjoint cell.address initial.rip bytes.length)
    (stackDisjoint : QWordDisjoint cell.address (initial.registers .rsp) 8)
    (stack : readWord initial.memory (initial.registers .rsp) = .ok returnAddress)
    (returnValid : canonical returnAddress = true) :
    Executes choices initial (result initial changed.1 changed.2 (choices 0) returnAddress) := by
  have decoded := decodeAt_of_code .orRdiRsi (first_code code)
  have first := logicalDiscard_step _ _ _ _ _ _ _ _ (choices 0) success authorized
    memory operand rfl decoded
  let middle := afterOr initial (toMemory changed.1.legacy.shared.resources.space)
    changed.2.logical.event.after (choices 0)
  have effect : OrEffect initial (choices 0) changed.2.logical middle :=
    (step_atomic64_sound first).2.1
  have atCell := (logicalDiscard_identity _ _ _ _ _ _ _ success authorized).2
  have preserved := effect.preserves_code initial.rip bytes code (by rwa [atCell])
  have retCode : CodeAt middle.memory middle.rip Instruction.ret.bytes := return_code preserved
  have stackAfter : readWord middle.memory (middle.registers .rsp) = .ok returnAddress := by
    change readWord middle.memory (initial.registers .rsp) = .ok returnAddress
    exact (effect.stack_frame (initial.registers .rsp) (by rwa [atCell])).trans stack
  have second : step ((choices.drop 1) 0) middle =
      .ok ⟨.returned (returned middle returnAddress), [.stack8 (initial.registers .rsp)]⟩ := by
    rw [step_eq_execute _ (decodeAt_of_code .ret retCode)]
    exact execute_ret_context middle returnAddress _ stackAfter returnValid
  have actual := Executes.atomic64 first (Executes.ret second)
  simpa [result, Result.prepend, middle, operand] using actual

/-- Current ownership/epoch/permissions/actor authority derive successful OS
execution for every mask and every AF stream. No future-success premise is
required. Native interpretation additionally retains the physical and lifetime
assumptions documented by the locked profile. -/
theorem enabled (state : Atomics64.State) (actor : Nat) (identifier : HandleId64)
    (handle : Handle) (cell : Atomics64.Cell) (initial : X86.State)
    (choices : Choices) (returnAddress : Word) (valid : WellFormed state)
    (authorized : authorize state actor identifier = .ok (handle, cell))
    (memory : initial.memory = toMemory state.legacy.shared.resources.space)
    (operand : initial.registers .rdi = cell.address)
    (code : CodeAt initial.memory initial.rip bytes)
    (codeDisjoint : QWordDisjoint cell.address initial.rip bytes.length)
    (stackDisjoint : QWordDisjoint cell.address (initial.registers .rsp) 8)
    (stack : readWord initial.memory (initial.registers .rsp) = .ok returnAddress)
    (returnValid : canonical returnAddress = true) :
    ∃ changed, logicalDiscard state actor identifier (initial.registers .rsi) = .ok changed ∧
      Executes choices initial (result initial changed.1 changed.2 (choices 0) returnAddress) := by
  obtain ⟨changed, success⟩ := logicalDiscard_enabled _ _ _ _ _ _ valid authorized
  exact ⟨changed, success, execution _ _ _ _ _ _ _ _ _ success authorized memory operand
    code codeDisjoint stackDisjoint stack returnValid⟩

/-- Independent per-bit union contract on the actual result, including bit63.
This value theorem is separate from execution and resource/lifetime authority. -/
theorem mathematical (state : Atomics64.State) (actor : Nat) (identifier : HandleId64)
    (mask : Word) (changed : Atomics64.State × Event)
    (success : logicalDiscard state actor identifier mask = .ok changed) :
    Logical64.MathematicalResult .union changed.2.logical.event.before mask
      changed.2.logical.event.after := by
  have value := (logicalDiscard_sound _ _ _ _ _ success).2.2.2.1
  rw [value]
  exact Logical64.eval_mathematical .union _ _

/-- A callable all-choice contract: one actual full64 event, two retired
instructions, full pointer/register return behavior and the independent union
result in current RAM. This routine discards its result at the ABI boundary.
Code/stack ownership and managed scheduling are established separately. -/
theorem correct (state : Atomics64.State) (actor : Nat) (identifier : HandleId64)
    (handle : Handle) (cell : Atomics64.Cell) (initial : X86.State)
    (returnAddress : Word) (valid : WellFormed state)
    (authorized : authorize state actor identifier = .ok (handle, cell))
    (memory : initial.memory = toMemory state.legacy.shared.resources.space)
    (operand : initial.registers .rdi = cell.address)
    (code : CodeAt initial.memory initial.rip bytes)
    (codeDisjoint : QWordDisjoint cell.address initial.rip bytes.length)
    (stackDisjoint : QWordDisjoint cell.address (initial.registers .rsp) 8)
    (stack : readWord initial.memory (initial.registers .rsp) = .ok returnAddress)
    (returnValid : canonical returnAddress = true) :
    AllExecutions initial (fun output =>
      ∃ changed, logicalDiscard state actor identifier (initial.registers .rsi) = .ok changed ∧
        output.instructions = 2 ∧ output.events = [changed.2.logical] ∧
        output.accesses = [.rmw8 cell.address, .stack8 (initial.registers .rsp)] ∧
        output.state.memory = toMemory changed.1.legacy.shared.resources.space ∧
        output.state.rip = returnAddress ∧
        output.state.registers .rsp = initial.registers .rsp + 8 ∧
        (∀ register, register ≠ .rsp →
          output.state.registers register = initial.registers register) ∧
        loadQWord output.state.memory cell.address = .ok changed.2.logical.event.after ∧
        Logical64.MathematicalResult .union changed.2.logical.event.before
          (initial.registers .rsi) changed.2.logical.event.after) := by
  intro choices
  obtain ⟨changed, success, actual⟩ := enabled state actor identifier handle cell initial
    choices returnAddress valid authorized memory operand code codeDisjoint stackDisjoint stack returnValid
  refine ⟨_, actual, changed, success, rfl, rfl, ?_, rfl, rfl, ?_, ?_, ?_,
    mathematical _ _ _ _ _ success⟩
  · simp only [result, operand]
  · simp [result, returned, afterOr, X86.State.writeRegister]
  · intro register other
    simp [result, returned, afterOr, X86.State.writeRegister, other]
  · have readback := (logicalDiscard_sound _ _ _ _ _ success).1.readback
    rw [(logicalDiscard_identity _ _ _ _ _ _ _ success authorized).2] at readback
    exact readback

end Routine
end EDSL.OS.Atomics64
