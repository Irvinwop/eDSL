/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Atomics64.LogicalMachine
import EDSL.X86.LockedSet64.Execution
import EDSL.Logical64.Algebra

namespace EDSL.OS.Atomics64.LogicalRoutine
open X86 AddressSpace X86.LockedSet64

/-- Exact locked AND/OR/XOR plus RET. The result is discarded at the ABI boundary. -/
def bytes (op : Sequential.LogicalOp) : List Byte :=
  [0xf0, 0x48, logicalOpcode op, 0x37, 0xc3]

def returned (initial : X86.State) (returnAddress : Word) : X86.State :=
  { initial.writeRegister .rsp (initial.registers .rsp + 8) with rip := returnAddress }

def result (initial : X86.State) (after : Atomics64.State) (event : Event)
    (af : Bool) (returnAddress : Word) : Result :=
  ⟨returned (afterLogical initial (toMemory after.legacy.shared.resources.space)
      event.logical.event.after af) returnAddress,
    2, [event.logical], [.rmw8 (initial.registers .rdi), .stack8 (initial.registers .rsp)]⟩

theorem first_code (op : Sequential.LogicalOp) {memory : Memory} {base : Word}
    (code : CodeAt memory base (bytes op)) :
    CodeAt memory base (Instruction.logicalRdiRsi op).bytes := by
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

theorem return_code (op : Sequential.LogicalOp) {memory : Memory} {base : Word}
    (code : CodeAt memory base (bytes op)) :
    CodeAt memory (base + 4) Instruction.ret.bytes := by
  apply code.window 4
  · simp [bytes, Instruction.bytes]
  · have bound := code.1
    change base.toNat + 5 ≤ 2^64 at bound
    omega
  · intro index byte present
    match index with
    | 0 => simpa [Instruction.bytes, bytes] using present
    | index + 1 => simp [Instruction.bytes] at present

/-- Actual checked CPU execution of the exact five bytes, for every AF stream.
The current code and caller slot are framed across the entire eight-byte RMW. -/
theorem execution (op : Sequential.LogicalOp) (state : Atomics64.State) (actor : Nat)
    (identifier : HandleId64) (changed : Atomics64.State × Event) (handle : Handle)
    (cell : Atomics64.Cell) (initial : X86.State) (choices : Choices) (returnAddress : Word)
    (success : logicalUpdate op state actor identifier (initial.registers .rsi) = .ok changed)
    (authorized : authorize state actor identifier = .ok (handle, cell))
    (memory : initial.memory = toMemory state.legacy.shared.resources.space)
    (operand : initial.registers .rdi = cell.address)
    (code : CodeAt initial.memory initial.rip (bytes op))
    (codeDisjoint : QWordDisjoint cell.address initial.rip (bytes op).length)
    (stackDisjoint : QWordDisjoint cell.address (initial.registers .rsp) 8)
    (stack : readWord initial.memory (initial.registers .rsp) = .ok returnAddress)
    (returnValid : canonical returnAddress = true) :
    Executes choices initial (result initial changed.1 changed.2 (choices 0) returnAddress) := by
  have decoded := decodeAt_of_code (.logicalRdiRsi op) (first_code op code)
  have first := logicalUpdate_step op _ _ _ _ _ _ _ _ (choices 0) success authorized
    memory operand rfl decoded
  let middle := afterLogical initial (toMemory changed.1.legacy.shared.resources.space)
    changed.2.logical.event.after (choices 0)
  have effect : LogicalEffect op initial (choices 0) changed.2.logical middle := by
    obtain ⟨actualOp, _, actualEffect, _⟩ := step_atomic64_sound first
    have selected : actualOp = op := actualEffect.op.symm.trans
      ((logicalUpdate_sound op _ _ _ _ _ success).2.1)
    subst actualOp
    exact actualEffect
  have atCell := (logicalUpdate_identity op _ _ _ _ _ _ _ success authorized).2
  have preserved := effect.preserves_code initial.rip (bytes op) code (by rwa [atCell])
  have retCode : CodeAt middle.memory middle.rip Instruction.ret.bytes := return_code op preserved
  have stackAfter : readWord middle.memory (middle.registers .rsp) = .ok returnAddress := by
    change readWord middle.memory (initial.registers .rsp) = .ok returnAddress
    exact (effect.stack_frame (initial.registers .rsp) (by rwa [atCell])).trans stack
  have second : step ((choices.drop 1) 0) middle =
      .ok ⟨.returned (returned middle returnAddress), [.stack8 (initial.registers .rsp)]⟩ := by
    rw [step_eq_execute _ (decodeAt_of_code .ret retCode)]
    exact execute_ret_context middle returnAddress _ stackAfter returnValid
  have actual := Executes.atomic64 first (Executes.ret second)
  simpa [result, Result.prepend, middle, operand] using actual

theorem enabled (op : Sequential.LogicalOp) (state : Atomics64.State) (actor : Nat)
    (identifier : HandleId64) (handle : Handle) (cell : Atomics64.Cell) (initial : X86.State)
    (choices : Choices) (returnAddress : Word) (valid : WellFormed state)
    (authorized : authorize state actor identifier = .ok (handle, cell))
    (memory : initial.memory = toMemory state.legacy.shared.resources.space)
    (operand : initial.registers .rdi = cell.address)
    (code : CodeAt initial.memory initial.rip (bytes op))
    (codeDisjoint : QWordDisjoint cell.address initial.rip (bytes op).length)
    (stackDisjoint : QWordDisjoint cell.address (initial.registers .rsp) 8)
    (stack : readWord initial.memory (initial.registers .rsp) = .ok returnAddress)
    (returnValid : canonical returnAddress = true) :
    ∃ changed, logicalUpdate op state actor identifier (initial.registers .rsi) = .ok changed ∧
      Executes choices initial (result initial changed.1 changed.2 (choices 0) returnAddress) := by
  obtain ⟨changed, success⟩ := logicalUpdate_enabled op _ _ _ _ _ _ valid authorized
  exact ⟨changed, success, execution op _ _ _ _ _ _ _ _ _ success authorized memory operand
    code codeDisjoint stackDisjoint stack returnValid⟩

/-- Independent natural-bit set specification of the checked OS result. -/
theorem mathematical (operation : Logical64.Operation) (state : Atomics64.State) (actor : Nat)
    (identifier : HandleId64) (mask : Word) (changed : Atomics64.State × Event)
    (success : logicalUpdate operation.toLogicalOp state actor identifier mask = .ok changed) :
    Logical64.MathematicalResult operation changed.2.logical.event.before mask
      changed.2.logical.event.after := by
  have value := (logicalUpdate_sound operation.toLogicalOp _ _ _ _ _ success).2.2.2.1
  rw [value]
  exact Logical64.eval_mathematical operation _ _

/-- Current authority and exact code suffice for all AF choices. The postcondition
retains the OS event, exact RAM, ABI frames, actual RET and independent result.
Physical CPU, compiler-source and language memory-order refinement are external. -/
theorem correct (operation : Logical64.Operation) (state : Atomics64.State) (actor : Nat)
    (identifier : HandleId64) (handle : Handle) (cell : Atomics64.Cell) (initial : X86.State)
    (returnAddress : Word) (valid : WellFormed state)
    (authorized : authorize state actor identifier = .ok (handle, cell))
    (memory : initial.memory = toMemory state.legacy.shared.resources.space)
    (operand : initial.registers .rdi = cell.address)
    (code : CodeAt initial.memory initial.rip (bytes operation.toLogicalOp))
    (codeDisjoint : QWordDisjoint cell.address initial.rip (bytes operation.toLogicalOp).length)
    (stackDisjoint : QWordDisjoint cell.address (initial.registers .rsp) 8)
    (stack : readWord initial.memory (initial.registers .rsp) = .ok returnAddress)
    (returnValid : canonical returnAddress = true) :
    AllExecutions initial (fun output =>
      ∃ changed, logicalUpdate operation.toLogicalOp state actor identifier
          (initial.registers .rsi) = .ok changed ∧
        WellFormed changed.1 ∧ output.instructions = 2 ∧ output.events = [changed.2.logical] ∧
        output.accesses = [.rmw8 cell.address, .stack8 (initial.registers .rsp)] ∧
        output.state.memory = toMemory changed.1.legacy.shared.resources.space ∧
        output.state.rip = returnAddress ∧
        output.state.registers .rsp = initial.registers .rsp + 8 ∧
        (∀ register, register ≠ .rsp →
          output.state.registers register = initial.registers register) ∧
        loadQWord output.state.memory cell.address = .ok changed.2.logical.event.after ∧
        Logical64.MathematicalResult operation changed.2.logical.event.before
          (initial.registers .rsi) changed.2.logical.event.after) := by
  intro choices
  obtain ⟨changed, success, actual⟩ := enabled operation.toLogicalOp state actor identifier handle cell initial
    choices returnAddress valid authorized memory operand code codeDisjoint stackDisjoint stack returnValid
  refine ⟨_, actual, changed, success, logicalUpdate_wellFormed _ _ _ _ _ _ valid success,
    rfl, rfl, ?_, rfl, rfl, ?_, ?_, ?_, mathematical _ _ _ _ _ _ success⟩
  · simp only [result, operand]
  · simp [result, returned, afterLogical, X86.State.writeRegister]
  · intro register other
    simp [result, returned, afterLogical, X86.State.writeRegister, other]
  · have readback := (logicalUpdate_sound _ _ _ _ _ _ success).1.readback
    rw [(logicalUpdate_identity _ _ _ _ _ _ _ _ success authorized).2] at readback
    exact readback

end EDSL.OS.Atomics64.LogicalRoutine
