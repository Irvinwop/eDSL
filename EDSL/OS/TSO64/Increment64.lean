/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.RMWFamily
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Shared exact increment consequences of an existing current arithmetic machine
effect. The old qword comes from current RAM. Inherits the imported effect's
long-mode/CET-off, coherent scalar WB RAM, stable-translation/no-alias and
protected-resource model. Selected authority and pointer binding are explicit.
This supplies no scheduler, progress, physical LOCK, Linux, compiler, fairness,
ABI or corpus-refinement claim.
-/

namespace EDSL.OS.TSO64.Increment64
open X86

/-- INC or ADD with encoded imm8 exactly 1. XADD is excluded even if its
current source happens to contain 1: it has an old-word destination. -/
def IsIncrement : AddRMW64.Instruction → Prop
  | .inc _ => True
  | .addImm8 encoding => encoding.imm8 = 1
  | .xadd _ => False

theorem IsIncrement.delta {instruction : AddRMW64.Instruction}
    (increment : IsIncrement instruction) (initial : X86.State) :
    instruction.delta initial = 1 := by
  cases instruction with
  | xadd _ => exact False.elim increment
  | addImm8 encoding =>
    change encoding.imm8 = (1 : Byte) at increment
    change encoding.imm8.signExtend 64 = (1 : Word)
    exact (congrArg (fun byte : Byte => byte.signExtend 64) increment).trans (by decide +kernel)
  | inc _ => rfl

theorem IsIncrement.noDestination {instruction : AddRMW64.Instruction}
    (increment : IsIncrement instruction) : instruction.oldDestination = none := by
  cases instruction with
  | xadd _ => exact False.elim increment
  | addImm8 _ => rfl
  | inc _ => rfl

/-- Convenience consequences, retaining the entire original observation and
joint effect. RIP uses the actual typed encoding's bytes (INC 4, ADD 5).
All GPRs includes RSP, the operand base, and arbitrary unmentioned registers. -/
structure Effect (before : World) (actor : Nat) (identifier : Atomics64.HandleId64)
    (initial : X86.State) (instruction : AddRMW64.Instruction)
    (result : World × Atomics64.FetchAddEvent) (observation : AddRMW64.Observation) : Prop where
  machine : RMWFamily.arithmetic.MachineEffect before actor identifier initial
    instruction result observation
  increment : IsIncrement instruction
  delta : result.2.arithmetic.delta = 1
  observedDelta : observation.event.delta = 1
  address : result.2.arithmetic.event.address = initial.registers instruction.base
  old : loadQWord initial.memory result.2.arithmetic.event.address =
    .ok result.2.arithmetic.event.before
  after : result.2.arithmetic.event.after = result.2.arithmetic.event.before + 1
  readback : loadQWord observation.state.memory result.2.arithmetic.event.address =
    .ok (result.2.arithmetic.event.before + 1)
  rip : observation.state.rip = initial.rip + BitVec.ofNat 64 instruction.bytes.length
  registers : observation.state.registers = initial.registers

namespace Effect
variable {before : World} {actor : Nat} {identifier : Atomics64.HandleId64}
  {initial : X86.State} {instruction : AddRMW64.Instruction}
  {result : World × Atomics64.FetchAddEvent} {observation : AddRMW64.Observation}

/-- No old-value oracle or enabled future run: specialize an already supplied
current checked effect, without reconstructing a primitive or machine step. -/
theorem of_effect
    (effect : RMWFamily.arithmetic.MachineEffect before actor identifier initial
      instruction result observation) (increment : IsIncrement instruction) :
    Effect before actor identifier initial instruction result observation := by
  have current := RMWFamily.MachineEffect.arithmetic (family := .arithmetic) effect
  have delta : result.2.arithmetic.delta = 1 := current.delta.trans (increment.delta initial)
  have added : result.2.arithmetic.event.after = result.2.arithmetic.event.before + 1 := by
    simpa only [delta] using current.cpu.after
  exact {
    machine := effect
    increment := increment
    delta := delta
    observedDelta := by rw [current.event]; exact delta
    address := current.cpu.address
    old := current.cpu.old
    after := added
    readback := by simpa only [added] using current.cpu.readback
    rip := by simpa only [RMWFamily.embed, AddRMW64.Instruction.bytes_length] using current.rip
    registers := current.all_registers increment.noDestination }

/-- The caller names the actual authorized handle/cell and binds the current
base value to its pointer. This is not a proof of the scheduler's first-match
selector; retain that separate equality when using AtomicIssued.of_effect. -/
theorem selected (summary : Effect before actor identifier initial instruction result observation)
    (handle : Atomics64.Handle) (cell : Atomics64.Cell) (pointer : Word)
    (authorized : Atomics64.authorize before actor identifier = .ok (handle, cell))
    (operand : initial.registers instruction.base = pointer) :
    before.cells handle.cell = some cell ∧ Atomics64.ValidCell before.legacy.shared cell ∧
      result.2.actor = actor ∧ result.2.handle = identifier ∧ result.2.cell = handle.cell ∧
      result.2.arithmetic.event.address = pointer ∧ cell.address = pointer ∧
      loadQWord initial.memory pointer = .ok result.2.arithmetic.event.before ∧
      loadQWord observation.state.memory pointer = .ok (result.2.arithmetic.event.before + 1) := by
  have current := RMWFamily.MachineEffect.arithmetic (family := .arithmetic) summary.machine
  have identities := Atomics64.fetchAdd_identity _ _ _ _ _ handle cell current.checked authorized
  have authority := Atomics64.authorize_ok _ _ _ _ authorized
  have target := summary.address.trans operand
  have actorHandle := current.actor_handle
  refine ⟨authority.2.2.1, authority.2.2.2, actorHandle.1, actorHandle.2,
    identities.1, target, identities.2.symm.trans target, ?_, ?_⟩
  · simpa only [target] using summary.old
  · simpa only [target] using summary.readback

end Effect

#print axioms IsIncrement
#print axioms IsIncrement.delta
#print axioms IsIncrement.noDestination
#print axioms Effect
#print axioms Effect.of_effect
#print axioms Effect.selected

end EDSL.OS.TSO64.Increment64

#audit_edsl
