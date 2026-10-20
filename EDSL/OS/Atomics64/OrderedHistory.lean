/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Atomics64.LogicalTrace
import EDSL.Logical64.OrderedHistory

set_option warningAsError true

namespace EDSL.OS.Atomics64
open X86

/-- Decoded machine tags are adapted outside the independent ordered contract.
The actual tag, rather than a desired task parameter, chooses the request. -/
def operationOfLogicalOp : Sequential.LogicalOp → Logical64.Operation
  | .band => .intersection
  | .bor => .union
  | .bxor => .symmetricDifference

@[simp] theorem operationOfLogicalOp_toLogicalOp (operation : Sequential.LogicalOp) :
    (operationOfLogicalOp operation).toLogicalOp = operation := by
  cases operation <;> rfl

theorem operationOfLogicalOp_injective {first second : Sequential.LogicalOp}
    (same : operationOfLogicalOp first = operationOfLogicalOp second) : first = second := by
  have := congrArg Logical64.Operation.toLogicalOp same
  simpa only [operationOfLogicalOp_toLogicalOp] using this

def Event.orderedRequest (event : Event) : Logical64.Operation × Word :=
  (operationOfLogicalOp event.logical.op, event.logical.mask)

/-- Mapping is one-for-one: no no-change event or cancelling XOR occurrence
is removed. Actor, handle and cell identity remain available in the source
event list; this projection specifies only its ordered mathematical effects. -/
theorem orderedRequests_length (events : List Event) :
    (events.map Event.orderedRequest).length = events.length := List.length_map _

theorem LogicalChain.orderedMathematicalResult {initial final : Word} {events : List Event}
    (chain : LogicalChain initial events final) :
    Logical64.OrderedMathematicalResult initial (events.map Event.orderedRequest) final := by
  induction chain with
  | nil => exact .nil
  | @cons initial event rest final _ write _ induction =>
    refine .cons ?_ induction
    have result := Logical64.eval_mathematical (operationOfLogicalOp event.logical.op)
      initial event.logical.mask
    simpa only [Event.orderedRequest, operationOfLogicalOp_toLogicalOp, ← write] using result

/-- Actual checked updates supply the requests and the current final readback.
This is a fixed-cell abstract OS trace theorem; it establishes no CPU scheduler,
thread lifecycle, physical machine refinement or compound-call linearizability. -/
theorem LogicalTrace.orderedMathematicalResult
    {identifier : CellId64} {cell : Cell} {before after : State} {events : List Event}
    (trace : LogicalTrace identifier cell before events after) (initial : Word)
    (read : loadQWord (AddressSpace.toMemory before.legacy.shared.resources.space) cell.address = .ok initial) :
    ∃ final,
      loadQWord (AddressSpace.toMemory after.legacy.shared.resources.space) cell.address = .ok final ∧
      Logical64.OrderedMathematicalResult initial (events.map Event.orderedRequest) final := by
  obtain ⟨final, finalRead, chain⟩ := trace.chain initial read
  exact ⟨final, finalRead, chain.orderedMathematicalResult⟩

end EDSL.OS.Atomics64
