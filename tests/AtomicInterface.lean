/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Concurrency.AtomicCalls
import EDSL.OS.TSO64.C23Projection.AtomicTrace
import tests.TSO64SharedCells
import tests.C23AtomicWeakening
import tests.TSO64DrainClosure
import EDSL.Audit

set_option autoImplicit false

namespace EDSL.Tests.AtomicInterface
open X86 OS.TSO64 OS.TSO64.C23Projection
open Concurrency

private instance : DecidableEq (Nat × Nat × Nat) := inferInstance
private instance : DecidableEq
    (Bool × List (Nat × Nat × Nat) × List (Option Nat) × List Nat) := inferInstance

def orders : AtomicTrace.Orders where
  read _ _ := .acquire
  write _ _ := .release
  rmw _ _ := .acqRel

def responsePosition (observations : List Observation) (tid : Nat) : Option Nat :=
  observations.findIdx? (fun observation => decide (observation = .returned tid))

/-- Two independent callable bodies share a code loan: MOV [RDI],RSI; RET;
MOV RAX,[RDI]; RET. Both calls return before the store's drain. Requests are
declared from the intended interface; replies and positions come from execution. -/
def actualCallMatch : Except Fault
    (Option (Bool × List (Nat × Nat × Nat) × List (Option Nat) × List Nat)) := do
  let initial ← TSO64SharedCells.start 0xc3078b48c3378948 0 0 7 0 0 4
  match AtomicTrace.verify initial
      [.issue 0 false, .issue 0 false, .issue 1 false, .issue 1 false, .drain 0] orders with
  | .error _ => pure none
  | .ok output =>
      let found : Option (Bool × List (Nat × Nat × Nat) × List (Option Nat) × List Nat) := do
        let writer ← output.run.events[0]?
        let reader ← output.run.events[1]?
        let writerReturn ← responsePosition output.run.observations 0
        let readerReturn ← responsePosition output.run.observations 1
        let worker ← output.run.state.workers[1]?
        let store : AtomicCalls.Call OS.Atomics64.CellId64 Word := {
          thread := 0, occurrence := 0, request := .storeRelease ⟨0⟩ 7, reply := ⟨⟩,
          invoked := 0, performed := writer.position, returned := writerReturn }
        let load : AtomicCalls.Call OS.Atomics64.CellId64 Word := {
          thread := 1, occurrence := 0, request := .loadAcquire ⟨0⟩,
          reply := worker.context.registers .rax,
          invoked := 0, performed := reader.position, returned := readerReturn }
        let calls := [store, load]
        pure (decide (calls.map AtomicCalls.Call.event =
            output.table.events.drop output.initials.length),
          calls.map (fun call => (call.thread, call.performed, call.returned)),
          output.table.sources, output.table.ranks)
      pure found

/-- The acquire returns initialization, and the typed calls match the actual
checked source rows. The release call returns at1 but publishes at4 (rank5).
No within-call publication point or unconditional synchronization is assumed. -/
theorem actual_typed_calls_allow_return_before_publication : actualCallMatch = .ok
    (some (true, [(0, 0, 1), (1, 2, 3)], [none, none, some 0], [0, 5, 0])) := by decide +kernel

/-- LOCK XADD [RDI],RAX; RET, with high initial bits and a nonzero delta.
The reply is taken from actual returned RAX. The declared RMW transformation
must match the actual before/after pair; an identity update must fail. -/
def actualRMWMatch : Except Fault (Option (Bool × Bool)) := do
  let initial ← TSO64SharedCells.start 0x0000c307c10f48f0 0 0x100000000 0 0 0 0
  match AtomicTrace.verify initial [.issue 0 false, .issue 0 false] orders with
  | .error _ => pure none
  | .ok output =>
      let found : Option (Bool × Bool) := do
        let event ← output.run.events[0]?
        let returned ← responsePosition output.run.observations 0
        let worker ← output.run.state.workers[0]?
        let call : AtomicCalls.Call OS.Atomics64.CellId64 Word := {
          thread := 0, occurrence := 0,
          request := .rmw ⟨0⟩ .acqRel (fun value => value + 5),
          reply := worker.context.registers .rax,
          invoked := 0, performed := event.position, returned := returned }
        let wrong : AtomicCalls.Call OS.Atomics64.CellId64 Word := {
          thread := 0, occurrence := 0, request := .rmw ⟨0⟩ .acqRel id,
          reply := worker.context.registers .rax,
          invoked := 0, performed := event.position, returned := returned }
        let actual := output.table.events[output.initials.length]?
        pure (decide (actual = some call.event), decide (actual = some wrong.event))
      pure found

theorem intended_rmw_transform_is_checked_against_actual_execution :
    actualRMWMatch = .ok (some (true, false)) := by decide +kernel

end EDSL.Tests.AtomicInterface

#print axioms EDSL.Concurrency.AtomicCalls.History.read_source
#print axioms EDSL.Concurrency.AtomicCalls.Realizes.direct_synchronizes
#audit_edsl
