/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.FetchAddResources

set_option warningAsError true

namespace EDSL.Tests.CorpusFetchAdd64
open X86 OS OS.TSO64 Concurrency Corpus.V1

abbrev Compiler := FetchAddWindows.Compiler
abbrev Entry := FetchAddCalls64.Entry Nat

def padding : Compiler → List Entry
  | .defaultGCC => [.execute (.issue 0 true) .quiet, .execute (.issue 1 false) .quiet]
  | .defaultClang => []

def forward (compiler : Compiler) (idA idB : Nat) (oldA oldB deltaA deltaB : Word) : List Entry :=
  [.invoke idA 0 deltaA, .invoke idB 1 deltaB] ++ padding compiler ++
  [.execute (.issue 0 false) .quiet, .execute (.issue 1 true) .quiet,
   .execute (.issue 0 true) (.rmw idA), .execute (.issue 1 false) (.rmw idB),
   .execute (.issue 1 true) (.response idB 1 oldB),
   .execute (.issue 0 false) (.response idA 0 oldA)]

def reverse (compiler : Compiler) (oldA oldB deltaA deltaB : Word) : List Entry :=
  [.invoke 10 0 deltaA, .invoke 20 1 deltaB] ++ padding compiler ++
  [.execute (.issue 0 true) .quiet, .execute (.issue 1 false) .quiet,
   .execute (.issue 1 true) (.rmw 20), .execute (.issue 0 false) (.rmw 10),
   .execute (.issue 0 true) (.response 10 0 oldA),
   .execute (.issue 1 false) (.response 20 1 oldB)]

/-- One actual gated replay; neither the scheduler nor an arithmetic evaluator
is rerun to obtain the expected result. Expectations below are independent
literal full64 carry/wrap/old-return and complete-protocol requirements. -/
def observe (compiler : Compiler) (old deltaA deltaB : Word) (entries : List Entry) :=
  let before := FetchAddResources.current compiler old deltaA deltaB
  (FetchAddABI64.replay (FetchAddResources.image compiler) FetchAddResources.target
    FetchAddResources.cell before entries).map fun result =>
      (Linearizability.check result.events,
        result.observations.filterMap fun observation => match observation with
          | .rmw tid event => some (tid, event.arithmetic.delta,
              event.arithmetic.event.before, event.arithmetic.event.after)
          | _ => none,
        FetchAddCalls64.read result.state.state FetchAddResources.cell,
        collect result.state.state 0, collect result.state.state 1,
        [0, 1].all fun tid =>
          match before.state.workers[tid]?, result.state.state.workers[tid]? with
          | some initial, some final =>
              !final.context.flags.getLsbD 10 &&
              decide (final.context.registers .rsp = initial.context.registers .rsp + 8) &&
              PureCall.calleeSaved.all fun register =>
                decide (final.context.registers register = initial.context.registers register)
          | _, _ => false)

-- Upper-word carry and full64 delta; both bodies really execute concurrently,
-- and both returns occur after the second context's RMW.
theorem carry_old_returns (compiler : Compiler) :
    observe compiler 0x11223344ffffffff 1 0x100000001
      (forward compiler 10 20 0x11223344ffffffff 0x1122334500000000 1 0x100000001) =
    some (true, [(0, 1, 0x11223344ffffffff, 0x1122334500000000),
      (1, 0x100000001, 0x1122334500000000, 0x1122334600000001)],
      .ok 0x1122334600000001, .ok 0x11223344ffffffff, .ok 0x1122334500000000, true) := by
  cases compiler <;> fetch_add_kernel_rfl

-- Reverse the real RMW order across modulo wrap. Returning the new word,
-- truncating to 32 bits or ordering by invocation would fail this contract.
theorem reverse_wrap_old_returns (compiler : Compiler) :
    observe compiler 0xfffffffffffffffe 1 2 (reverse compiler 0 0xfffffffffffffffe 1 2) =
    some (true, [(1, 2, 0xfffffffffffffffe, 0), (0, 1, 0, 1)],
      .ok 1, .ok 0, .ok 0xfffffffffffffffe, true) := by
  cases compiler <;> fetch_add_kernel_rfl

-- Equal zero arithmetic still needs two distinct complete occurrences. Reusing
-- an ID rejects even though both inputs, outputs and state changes are equal.
theorem zero_calls_need_distinct_ids (compiler : Compiler) :
    (observe compiler 0 0 0 (forward compiler 10 20 0 0 0 0)).map (fun result => result.1) = some true ∧
    (observe compiler 0 0 0 (forward compiler 10 10 0 0 0 0)).map (fun result => result.1) = some false := by
  cases compiler <;> constructor <;> fetch_add_kernel_rfl

-- A missing actual RET is a pending call, even when the update adds zero.
theorem pending_return_rejected (compiler : Compiler) :
    let entries := forward compiler 10 20 0 0 0 0
    (observe compiler 0 0 0 (entries.take (entries.length - 1))).map (fun result => result.1) = some false := by
  cases compiler <;> fetch_add_kernel_rfl

-- ABI admission compares the ENTIRE RSI word, before any execution.
theorem upper_delta_rejected (compiler : Compiler) :
    FetchAddABI64.replay (FetchAddResources.image compiler) FetchAddResources.target
      FetchAddResources.cell (FetchAddResources.current compiler 17 1 2)
      ([.invoke 10 0 0x100000001] : List Entry) = none := by
  cases compiler <;> fetch_add_kernel_rfl

-- Every byte in the selected symbol is bound; replacing its LAST byte fails.
theorem last_byte_rejected (compiler : Compiler) :
    let image : FetchAddABI64.Image := ⟨FetchAddResources.entry compiler,
      (FetchAddWindows.bytes compiler).take ((FetchAddWindows.bytes compiler).length - 1) ++ [0x90]⟩
    FetchAddABI64.replay image FetchAddResources.target FetchAddResources.cell
      (FetchAddResources.current compiler 17 1 2) ([.invoke 10 0 1] : List Entry) = none := by
  cases compiler <;> fetch_add_kernel_rfl

/-- Change represented CPU entry state while retaining the exact checked
manager world, leases, handles and FIFOs. WF imposes no desired ABI result. -/
def recontext {target cell} (before : FetchAddCalls64.CheckedState target cell)
    (change : Context → Context) : FetchAddCalls64.CheckedState target cell :=
  ⟨{ before.state with workers := before.state.workers.map fun worker =>
      { worker with context := change worker.context } },
    ⟨before.valid.1, by
      intro worker member
      obtain ⟨original, listed, rfl⟩ := List.mem_map.mp member
      exact before.valid.2 original listed⟩, before.live⟩

def entryControls (compiler : Compiler) : List Bool :=
  let before := FetchAddResources.current compiler 17 1 2
  let rejects := fun state => (FetchAddABI64.replay (FetchAddResources.image compiler)
    FetchAddResources.target FetchAddResources.cell state ([.invoke 10 0 1] : List Entry)).isNone
  [rejects (recontext before fun context => { context with flags := context.flags ||| 0x400 }),
   rejects (recontext before fun context => { context with registers := fun register =>
     if register = .rsp then 0x710008 else context.registers register }),
   rejects (recontext before fun context => { context with rip := context.rip + 1 })]

-- Set DF, use the peer's readable caller slot, or enter inside the selected
-- frozen function. Current resources alone authorize none of these entries.
theorem invalid_entry_rejected (compiler : Compiler) : entryControls compiler = [true, true, true] := by
  cases compiler <;> fetch_add_kernel_rfl

end EDSL.Tests.CorpusFetchAdd64

#audit_edsl
