/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.Access
import EDSL.OS.TSO64.Run
import EDSL.X86.Sequential.Return

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.OS.TSO64.Return
open X86

/-!
Response facts for a single actual RET under either authority profile and
instruction family.
The prestate invariant supplies current resource validity and protects the
original caller slot from the local FIFO overlay. No queue emptiness or prior
issue history is required. Function-wide result and ABI contracts, publication,
and correspondence with physical execution remain separate obligations.
-/

/-- A response comes from actual RET execution with current code and original
caller authority. The exact installation retains resources, pending entries,
and the next store number; it installs the actual returned machine context.
The profile indexes the ordinary effect and its read checks; the instruction
family indexes the actual guarded fetch. -/
def ReturnOrigin (before : State) (action : Action)
    (result : State × Observation) (tid : Nat) (value : Word)
    (profile : Profile := .ownedOnly) (family : RMWFamily := .xaddOnly) : Prop :=
  ∃ af worker output observation,
    action = .issue tid af ∧ before.workers[tid]? = some worker ∧ worker.phase ≠ .returned ∧
    LeaseCurrent before.world worker.resources.actor worker.resources.code ∧
    LeaseCurrent before.world worker.resources.actor worker.resources.caller ∧
    before.world.legacy.shared.loans worker.resources.caller.identifier = some worker.resources.caller.loan ∧
    worker.resources.caller.loan.region = AddressSpace.qwordRegion worker.resources.callerAddress ∧
    codeFits worker (Sequential.Instruction.legacy .ret).length ∧
    decode (fetchCPU before worker) family = .ok (.ordinary (.legacy .ret)) ∧
    OrdinaryEffect before tid worker (.legacy .ret) af result profile ∧
    Sequential.decodeAt (localCPU before worker) = .ok (.legacy .ret) ∧
    Sequential.execute (localCPU before worker) (.legacy .ret) af = .ok observation ∧
    Sequential.step af (localCPU before worker) = .ok observation ∧
    observation.result = .returned output ∧
    (localCPU before worker).registers .rsp = worker.resources.callerAddress ∧
    (∃ target, Borrowing.loadWord64 before.world.legacy.shared worker.resources.actor
      worker.resources.caller.identifier worker.resources.callerAddress = .ok target ∧
      readWord (localCPU before worker).memory worker.resources.callerAddress = .ok target) ∧
    result = (install before tid before.world
      { worker with context := .ofCPU output, phase := .returned }, .returned tid) ∧
    output.registers .rax = value

/-- Project the response from the actual successor worker's RAX. Observations
other than RET and missing successor workers produce no response. -/
def returnValue (result : State × Observation) : Option (Nat × Word) :=
  match result.2 with
  | .returned tid => result.1.workers[tid]?.map fun worker => (tid, worker.context.registers .rax)
  | _ => none

/-- Explicit resource, FIFO, and counter frame for clients that compose a RET
response with a load or store call. The world is retained without publication. -/
theorem ReturnOrigin.frame {before : State} {action : Action}
    {result : State × Observation} {tid : Nat} {value : Word}
    {profile : Profile} {family : RMWFamily}
    (origin : ReturnOrigin before action result tid value profile family) :
    result.1.world = before.world ∧
      ∃ prior current,
        before.workers[tid]? = some prior ∧ result.1.workers[tid]? = some current ∧
        current.context.registers .rax = value ∧ current.phase = .returned ∧
        current.resources = prior.resources ∧ current.pending = prior.pending ∧
        current.nextStore = prior.nextStore := by
  obtain ⟨_, worker, output, _, _, live, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    installed, actualValue⟩ := origin
  rw [installed]
  refine ⟨rfl, worker, { worker with context := .ofCPU output, phase := .returned }, live,
    ?_, actualValue, rfl, rfl, rfl, rfl⟩
  exact List.getElem?_set_self (List.getElem_of_getElem? live).1

/-- Successful RET exposes both the response projection and its independent
machine/resource origin. All initial FIFOs may be nonempty provided the stated
prestate invariant holds under the selected profile. -/
theorem returned_origin {before : State} {action : Action}
    {after : State} {tid : Nat} {profile : Profile} {family : RMWFamily}
    (valid : WellFormed before profile)
    (success : step before action profile family = .ok (after, .returned tid)) :
    ∃ value, returnValue (after, .returned tid) = some (tid, value) ∧
      ReturnOrigin before action (after, .returned tid) tid value profile family := by
  cases step_origin (profile := profile) success with
  | @ordinary _ tid af worker instruction result _ live running code caller fetched effect =>
    have workerValid := valid.2 _ (List.mem_of_getElem? live)
    have accesses := effect.accesses
    have actualEffect := effect
    cases effect with
    | @intro pending observation supported bounds decoded reads queue actual finish =>
      cases finish with
      | @returned output _ outcome =>
        have executed := actual
        rw [Sequential.step_eq_execute _ decoded] at executed
        have onlyRet := Sequential.execute_returned_only_ret executed outcome
        subst instruction
        cases queue with
        | enqueued intent grant =>
          simp [storeIntent, Sequential.Instruction.storeIntent64,
            Sequential.Instruction.storeIntent, X86.Instruction.storeIntent] at intent
        | unchanged intent =>
          obtain ⟨observed, actualAgain, authorized⟩ := accesses
          have sameObservation := Except.ok.inj (actualAgain.symm.trans actual)
          subst observed
          have listed := Sequential.execute_reads executed
          have current := authorized ⟨.stack, (localCPU before worker).registers .rsp, 8⟩
            (by rw [listed]; simp [Sequential.Instruction.operandReads])
          obtain ⟨slot, _, target, borrowed⟩ := current.1
          change (localCPU before worker).registers .rsp = worker.resources.callerAddress at slot
          have borrowedSlot : Borrowing.loadWord64 before.world.legacy.shared worker.resources.actor
              worker.resources.caller.identifier worker.resources.callerAddress = .ok target := by
            change Borrowing.loadWord64 before.world.legacy.shared worker.resources.actor
              worker.resources.caller.identifier ((localCPU before worker).registers .rsp) = .ok target at borrowed
            rw [slot] at borrowed
            exact borrowed
          have loaded := (Borrowing.loadWord64_ok _ _ _ _ _ borrowedSlot).choose_spec.2.2
          have localRead : readWord (localCPU before worker).memory worker.resources.callerAddress = .ok target := by
            rw [local_original_caller (profile := profile) valid workerValid]
            exact readWord_of_loadQWord _ _ _ loaded
          have installed : (install before tid before.world
              { worker with context := .ofCPU output, phase := .returned }).workers[tid]? =
              some { worker with context := .ofCPU output, phase := .returned } :=
            List.getElem?_set_self (List.getElem_of_getElem? live).1
          refine ⟨output.registers .rax, ?_, af, worker, output, observation, rfl, live, running,
            code, caller, workerValid.1.2.1.1, workerValid.1.2.2.1, bounds,
            fetched, actualEffect, decoded, executed, actual, outcome, slot,
            ⟨target, borrowedSlot, localRead⟩, rfl, rfl⟩
          change Option.map (fun worker : Worker => (tid, worker.context.registers .rax))
            (install before tid before.world
              { worker with context := .ofCPU output, phase := .returned }).workers[tid]? = _
          rw [installed]
          rfl

/-- A projected response from a successful scheduler step has an actual RET
origin. This public theorem is independent of call classification or history. -/
theorem returnValue_sound {before : State} {action : Action}
    {result : State × Observation} {tid : Nat} {value : Word}
    {profile : Profile} {family : RMWFamily}
    (valid : WellFormed before profile) (success : step before action profile family = .ok result)
    (accepted : returnValue result = some (tid, value)) :
    ReturnOrigin before action result tid value profile family := by
  cases observed : result.2 with
  | returned actualTid =>
    have shape : result = (result.1, .returned actualTid) := Prod.ext rfl observed
    have actual : step before action profile family = .ok (result.1, .returned actualTid) := by
      exact success.trans (congrArg Except.ok shape)
    obtain ⟨actualValue, extracted, origin⟩ := returned_origin valid actual
    rw [shape] at accepted
    have same : (actualTid, actualValue) = (tid, value) :=
      Option.some.inj (extracted.symm.trans accepted)
    cases same
    rw [shape]
    exact origin
  | ordinary _ | rmw _ _ | blocked _ | drained _ _ => simp [returnValue, observed] at accepted

end EDSL.OS.TSO64.Return
