/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.Model
import EDSL.OS.Futex.Storage

namespace EDSL.OS.Futex.Physical
open X86 AddressSpace

structure Access where
  actor : Nat
  handle : Nat
  deriving DecidableEq, Repr

/-- Fixed environment authority for each physical worker. These records never
select an instruction: decoding and execution run before resource replay. -/
structure Profile where
  service : Futex.Config
  payload : Nat → Option Storage.Grant
  atomic : Nat → Option Access

inductive Fault where
  | service (fault : Futex.Fault)
  | resources (fault : Atomics.Fault)
  | missingPayload | missingAtomic | wrongAddress | wrongOldValue
  deriving DecidableEq, Repr

@[simp] theorem throw_error (fault : Fault) : (throw fault : Except Fault α) = .error fault := rfl

/-- Update managed cells from an already observed physical effect. Ordinary
store retirement changes neither RAM nor managed cells; only its drain writes.
An atomic effect reuses the worker's live producer handle. -/
def synchronize (profile : Profile) (authority : Atomics.State) :
    Suspend.Observation → Except Fault Atomics.State
  | .machine (.drained worker store) => do
    let some grant := profile.payload worker | throw .missingPayload
    if grant.address ≠ store.address then throw .wrongAddress
    (Storage.publish authority grant store.value).mapError Fault.resources
  | .machine (.retired worker (some event)) => do
    let some access := profile.atomic worker | throw .missingAtomic
    let handle ← (Atomics.authorize authority access.actor access.handle).mapError Fault.resources
    if handle.address ≠ event.address then throw .wrongAddress
    let result ← (Atomics.exchange authority access.actor access.handle event.after).mapError Fault.resources
    if result.2 ≠ event.before then throw .wrongOldValue
    return result.1
  | _ => .ok authority

/-- Current authorization for the actual effect. This contains no successful
resource update, future service action, or future machine execution premise. -/
def Ready (profile : Profile) (authority : Atomics.State) : Suspend.Observation → Prop
  | .machine (.drained worker store) => ∃ grant,
      profile.payload worker = some grant ∧ grant.address = store.address ∧ grant.Valid authority
  | .machine (.retired worker (some event)) => ∃ access handle,
      profile.atomic worker = some access ∧
      Atomics.authorize authority access.actor access.handle = .ok handle ∧ handle.address = event.address
  | _ => True

/-- Independent exact RAM effects obtained from physical execution. -/
def Effect (before after : Memory) : Suspend.Observation → Prop
  | .machine (.drained _ store) => storeDWord before store.address store.value = .ok after
  | .machine (.retired _ (some event)) => ExchangeTransition before event after
  | _ => after = before

/-- Physical issue is inverted without consulting profile authority, service
phases, an expected opcode, or an expected program counter. -/
theorem issue_effect {before after : Suspend.State} {worker : Nat} {observation : Suspend.Observation}
    (success : Suspend.issue before worker = .ok (after, observation)) :
    Effect before.machine.memory after.machine.memory observation := by
  cases Suspend.issue_effect _ _ _ success with
  | entered live running pending decoded empty executed stepped user continuation => rfl
  | parked live running pending => rfl
  | @machine machine observation pending issued =>
    obtain ⟨selected, instruction, live, running, decoded, executed, effect⟩ := TSO.issue_effect _ _ _ issued
    cases effect with
    | queued pending aligned data executed writable output => rfl
    | ordinary pending unlocked loads executed memory => rfl
    | returned pending unlocked instruction executed memory => rfl
    | atomic pending classified empty data executed transition address accumulator => exact transition
    | blocked pending classified nonempty => rfl

theorem drain_effect {before after : Suspend.State} {worker : Nat} {observation : Suspend.Observation}
    (success : Suspend.drain before worker = .ok (after, observation)) :
    Effect before.machine.memory after.machine.memory observation := by
  obtain ⟨machine, observed, drained, same⟩ := Suspend.drain_ok _ _ _ success
  obtain ⟨selected, head, tail, memory, live, buffer, committed, installed⟩ := TSO.drain_ok _ _ _ drained
  have afterEq := congrArg Prod.fst same
  have obsEq := congrArg Prod.snd same
  have machineEq := congrArg Prod.fst installed
  have observedEq := congrArg Prod.snd installed
  dsimp only at afterEq obsEq machineEq observedEq
  rw [afterEq, obsEq, observedEq, machineEq]
  exact committed

/-- Every admitted observed effect has an enabled checked lift. Both models
continue to use the same entire RAM, including all unrelated bytes/permissions. -/
theorem synchronize_enabled (profile : Profile) (authority : Atomics.State)
    (before after : Memory) (observation : Suspend.Observation)
    (valid : Atomics.WellFormed authority)
    (memory : toMemory authority.shared.resources.space = before)
    (ready : Ready profile authority observation) (effect : Effect before after observation) :
    ∃ next, synchronize profile authority observation = .ok next ∧
      toMemory next.shared.resources.space = after ∧
      Atomics.History authority next ∧ Atomics.WellFormed next := by
  cases observation with
  | machine observed =>
    cases observed with
    | drained worker store =>
      obtain ⟨grant, atGrant, address, writable⟩ := ready
      obtain ⟨next, published⟩ := Storage.publish_enabled authority grant store.value writable
      have facts := Storage.publish_effect published
      have afterEq : after = writeDWordUnchecked before store.address store.value := by
        dsimp only [Effect] at effect
        unfold storeDWord at effect
        split at effect
        · exact Except.ok.inj effect.symm
        · cases effect
      refine ⟨next, ?_, ?_, .next facts.1 .refl, facts.1.wellFormed valid⟩
      · simp [synchronize, atGrant, address, published, Except.mapError]
      · rw [facts.2.1, memory, address, afterEq]
    | retired worker event =>
      cases event with
      | none => exact ⟨authority, rfl, memory.trans effect.symm, .refl, valid⟩
      | some event =>
        obtain ⟨access, handle, atAccess, authorized, address⟩ := ready
        obtain ⟨result, exchanged, old, same, wf⟩ := Storage.exchange_coupling valid memory authorized address effect
        exact ⟨result.1, by simp [synchronize, atAccess, authorized, address, exchanged, old, Except.mapError],
          same, .next (.exchange exchanged) .refl, wf⟩
    | blocked worker => exact ⟨authority, rfl, memory.trans effect.symm, .refl, valid⟩
  | entered worker invocation => exact ⟨authority, rfl, memory.trans effect.symm, .refl, valid⟩
  | parked worker invocation => exact ⟨authority, rfl, memory.trans effect.symm, .refl, valid⟩
  | resumed worker invocation raw => exact ⟨authority, rfl, memory.trans effect.symm, .refl, valid⟩
  | idle => exact ⟨authority, rfl, memory.trans effect.symm, .refl, valid⟩

/-- Actual issue, resource replay and pin retention are one pure adapter step.
A wrapper failure returns no partially modified state. -/
def issue (profile : Profile) (state : Futex.State) (worker : Nat) :
    Except Fault (Futex.State × Suspend.Observation) := do
  let result ← (Suspend.issue state.suspended worker).mapError (fun fault => Fault.service (.suspended fault))
  let authority ← synchronize profile state.authority result.2
  let next := { state with suspended := result.1, authority := authority }
  match result.2 with
  | .entered selected invocation =>
    let captured ← (captureEntered profile.service next selected invocation).mapError Fault.service
    return (captured, result.2)
  | _ => return (next, result.2)

def drain (profile : Profile) (state : Futex.State) (worker : Nat) :
    Except Fault (Futex.State × Suspend.Observation) := do
  let result ← (Suspend.drain state.suspended worker).mapError (fun fault => Fault.service (.suspended fault))
  let authority ← synchronize profile state.authority result.2
  return ({ state with suspended := result.1, authority := authority }, result.2)

end EDSL.OS.Futex.Physical
