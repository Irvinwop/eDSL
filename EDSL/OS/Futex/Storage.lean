/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Atomics
import EDSL.OS.Suspend

namespace EDSL.OS.Futex.Storage
open X86 AddressSpace

/-- A separate ordinary-write allocation. Futex reservations do not authorize
ordinary buffered writes to the reserved word. -/
structure Grant where
  owner : Nat
  ticket : Ownership.Ticket
  address : Word
  deriving DecidableEq, Repr

/-- Current authority, byte permissions and absence of conflicting reservations
and readers. No successful future drain or resource update is assumed. -/
def Grant.Valid (state : Atomics.State) (grant : Grant) : Prop :=
  ∃ allocation, Ownership.authorize state.shared.resources grant.owner grant.ticket = .ok allocation ∧
    Ownership.containsWord allocation grant.address = true ∧
    canStoreDWord (toMemory state.shared.resources.space) grant.address = true ∧
    Atomics.allowed state (.store grant.owner grant.ticket grant.address 0) = true ∧
    Borrowing.allowed state.shared (.store grant.owner grant.ticket grant.address 0) = true

def publish (state : Atomics.State) (grant : Grant) (value : BitVec 32) :
    Except Atomics.Fault Atomics.State := do
  let result ← Atomics.mutate state (.store grant.owner grant.ticket grant.address value)
  return result.1

theorem publish_enabled (state : Atomics.State) (grant : Grant) (value : BitVec 32)
    (ready : grant.Valid state) : ∃ after, publish state grant value = .ok after := by
  obtain ⟨allocation, authorized, fits, writable, unreserved, unborrowed⟩ := ready
  let world := { state.shared.resources with
    space := writeWordCells state.shared.resources.space grant.address value }
  have stored : Ownership.storeWord state.shared.resources grant.owner grant.ticket grant.address value = .ok world :=
    Ownership.storeWord_success _ _ _ _ _ _ authorized fits writable
  have unreserved' : Atomics.allowed state (.store grant.owner grant.ticket grant.address value) = true := unreserved
  have unborrowed' : Borrowing.allowed state.shared (.store grant.owner grant.ticket grant.address value) = true := unborrowed
  exact ⟨{ state with shared := { state.shared with resources := world } }, by
    simp [publish, Atomics.mutate, unreserved', Borrowing.mutate, unborrowed',
      Ownership.Mutation.run, stored, Except.mapError, Except.map, world]⟩

theorem publish_effect {state after : Atomics.State} {grant : Grant} {value : BitVec 32}
    (success : publish state grant value = .ok after) :
    Atomics.Step state after ∧
    toMemory after.shared.resources.space =
      writeDWordUnchecked (toMemory state.shared.resources.space) grant.address value ∧
    after.handles = state.handles ∧ after.nextHandle = state.nextHandle := by
  cases changed : Atomics.mutate state (.store grant.owner grant.ticket grant.address value) with
  | error fault => simp [publish, changed] at success
  | ok result =>
    simp [publish, changed] at success
    subst after
    obtain ⟨_, shared, mutation, same⟩ := Atomics.mutate_ok _ _ _ changed
    obtain ⟨_, resources, owned, sharedEq⟩ := Borrowing.mutate_ok _ _ _ mutation
    cases stored : Ownership.storeWord state.shared.resources grant.owner grant.ticket grant.address value with
    | error fault => simp [Ownership.Mutation.run, stored, Except.map] at owned
    | ok world =>
      simp [Ownership.Mutation.run, stored, Except.map] at owned
      subst resources
      obtain ⟨allocation, space, _, _, osStore, worldEq⟩ := Ownership.storeWord_ok _ _ _ _ _ _ stored
      obtain ⟨spaceEq, allowed⟩ := AddressSpace.storeWord_ok _ _ _ _ osStore
      refine ⟨.mutate changed, ?_, ?_, ?_⟩
      · rw [same, sharedEq, worldEq, spaceEq]
        exact writeWord_projects _ _ _ allowed
      · rw [same]
      · rw [same]

/-- A checked managed update publishes exactly the actual FIFO head. -/
theorem drain_coupling {authority : Atomics.State} {before after : Suspend.State}
    {worker : Nat} {store : StoreBuffer.Store} {grant : Grant}
    (memory : toMemory authority.shared.resources.space = before.machine.memory)
    (ready : grant.Valid authority)
    (success : Suspend.drain before worker = .ok (after, .machine (.drained worker store)))
    (target : ∀ selected head tail, before.machine.workers[worker]? = some selected →
      selected.buffer = head :: tail → head.address = grant.address) :
    ∃ next, publish authority grant store.value = .ok next ∧
      toMemory next.shared.resources.space = after.machine.memory ∧
      Atomics.Step authority next := by
  obtain ⟨machine, observation, drained, same⟩ := Suspend.drain_ok _ _ _ success
  obtain ⟨selected, head, tail, current, live, buffer, committed, installed⟩ := TSO.drain_ok _ _ _ drained
  have address := target selected head tail live buffer
  obtain ⟨next, published⟩ := publish_enabled authority grant head.value ready
  have effect := publish_effect published
  have currentEq : current = writeDWordUnchecked before.machine.memory head.address head.value := by
    unfold storeDWord at committed
    split at committed
    · exact Except.ok.inj committed.symm
    · cases committed
  have observed := congrArg Prod.snd same
  have machineEq := congrArg Prod.fst installed
  have observationEq := congrArg Prod.snd installed
  dsimp only at observed observationEq machineEq
  rw [observationEq] at observed
  have storeEq : store = head := by cases observed; rfl
  subst store
  refine ⟨next, published, ?_, effect.1⟩
  rw [effect.2.1, memory, ← address]
  have afterEq := congrArg Prod.fst same
  dsimp only at afterEq
  rw [afterEq, machineEq, currentEq]
  rfl

/-- Exact resource coupling for an architectural atomic event. Its old value
is identified by two reads of the same current RAM, never an entry snapshot. -/
theorem exchange_coupling {authority : Atomics.State} {before after : Memory}
    {actor identifier : Nat} {handle : Atomics.Handle} {event : AtomicEvent}
    (valid : Atomics.WellFormed authority)
    (memory : toMemory authority.shared.resources.space = before)
    (authorized : Atomics.authorize authority actor identifier = .ok handle)
    (address : handle.address = event.address)
    (transition : ExchangeTransition before event after) :
    ∃ result, Atomics.exchange authority actor identifier event.after = .ok result ∧
      result.2 = event.before ∧ toMemory result.1.shared.resources.space = after ∧
      Atomics.WellFormed result.1 := by
  obtain ⟨result, exchanged⟩ := Atomics.exchange_enabled authority actor identifier handle event.after valid authorized
  obtain ⟨selected, checked, actual⟩ := Atomics.exchange_sound _ _ _ _ _ exchanged
  have same := Except.ok.inj (authorized.symm.trans checked)
  subst selected
  have old : result.2 = event.before := by
    have read := actual.2.2.1
    rw [memory, address, transition.2.2.1] at read
    exact (Except.ok.inj read).symm
  refine ⟨result, exchanged, old, ?_, Atomics.exchange_wellFormed _ _ _ _ _ valid exchanged⟩
  exact actual.2.2.2.trans (by rw [memory, address]; exact transition.2.2.2.symm)

end EDSL.OS.Futex.Storage
