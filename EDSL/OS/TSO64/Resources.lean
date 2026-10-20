/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.Queue.Entry

namespace EDSL.OS.TSO64
open X86 AddressSpace

abbrev Profile := Queue.Profile
abbrev Pending := Queue.Entry

def payload (pending : List Pending) : Buffer := Queue.payload pending

def ResourcesValid (world : World) (resources : Resources) : Prop :=
  LeaseCurrent world resources.actor resources.code ∧
  LeaseCurrent world resources.actor resources.caller ∧
  resources.caller.loan.region = qwordRegion resources.callerAddress ∧
  (∀ ticket ∈ resources.grants, TicketCurrent world resources.actor ticket = true) ∧
  (∀ identifier ∈ resources.atomics, (Atomics64.authorize world resources.actor identifier).isOk = true)

def PendingValid (world : World) (resources : Resources) (pending : Pending)
    (profile : Profile := .ownedOnly) : Prop := Queue.Valid world resources pending profile

instance (world : World) (resources : Resources) (pending : Pending) (profile : Profile) :
    Decidable (PendingValid world resources pending profile) :=
  inferInstanceAs (Decidable (Queue.Valid world resources pending profile))

/-- Metadata and permissions fixed by this scheduler. No release, protect,
transfer, enrollment, revocation, loan finishing, or external write action is
provided during a run. Stability is proved for publication, never admitted as
a desired successor condition. Byte values may change. -/
structure Stable (before after : World) : Prop where
  allocations : after.legacy.shared.resources.allocations = before.legacy.shared.resources.allocations
  frontier : after.legacy.shared.resources.frontier = before.legacy.shared.resources.frontier
  loans : after.legacy.shared.loans = before.legacy.shared.loans
  nextLoan : after.legacy.shared.nextLoan = before.legacy.shared.nextLoan
  cells : after.cells = before.cells
  nextCell : after.nextCell = before.nextCell
  handles : after.handles = before.handles
  nextHandle : after.nextHandle = before.nextHandle
  legacyHandles : after.legacy.handles = before.legacy.handles
  legacyNextHandle : after.legacy.nextHandle = before.legacy.nextHandle
  permissions : ∀ query, (after.legacy.shared.resources.space.cells query).map Cell.permissions =
    (before.legacy.shared.resources.space.cells query).map Cell.permissions

theorem Stable.refl (world : World) : Stable world world :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩

theorem Stable.ownsRegion {before after : World} (frame : Stable before after)
    (actor : Nat) (ticket : Ownership.Ticket) (region : Region) :
    OwnsRegion after actor ticket region ↔ OwnsRegion before actor ticket region := by
  simp only [OwnsRegion, frame.allocations]

theorem Stable.ticketCurrent {before after : World} (frame : Stable before after)
    (actor : Nat) (ticket : Ownership.Ticket) :
    TicketCurrent after actor ticket = TicketCurrent before actor ticket := by
  simp only [TicketCurrent, Ownership.authorize, frame.allocations]

theorem Stable.memory {before after : World} (frame : Stable before after) (query : Word) :
    (published after).writable query = (published before).writable query ∧
    ((published after).read query).isSome = ((published before).read query).isSome ∧
    (published after).executable query = (published before).executable query := by
  have same := frame.permissions query
  cases a : after.legacy.shared.resources.space.cells query <;>
    cases b : before.legacy.shared.resources.space.cells query <;>
    simp_all [published, toMemory]
  split <;> simp_all

theorem Stable.readable {before after : World} (frame : Stable before after) (region : Region) :
    Borrowing.allReadable after.legacy.shared.resources.space region =
      Borrowing.allReadable before.legacy.shared.resources.space region := by
  unfold Borrowing.allReadable
  congr 1
  funext query
  have same := frame.permissions query
  cases a : after.legacy.shared.resources.space.cells query <;>
    cases b : before.legacy.shared.resources.space.cells query <;> simp_all

theorem Stable.leaseCurrent {before after : World} (frame : Stable before after)
    (actor : Nat) (lease : Lease) : LeaseCurrent after actor lease ↔ LeaseCurrent before actor lease := by
  simp only [LeaseCurrent, frame.loans, frame.ownsRegion, frame.readable]

theorem Stable.storeGate {before after : World} (frame : Stable before after)
    (actor : Nat) (ticket : Ownership.Ticket) (store : Store) :
    StoreGate after actor ticket store ↔ StoreGate before actor ticket store := by
  have scalarEq : scalar (published after) store = scalar (published before) store := by
    cases store.value <;>
      simp only [scalar, canStoreDWord, dwordWritable, canStoreQWord, qwordWritable,
        (frame.memory _).1, (frame.memory _).2.1]
  have dataEq : dataOnly (published after) store = dataOnly (published before) store := by
    simp only [dataOnly, (frame.memory _).2.2]
  simp only [StoreGate, frame.ownsRegion, scalarEq, dataEq,
    Atomics64.reserved, frame.cells, frame.nextCell, Atomics.reserved,
    frame.legacyHandles, frame.legacyNextHandle, Borrowing.allowed, frame.loans, frame.nextLoan]

theorem Stable.authorize {before after : World} (frame : Stable before after)
    (actor : Nat) (identifier : Atomics64.HandleId64) :
    Atomics64.authorize after actor identifier = Atomics64.authorize before actor identifier := by
  have validate (cell : Atomics64.Cell) : Atomics64.validateCell after cell = Atomics64.validateCell before cell := by
    simp only [Atomics64.validateCell, Ownership.authorize, frame.allocations,
      Borrowing.canStoreQWord_permissions frame.permissions, Atomics64.dataOnly64_permissions frame.permissions]
  simp only [Atomics64.authorize, frame.handles, Atomics64.currentCell, frame.cells, validate]

theorem Stable.resources {before after : World} (frame : Stable before after)
    {resources : Resources} (valid : ResourcesValid before resources) : ResourcesValid after resources :=
  ⟨(frame.leaseCurrent _ _).mpr valid.1, (frame.leaseCurrent _ _).mpr valid.2.1,
    valid.2.2.1, (fun ticket member => (frame.ticketCurrent _ _).trans (valid.2.2.2.1 ticket member)),
    fun identifier member => by rw [frame.authorize]; exact valid.2.2.2.2 identifier member⟩

theorem Stable.pending {before after : World} (frame : Stable before after)
    {resources : Resources} {pending : Pending} {profile : Profile}
    (valid : PendingValid before resources pending profile) :
    PendingValid after resources pending profile := by
  cases pending with
  | ordinary ticket store => exact ⟨valid.1, (frame.storeGate _ _ _).mpr valid.2⟩
  | managed reference value occurrence =>
      refine ⟨valid.1, valid.2.1, ?_⟩
      rw [frame.authorize]
      exact valid.2.2

theorem fetchAdd_stable {world : World} {actor : Nat} {identifier : Atomics64.HandleId64}
    {delta : Word} {result : World × Atomics64.FetchAddEvent}
    (success : Atomics64.fetchAdd world actor identifier delta = .ok result) : Stable world result.1 := by
  have effect := Atomics64.fetchAdd_effect _ _ _ _ _ success
  exact ⟨effect.shared.allocations, effect.shared.frontier, effect.shared.loans, effect.shared.nextLoan,
    effect.cells, effect.nextCell, effect.handles, effect.nextHandle,
    effect.legacyHandles, effect.legacyNextHandle, effect.shared.permissions⟩

end EDSL.OS.TSO64
