/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.LoanFrames

namespace EDSL.OS.Futex.Clients
open X86 AddressSpace

private theorem store_permissions {before after : Ownership.World}
    {owner : Nat} {ticket : Ownership.Ticket} {address : Word} {value : BitVec 32}
    (success : Ownership.storeWord before owner ticket address value = .ok after) :
    ∀ query, (after.space.cells query).map Cell.permissions =
      (before.space.cells query).map Cell.permissions := by
  obtain ⟨_, _, _, _, stored, same⟩ := Ownership.storeWord_ok _ _ _ _ _ _ success
  rw [same]
  exact (AddressSpace.storeWord_sound _ _ _ _ stored).2.2.1

private theorem publish_permissions {before after : Atomics.State} {grant : Storage.Grant}
    {value : BitVec 32} (success : Storage.publish before grant value = .ok after) :
    ∀ query, (after.shared.resources.space.cells query).map Cell.permissions =
      (before.shared.resources.space.cells query).map Cell.permissions := by
  cases mutation : Atomics.mutate before (.store grant.owner grant.ticket grant.address value) with
  | error fault => simp [Storage.publish, mutation] at success
  | ok result =>
    simp [Storage.publish, mutation] at success
    subst after
    obtain ⟨_, _, modified, same⟩ := Atomics.mutate_ok _ _ _ mutation
    obtain ⟨_, resources, owned, sharedEq⟩ := Borrowing.mutate_ok _ _ _ modified
    cases stored : Ownership.storeWord before.shared.resources grant.owner grant.ticket grant.address value with
    | error fault => simp [Ownership.Mutation.run, stored, Except.map] at owned
    | ok world =>
      simp [Ownership.Mutation.run, stored, Except.map] at owned
      subst resources
      rw [same, sharedEq]
      exact store_permissions stored

private theorem exchange_permissions {before : Atomics.State} {result : Atomics.State × BitVec 32}
    {actor identifier : Nat} {value : BitVec 32}
    (success : Atomics.exchange before actor identifier value = .ok result) :
    ∀ query, (result.1.shared.resources.space.cells query).map Cell.permissions =
      (before.shared.resources.space.cells query).map Cell.permissions := by
  obtain ⟨handle, _, _, exchanged, same⟩ := Atomics.exchange_ok _ _ _ _ _ success
  obtain ⟨_, resources, owned, sharedEq⟩ := Borrowing.mutate_ok _ _ _
    (AtomicExchange.exchangeWord_guarded _ _ _ _ _ _ exchanged)
  cases stored : Ownership.storeWord before.shared.resources handle.owner handle.ticket handle.address value with
  | error fault => simp [Ownership.Mutation.run, stored, Except.map] at owned
  | ok world =>
    simp [Ownership.Mutation.run, stored, Except.map] at owned
    subst resources
    have shared := congrArg Prod.fst sharedEq
    dsimp only at shared
    rw [same, shared]
    exact store_permissions stored

/-- Convert disjoint nonwrapping owned regions to the modular four-byte
footprint used by buffered execution, for every byte of the protected region. -/
private theorem allocation_disjoint {world : Ownership.World} {allocation : Ownership.Allocation}
    {identifier : Nat} {address : Word} {region : Region}
    (valid : Ownership.WellFormed world)
    (live : world.allocations identifier = some allocation)
    (fits : Ownership.containsWord allocation address = true)
    (regionValid : region.valid = true) (separate : Ownership.Disjoint allocation.region region) :
    DWordDisjoint address region.base region.length := by
  have allocationValid := (valid.1 _ _ live).2.1
  have limits := (of_decide_eq_true allocationValid).2.1
  have bounds := of_decide_eq_true fits
  have noWrap : address.toNat + 3 < 2^64 := by
    change allocation.region.base.toNat ≤ address.toNat ∧
      address.toNat + 4 ≤ allocation.region.base.toNat + allocation.region.length at bounds
    omega
  intro offset bound
  have inside : region.Contains (region.base + BitVec.ofNat 64 offset) :=
    Ownership.addresses_inside region regionValid _
      (List.mem_map.mpr ⟨offset, List.mem_range.mpr bound, rfl⟩)
  have outside := Ownership.disjoint_outside separate inside
  have notSmall : ¬ ((region.base + BitVec.ofNat 64 offset) - address).toNat < 4 := by
    intro small
    exact outside (Ownership.containsWord_inside allocation address _ fits
      ((word_contains_iff address _ noWrap).mpr small))
  omega

private theorem separate_of_disjoint {left right : Word}
    (disjoint : DWordDisjoint left right 4) : StoreBuffer.Separate left right := by
  intro query
  by_cases outside : 4 ≤ (query - right).toNat
  · exact Or.inr outside
  · have inside : (query - right).toNat < 4 := by omega
    have framed := disjoint (query - right).toNat inside
    rw [← AddressSpace.query_of_offset right query _ rfl] at framed
    exact Or.inl framed

end EDSL.OS.Futex.Clients

namespace EDSL.OS.Futex.Physical
open X86 AddressSpace

/-- Checked physical replay preserves every mapped permission. Values may
change at a real drain or exchange; no replay enabledness is assumed here. -/
theorem synchronize_permissions (profile : Profile) (authority next : Atomics.State)
    (observation : Suspend.Observation)
    (success : synchronize profile authority observation = .ok next) :
    ∀ query, (next.shared.resources.space.cells query).map Cell.permissions =
      (authority.shared.resources.space.cells query).map Cell.permissions := by
  cases observation with
  | machine observed =>
    cases observed with
    | drained worker store =>
      cases atGrant : profile.payload worker with
      | none => simp [synchronize, atGrant] at success
      | some grant =>
        by_cases address : grant.address = store.address
        · cases published : Storage.publish authority grant store.value with
          | error fault => simp [synchronize, atGrant, address, published, Except.mapError] at success
          | ok result =>
            simp [synchronize, atGrant, address, published, Except.mapError] at success
            subst next
            exact Clients.publish_permissions published
        · simp [synchronize, atGrant, address] at success
    | retired worker event =>
      cases event with
      | none =>
        simp only [synchronize, Except.ok.injEq] at success
        subst next
        exact fun _ => rfl
      | some event =>
        cases atAccess : profile.atomic worker with
        | none => simp [synchronize, atAccess] at success
        | some access =>
          cases authorized : Atomics.authorize authority access.actor access.handle with
          | error fault => simp [synchronize, atAccess, authorized, Except.mapError] at success
          | ok handle =>
            by_cases address : handle.address = event.address
            · cases exchanged : Atomics.exchange authority access.actor access.handle event.after with
              | error fault =>
                simp [synchronize, atAccess, authorized, address, exchanged, Except.mapError] at success
              | ok result =>
                by_cases old : result.2 = event.before
                · simp [synchronize, atAccess, authorized, address, exchanged, old, Except.mapError] at success
                  subst next
                  exact Clients.exchange_permissions exchanged
                · simp [synchronize, atAccess, authorized, address, exchanged, old, Except.mapError] at success
            · simp [synchronize, atAccess, authorized, address, Except.mapError] at success
    | blocked worker =>
      simp only [synchronize, Except.ok.injEq] at success
      subst next
      exact fun _ => rfl
  | entered worker invocation | parked worker invocation | resumed worker invocation raw | idle =>
    simp only [synchronize, Except.ok.injEq] at success
    subst next
    exact fun _ => rfl

end EDSL.OS.Futex.Physical

namespace EDSL.OS.Futex.Storage
open X86 AddressSpace

/-- Grant validity depends on current allocation metadata, the complete loan
and handle registries with their scan frontiers, and mapped permissions. Byte
values and the ownership allocation frontier are irrelevant to this contract. -/
theorem Grant.Valid.frame {before after : Atomics.State} {grant : Grant}
    (ready : grant.Valid before)
    (allocations : after.shared.resources.allocations = before.shared.resources.allocations)
    (loans : after.shared.loans = before.shared.loans)
    (nextLoan : after.shared.nextLoan = before.shared.nextLoan)
    (handles : after.handles = before.handles)
    (nextHandle : after.nextHandle = before.nextHandle)
    (permissions : ∀ query, (after.shared.resources.space.cells query).map Cell.permissions =
      (before.shared.resources.space.cells query).map Cell.permissions) : grant.Valid after := by
  obtain ⟨allocation, authorized, fits, writable, unreserved, unborrowed⟩ := ready
  refine ⟨allocation, ?_, fits, ?_, ?_, ?_⟩
  · simpa only [Ownership.authorize, allocations] using authorized
  · rw [Atomics.canStore_permissions permissions]
    exact writable
  · simpa only [Atomics.allowed, nextHandle, handles] using unreserved
  · simpa only [Borrowing.allowed, nextLoan, loans] using unborrowed

/-- Every actual checked replay retains every current grant, independently
of the producer's returned bit and of every worker's pending FIFO. -/
theorem Grant.Valid.synchronize {profile : Physical.Profile} {before after : Atomics.State}
    {observation : Suspend.Observation} {grant : Grant} (ready : grant.Valid before)
    (success : Physical.synchronize profile before observation = .ok after) : grant.Valid after := by
  obtain ⟨handles, nextHandle, loans, nextLoan, allocations, _⟩ :=
    Physical.synchronize_frames _ _ _ _ success
  exact ready.frame allocations loans nextLoan handles nextHandle
    (Physical.synchronize_permissions _ _ _ _ success)

/-- Installing a reservation for another allocation cannot revoke an ordinary
write grant. Actual call installation supplies freshness and compatibility. -/
theorem Grant.Valid.install_other {state : Atomics.State} {grant : Grant}
    (ready : grant.Valid state) (handle : Atomics.Handle)
    (different : handle.ticket.identifier ≠ grant.ticket.identifier) :
    grant.Valid (Atomics.install state handle) := by
  obtain ⟨allocation, authorized, fits, writable, unreserved, unborrowed⟩ := ready
  refine ⟨allocation, authorized, fits, writable, ?_, unborrowed⟩
  apply List.all_eq_true.mpr
  intro identifier member
  have below := List.mem_range.mp member
  change identifier < state.nextHandle + 1 at below
  by_cases fresh : identifier = state.nextHandle
  · simp [Atomics.install, fresh, Ownership.Mutation.target, Ne.symm different]
  · have old : identifier < state.nextHandle := by omega
    have checked := List.all_eq_true.mp unreserved identifier (List.mem_range.mpr old)
    simpa [Atomics.install, fresh] using checked

/-- Closing an actual authorized handle only removes a reservation. It does
not revoke an ordinary grant, even when the actor labels coincide. -/
theorem Grant.Valid.close {before after : Atomics.State} {grant : Grant}
    {actor identifier : Nat} (ready : grant.Valid before)
    (success : Atomics.close before actor identifier = .ok after) : grant.Valid after := by
  obtain ⟨_, _, same⟩ := Atomics.close_ok _ _ _ _ success
  subst after
  obtain ⟨allocation, authorized, fits, writable, unreserved, unborrowed⟩ := ready
  refine ⟨allocation, authorized, fits, writable, ?_, unborrowed⟩
  apply List.all_eq_true.mpr
  intro query member
  by_cases removed : query = identifier
  · simp [removed]
  · simpa [removed] using List.all_eq_true.mp unreserved query member

/-- Current publication authority excludes every live reserved allocation.
This derives ticket separation from the actual Atomics gate. -/
theorem Grant.Valid.different_handle_ticket {state : Atomics.State} {grant : Grant}
    (ready : grant.Valid state) (valid : Atomics.WellFormed state)
    {identifier : Nat} {handle : Atomics.Handle} (live : state.handles identifier = some handle) :
    grant.ticket.identifier ≠ handle.ticket.identifier := by
  obtain ⟨_, _, _, _, unreserved, _⟩ := ready
  have different := Atomics.allowed_sound state (.store grant.owner grant.ticket grant.address 0)
    valid unreserved identifier handle live
  simpa only [Ownership.Mutation.target, ne_eq, Option.some.injEq] using different

theorem Grant.Valid.different_keeper_ticket {state : Atomics.State} {grant : Grant}
    {registration : Resources.Registration} (ready : grant.Valid state)
    (valid : Atomics.WellFormed state) (live : Resources.Valid state registration) :
    grant.ticket.identifier ≠ registration.ticket.identifier :=
  ready.different_handle_ticket valid live

/-- Current borrowing permission excludes the allocation of every live loan,
including loans for a different subregion of that allocation. -/
theorem Grant.Valid.different_loan_ticket {state : Atomics.State} {grant : Grant}
    (ready : grant.Valid state) (valid : Atomics.WellFormed state)
    {identifier : Nat} {loan : Borrowing.Loan} (live : state.shared.loans identifier = some loan) :
    grant.ticket.identifier ≠ loan.ticket.identifier := by
  obtain ⟨_, _, _, _, _, unborrowed⟩ := ready
  have different := Borrowing.allowed_sound state.shared (.store grant.owner grant.ticket grant.address 0)
    valid.shared unborrowed identifier loan live
  simpa only [Ownership.Mutation.target, ne_eq, Option.some.injEq] using different

/-- All four written bytes miss the whole current loan, including all eight
bytes of a return stack and code regions of arbitrary supported length. -/
theorem Grant.Valid.disjoint_loan {state : Atomics.State} {grant : Grant}
    (ready : grant.Valid state) (valid : Atomics.WellFormed state)
    {identifier : Nat} {loan : Borrowing.Loan} (live : state.shared.loans identifier = some loan) :
    DWordDisjoint grant.address loan.region.base loan.region.length := by
  have different := ready.different_loan_ticket valid live
  obtain ⟨allocation, authorized, fits, _⟩ := ready
  have found := (Ownership.authorize_ok _ _ _ _ authorized).1
  obtain ⟨other, otherAt, _, _, subregion, regionValid, _⟩ := (valid.shared.2 _ _ live).2
  have separate := valid.shared.1.2 _ _ _ _ found otherAt different
  apply Clients.allocation_disjoint valid.shared.1 found fits regionValid
  rcases separate with before | after
  · exact Or.inl (by have := subregion.1; omega)
  · exact Or.inr (by have := subregion.2; omega)

theorem Grant.Valid.disjoint_hasLoan {state : Atomics.State} {grant : Grant}
    (ready : grant.Valid state) (valid : Atomics.WellFormed state)
    {subject identifier : Nat} {region : Region}
    (held : Threads.HasLoan state.shared subject identifier region) :
    DWordDisjoint grant.address region.base region.length := by
  obtain ⟨loan, live, _, same⟩ := held
  rw [← same]
  exact ready.disjoint_loan valid live

theorem Grant.Valid.disjoint_handle_word {state : Atomics.State} {grant : Grant}
    (ready : grant.Valid state) (valid : Atomics.WellFormed state)
    {identifier : Nat} {handle : Atomics.Handle} (live : state.handles identifier = some handle) :
    DWordDisjoint grant.address handle.address 4 := by
  have different := ready.different_handle_ticket valid live
  obtain ⟨allocation, authorized, fits, _⟩ := ready
  have found := (Ownership.authorize_ok _ _ _ _ authorized).1
  obtain ⟨other, otherAt, _, _, otherFits, _, _⟩ := (valid.handles _ _ live).2
  have separate := valid.shared.1.2 _ _ _ _ found otherAt different
  have otherBounds := of_decide_eq_true otherFits
  change other.region.base.toNat ≤ handle.address.toNat ∧
    handle.address.toNat + 4 ≤ other.region.base.toNat + other.region.length at otherBounds
  have regionValid : (wordRegion handle.address).valid = true := by
    have otherValid := of_decide_eq_true (valid.shared.1.1 _ _ otherAt).2.1
    change decide (0 < 4 ∧ handle.address.toNat + 4 ≤ 2^64 ∧
      (handle.address.toNat + 4 ≤ 2^47 ∨ 2^64 - 2^47 ≤ handle.address.toNat)) = true
    apply decide_eq_true_eq.mpr
    omega
  apply Clients.allocation_disjoint valid.shared.1 found fits regionValid
  rcases separate with before | after
  · exact Or.inl (by change allocation.region.base.toNat + allocation.region.length ≤ handle.address.toNat; omega)
  · exact Or.inr (by change handle.address.toNat + 4 ≤ allocation.region.base.toNat; omega)

theorem Grant.Valid.disjoint_keeper_word {state : Atomics.State} {grant : Grant}
    {registration : Resources.Registration} (ready : grant.Valid state)
    (valid : Atomics.WellFormed state) (live : Resources.Valid state registration) :
    DWordDisjoint grant.address registration.address 4 :=
  ready.disjoint_handle_word valid live

/-- The same four-byte exclusion in the symmetric form used to commute
atomic exchange with an independently buffered ordinary write. -/
theorem Grant.Valid.separate_handle_word {state : Atomics.State} {grant : Grant}
    (ready : grant.Valid state) (valid : Atomics.WellFormed state)
    {identifier : Nat} {handle : Atomics.Handle} (live : state.handles identifier = some handle) :
    StoreBuffer.Separate grant.address handle.address :=
  Clients.separate_of_disjoint (ready.disjoint_handle_word valid live)

theorem Grant.Valid.separate_keeper_word {state : Atomics.State} {grant : Grant}
    {registration : Resources.Registration} (ready : grant.Valid state)
    (valid : Atomics.WellFormed state) (live : Resources.Valid state registration) :
    StoreBuffer.Separate grant.address registration.address :=
  ready.separate_handle_word valid live

/-- Actual fresh, compatible W-call retention preserves ordinary payload
authority; separation is derived from the live keeper, never supplied by replay. -/
theorem Grant.Valid.retainCall {before : Atomics.State} {result : Atomics.State × Nat}
    {registration : Resources.Registration} {actor : Nat} {grant : Grant}
    (ready : grant.Valid before) (valid : Atomics.WellFormed before)
    (success : Resources.retainCall before registration actor = .ok result) : grant.Valid result.1 := by
  have keeper := (Resources.retainCall_ok _ _ _ _ success).1
  have different := ready.different_keeper_ticket valid keeper
  have same := Except.ok.inj
    ((Resources.retainCall_enabled before registration actor valid keeper).symm.trans success)
  rw [← same]
  exact ready.install_other _ (Ne.symm different)

theorem Grant.Valid.closeCall {before after : Atomics.State}
    {registration : Resources.Registration} {actor identifier : Nat} {grant : Grant}
    (ready : grant.Valid before)
    (success : Resources.closeCall before registration actor identifier = .ok after) : grant.Valid after :=
  ready.close (Resources.closeCall_ok _ _ _ _ _ success).2.2

end EDSL.OS.Futex.Storage

namespace EDSL.OS.Futex.Clients
open X86 AddressSpace

theorem captureEntered_grant {config : Config} {before after : State}
    {worker invocation : Nat} {grant : Storage.Grant}
    (valid : Atomics.WellFormed before.authority) (ready : grant.Valid before.authority)
    (success : captureEntered config before worker invocation = .ok after) :
    grant.Valid after.authority := by
  obtain ⟨_, _, registration, _, _, _, _, _, _, _, _, retained, same⟩ := captureEntered_effect success
  rw [same]
  exact ready.retainCall valid retained

theorem resumeReady_grant {config : Config} {before after : State}
    {invocation : Nat} {flags rcx r11 : Word} {grant : Storage.Grant}
    (ready : grant.Valid before.authority)
    (success : resumeReady config before invocation flags rcx r11 = .ok after) :
    grant.Valid after.authority := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, closed, same⟩ := resumeReady_effect success
  rw [same]
  exact ready.closeCall closed

theorem service_grant {config : Config} {before after : State} {action : Futex.Action}
    {grant : Storage.Grant} (ready : grant.Valid before.authority)
    (success : Futex.step config before action = .ok after) : grant.Valid after.authority := by
  cases action with
  | compare invocation => rw [(compareWait_stutter success).2.1]; exact ready
  | wake invocation selected => rw [(wakeOne_stutter success).2.1]; exact ready
  | retry invocation => rw [(retryQueued_stutter success).2.1]; exact ready
  | spurious invocation => rw [(spuriousReady_stutter success).2.1]; exact ready
  | resume invocation flags rcx r11 => exact resumeReady_grant ready success
  | idle => simp [Futex.step] at success; subst after; exact ready

/-- Resource interpretation of actual checked issue, including fresh syscall
capture. No completed-worker or empty-peer-buffer premise is imposed. -/
theorem issue_grant {profile : Physical.Profile} {before : State} {worker : Nat}
    {result : State × Suspend.Observation} {grant : Storage.Grant}
    (valid : Atomics.WellFormed before.authority) (ready : grant.Valid before.authority)
    (success : Physical.issue profile before worker = .ok result) : grant.Valid result.1.authority := by
  cases issued : Suspend.issue before.suspended worker with
  | error fault => simp [Physical.issue, issued, Except.mapError] at success
  | ok actual =>
    rcases actual with ⟨suspended, observation⟩
    cases synced : Physical.synchronize profile before.authority observation with
    | error fault => simp [Physical.issue, issued, synced, Except.mapError] at success
    | ok authority =>
      have framed := ready.synchronize synced
      cases observation with
      | entered selected invocation =>
        have authorityEq : authority = before.authority := by
          simpa [Physical.synchronize] using synced.symm
        subst authority
        cases captured : captureEntered profile.service { before with suspended := suspended } selected invocation with
        | error fault =>
          simp [Physical.issue, issued, Physical.synchronize, captured, Except.mapError] at success
        | ok after =>
          simp [Physical.issue, issued, Physical.synchronize, captured, Except.mapError] at success
          subst result
          exact captureEntered_grant (before := { before with suspended := suspended }) valid ready captured
      | machine observed =>
        simp [Physical.issue, issued, synced, Except.mapError] at success
        subst result
        exact framed
      | parked selected invocation | resumed selected invocation raw | idle =>
        simp [Physical.issue, issued, Physical.synchronize, Except.mapError] at success
        subst result
        exact ready

theorem drain_grant {profile : Physical.Profile} {before : State} {worker : Nat}
    {result : State × Suspend.Observation} {grant : Storage.Grant}
    (ready : grant.Valid before.authority)
    (success : Physical.drain profile before worker = .ok result) : grant.Valid result.1.authority := by
  cases drained : Suspend.drain before.suspended worker with
  | error fault => simp [Physical.drain, drained, Except.mapError] at success
  | ok actual =>
    cases synced : Physical.synchronize profile before.authority actual.2 with
    | error fault => simp [Physical.drain, drained, synced, Except.mapError] at success
    | ok authority =>
      simp [Physical.drain, drained, synced, Except.mapError] at success
      subst result
      exact ready.synchronize synced

theorem runtime_step_grant {profile : Physical.Profile} {before : State}
    {action : Runtime.Action} {result : State × Runtime.Observation} {grant : Storage.Grant}
    (valid : Runtime.Invariant profile before) (ready : grant.Valid before.authority)
    (success : Runtime.step profile before action = .ok result) : grant.Valid result.1.authority := by
  cases action with
  | issue worker =>
    cases issued : Physical.issue profile before worker with
    | error fault => simp [Runtime.step, issued] at success
    | ok actual =>
      simp [Runtime.step, issued] at success
      subst result
      exact issue_grant valid.service.authority ready issued
  | drain worker =>
    cases drained : Physical.drain profile before worker with
    | error fault => simp [Runtime.step, drained] at success
    | ok actual =>
      simp [Runtime.step, drained] at success
      subst result
      exact drain_grant ready drained
  | service action =>
    cases serviced : Futex.step profile.service before action with
    | error fault => simp [Runtime.step, serviced, Except.mapError] at success
    | ok after =>
      simp [Runtime.step, serviced, Except.mapError] at success
      subst result
      exact service_grant ready serviced

/-- An actual accepted mixed prefix retains all original ordinary grants,
including grants of returned producers with undrained FIFO entries. -/
theorem runtime_trace_grant {profile : Physical.Profile} {before after : State}
    {actions : List Runtime.Action} {observations : List Runtime.Observation} {grant : Storage.Grant}
    (valid : Runtime.Invariant profile before) (ready : grant.Valid before.authority)
    (trace : Runtime.Trace profile before actions observations after) : grant.Valid after.authority := by
  induction trace with
  | nil => exact ready
  | cons first tail ih =>
    exact ih (Runtime.step_invariant valid first).1 (runtime_step_grant valid ready first)

theorem runtime_schedule_grant {profile : Physical.Profile} {before : State}
    {actions : List Runtime.Action} {result : State × List Runtime.Observation} {grant : Storage.Grant}
    (valid : Runtime.Invariant profile before) (ready : grant.Valid before.authority)
    (success : Runtime.schedule profile before actions = .ok result) : grant.Valid result.1.authority :=
  runtime_trace_grant valid ready (Runtime.schedule_trace _ _ _ _ success)

/-- Positive call retention and retained payload authority follow from the
current keeper and grant, without a future successful resource-operation premise. -/
theorem retainCall_grant_enabled {state : Atomics.State} {registration : Resources.Registration}
    {grant : Storage.Grant} (valid : Atomics.WellFormed state)
    (keeper : Resources.Valid state registration) (ready : grant.Valid state) (actor : Nat) :
    Resources.retainCall state registration actor =
      .ok (Atomics.install state (registration.callHandle actor), state.nextHandle) ∧
      grant.Valid (Atomics.install state (registration.callHandle actor)) :=
  ⟨Resources.retainCall_enabled _ _ _ valid keeper,
    ready.install_other _ (Ne.symm (ready.different_keeper_ticket valid keeper))⟩

end EDSL.OS.Futex.Clients
