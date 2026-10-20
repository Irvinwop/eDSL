/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.Invariant

namespace EDSL.OS.TSO64
open X86 AddressSpace

theorem dataOnly_outside {memory : Memory} {store : Store} {query : Word}
    (data : dataOnly memory store = true) (code : memory.executable query = true) :
    store.width ≤ (query - store.address).toNat := by
  by_cases outside : store.width ≤ (query - store.address).toNat
  · exact outside
  have bound : (query - store.address).toNat < store.width := by omega
  have disabled := List.all_eq_true.mp data _ (List.mem_range.mpr bound)
  have location : store.address + BitVec.ofNat 64 (query - store.address).toNat = query := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  rw [location, code] at disabled
  contradiction

theorem dataOnly_code_disjoint {memory : Memory} {store : Store} {base : Word} {bytes : List Byte}
    (data : dataOnly memory store = true) (code : CodeAt memory base bytes) :
    store.Disjoint base bytes.length := by
  intro offset bound
  let byte := bytes[offset]'bound
  have fetched := code.2 offset byte (List.getElem?_eq_getElem bound)
  unfold fetchByte at fetched
  split at fetched
  next allowed => exact dataOnly_outside data (Bool.and_eq_true_iff.mp allowed).2
  next => cases fetched

theorem dataOnly_preserves_code {memory : Memory} {store : Store} {base : Word} {bytes : List Byte}
    (data : dataOnly memory store = true) (code : CodeAt memory base bytes) :
    CodeAt (store.publish memory) base bytes := by
  change CodeAt (StoreBuffer.Mixed.view memory [store]) base bytes
  apply StoreBuffer.Mixed.view_code _ _ _ _ code
  intro other member
  have same := List.mem_singleton.mp member
  subst other
  exact dataOnly_code_disjoint data code

theorem StoreGate.loan_disjoint {world : World} {actor : Nat} {ticket : Ownership.Ticket} {store : Store}
    (valid : Atomics64.WellFormed world) (gate : StoreGate world actor ticket store)
    {identifier : Nat} {loan : Borrowing.Loan} (live : world.legacy.shared.loans identifier = some loan) :
    store.Disjoint loan.region.base loan.region.length := by
  obtain ⟨owns, scalarGate, _, _, _, noLoan⟩ := gate
  obtain ⟨allocation, authorized, fits⟩ := owns.authorize
  obtain ⟨found, owner, epoch⟩ := Ownership.authorize_ok _ _ _ _ authorized
  have excluded := Borrowing.allowed_sound _ _ valid.legacy.shared noLoan identifier loan live
  have different : ticket.identifier ≠ loan.ticket.identifier := by
    cases value : store.value <;>
      simpa only [operation, value, Ownership.Mutation.target, ne_eq, Option.some.injEq] using excluded
  cases store with
  | mk address value =>
    cases value with
    | dword value =>
      have word : Mutex.WordValid world.legacy.shared actor ticket address :=
        ⟨allocation, found, owner, epoch, decide_eq_true fits, (Bool.and_eq_true_iff.mp scalarGate).2⟩
      exact WordResources.word_loan_disjoint valid.legacy.shared word live different
    | qword value =>
      have word : WordResources64.WordValid world.legacy.shared actor ticket address :=
        ⟨allocation, found, owner, epoch, decide_eq_true fits, (Bool.and_eq_true_iff.mp scalarGate).2⟩
      exact WordResources64.word_loan_disjoint valid.legacy.shared word live different

theorem Queue.Current.cell {world : World} {resources : Resources} {reference : Queue.ManagedRef}
    (current : Queue.Current world resources reference) :
    world.cells reference.handle.cell = some reference.cell :=
  (Atomics64.authorize_ok _ _ _ _ current.2).2.2.1

theorem Queue.Current.validCell {world : World} {resources : Resources} {reference : Queue.ManagedRef}
    (current : Queue.Current world resources reference) :
    Atomics64.ValidCell world.legacy.shared reference.cell :=
  (Atomics64.authorize_ok _ _ _ _ current.2).2.2.2

/-- Current managed authority separates its entire allocation from every live
loan. The retained descriptor alone, without the world invariant, is insufficient. -/
theorem Queue.Current.loan_disjoint {world : World} {resources : Resources}
    {reference : Queue.ManagedRef} (current : Queue.Current world resources reference)
    (valid : Atomics64.WellFormed world) {identifier : Nat} {loan : Borrowing.Loan}
    (live : world.legacy.shared.loans identifier = some loan) :
    QWordDisjoint reference.cell.address loan.region.base loan.region.length :=
  Atomics64.cell_loan_disjoint world valid reference.handle.cell reference.cell current.cell
    identifier loan live

theorem PendingValid.loan_disjoint {world : World} {resources : Resources}
    {entry : Pending} {profile : Profile} (entryValid : PendingValid world resources entry profile)
    (valid : Atomics64.WellFormed world) {identifier : Nat} {loan : Borrowing.Loan}
    (live : world.legacy.shared.loans identifier = some loan) :
    entry.store.Disjoint loan.region.base loan.region.length := by
  cases entry with
  | ordinary ticket store => exact entryValid.2.loan_disjoint valid live
  | managed reference value occurrence => exact entryValid.2.loan_disjoint valid live

theorem PendingValid.dataOnly {world : World} {resources : Resources}
    {entry : Pending} {profile : Profile} (valid : PendingValid world resources entry profile) :
    dataOnly (published world) entry.store = true := by
  cases entry with
  | ordinary ticket store => exact valid.2.2.2.1
  | managed reference value occurrence =>
    change (List.range 8).all (fun offset =>
      !(published world).executable (reference.cell.address + BitVec.ofNat 64 offset)) = true
    apply List.all_eq_true.mpr
    intro offset member
    have byte := dataOnly64_bytes (published world) reference.cell.address
      valid.2.validCell.2.2 offset (List.mem_range.mp member)
    simpa only [Bool.not_eq_true'] using byte

private theorem store_disjoint_of_allocations {world : Ownership.World} {left right : Nat}
    {allocation other : Ownership.Allocation} {store : Store} {address : Word}
    (valid : Ownership.WellFormed world)
    (found : world.allocations left = some allocation)
    (otherFound : world.allocations right = some other)
    (fits : Borrowing.Subregion ⟨store.address, store.width⟩ allocation.region)
    (otherFits : Ownership.containsQWord other address = true) (different : left ≠ right) :
    store.Disjoint address 8 := by
  have separate := valid.2 _ _ _ _ found otherFound different
  have limit := (of_decide_eq_true (valid.1 _ _ found).2.1).2.1
  have otherLimit := (of_decide_eq_true (valid.1 _ _ otherFound).2.1).2.1
  have bounds : other.region.base.toNat ≤ address.toNat ∧
      address.toNat + 8 ≤ other.region.base.toNat + other.region.length :=
    of_decide_eq_true otherFits
  rcases fits with ⟨lower, upper⟩
  change allocation.region.base.toNat ≤ store.address.toNat at lower
  change store.address.toNat + store.width ≤ allocation.region.base.toNat + allocation.region.length at upper
  intro offset bound
  let query := address + BitVec.ofNat 64 offset
  have offsetSmall : offset < 2^64 := by omega
  have sumSmall : address.toNat + offset < 2^64 := by omega
  have queryNat : query.toNat = address.toNat + offset := by
    simp only [query, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt offsetSmall, Nat.mod_eq_of_lt sumSmall]
  have inside : other.region.Contains query := ⟨by omega, by omega⟩
  by_cases outside : store.width ≤ (query - store.address).toNat
  · exact outside
  have distance : (query - store.address).toNat < store.width := by omega
  have distanceSmall : (query - store.address).toNat < 2^64 := by omega
  have storeSumSmall : store.address.toNat + (query - store.address).toNat < 2^64 := by omega
  have location : store.address + BitVec.ofNat 64 (query - store.address).toNat = query := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  have storedNat : query.toNat = store.address.toNat + (query - store.address).toNat := by
    calc
      query.toNat = (store.address + BitVec.ofNat 64 (query - store.address).toNat).toNat :=
        congrArg BitVec.toNat location.symm
      _ = _ := by
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt distanceSmall, Nat.mod_eq_of_lt storeSumSmall]
  exact False.elim (Ownership.disjoint_outside separate inside ⟨by omega, by omega⟩)

/-- Ordinary authority excludes the full allocation of every currently managed
cell, including when that cell belongs to another worker or actor. -/
theorem StoreGate.managed_disjoint {world : World} {actor : Nat} {ticket : Ownership.Ticket}
    {store : Store} {resources : Resources} {reference : Queue.ManagedRef}
    (gate : StoreGate world actor ticket store) (valid : Atomics64.WellFormed world)
    (current : Queue.Current world resources reference) : store.Disjoint reference.cell.address 8 := by
  obtain ⟨allocation, authorized, fits⟩ := gate.1.authorize
  have found := (Ownership.authorize_ok _ _ _ _ authorized).1
  obtain ⟨other, otherFound, _, _, otherFits, _⟩ := current.validCell.1
  have different := (Atomics64.unreserved_sound world valid ticket.identifier gate.2.2.2.1
    reference.handle.cell reference.cell current.cell).symm
  exact store_disjoint_of_allocations valid.legacy.shared.1 found otherFound fits otherFits different

/-- Distinct persistent managed cells occupy distinct allocations. Equal cell
identities select the same entire qword, regardless of handle or actor aliases. -/
theorem Queue.Current.qwordCompatible {world : World} {resources otherResources : Resources}
    {reference other : Queue.ManagedRef} (current : Queue.Current world resources reference)
    (target : Queue.Current world otherResources other) (valid : Atomics64.WellFormed world)
    (value : Word) :
    StoreBuffer.Mixed.QWordCompatible other.cell.address ⟨reference.cell.address, .qword value⟩ := by
  by_cases same : reference.handle.cell = other.handle.cell
  · have found := current.cell
    rw [same] at found
    have cells : reference.cell = other.cell := Option.some.inj (found.symm.trans target.cell)
    exact .inl (congrArg Atomics64.Cell.address cells)
  · obtain ⟨allocation, found, _, _, fits, _⟩ := current.validCell.1
    obtain ⟨otherAllocation, otherFound, _, _, otherFits, _⟩ := target.validCell.1
    have different : reference.cell.ticket.identifier ≠ other.cell.ticket.identifier := by
      intro equal
      exact same (valid.unique _ _ _ _ current.cell target.cell equal)
    exact .inr (store_disjoint_of_allocations valid.legacy.shared.1 found otherFound
      (of_decide_eq_true fits) otherFits different)

theorem PendingValid.qwordCompatible {world : World} {resources targetResources : Resources}
    {entry : Pending} {profile : Profile} {reference : Queue.ManagedRef}
    (entryValid : PendingValid world resources entry profile) (valid : Atomics64.WellFormed world)
    (target : Queue.Current world targetResources reference) :
    StoreBuffer.Mixed.QWordCompatible reference.cell.address entry.store := by
  cases entry with
  | ordinary ticket store =>
    have separate := entryValid.2.managed_disjoint valid target
    cases store with
    | mk address value =>
      cases value with
      | dword value => exact separate
      | qword value => exact .inr separate
  | managed other value occurrence => exact entryValid.2.qwordCompatible target valid value

/-- Compatibility is derived from present resource invariants. It is never a
read-admission premise and cannot replace the current authorization check. -/
theorem WorkerValid.managed_compatible {world : World} {worker : Worker} {profile : Profile}
    {resources : Resources} {reference : Queue.ManagedRef}
    (workerValid : WorkerValid world worker profile) (valid : Atomics64.WellFormed world)
    (current : Queue.Current world resources reference) :
    StoreBuffer.Mixed.WholeQWordCompatible (payload worker.pending) reference.cell.address := by
  intro store member
  obtain ⟨entry, queued, same⟩ := List.mem_map.mp member
  subst store
  exact (workerValid.2 entry queued).qwordCompatible valid current

/-- The real Mixed load selects the newest matching whole qword, or the actual
published load result. This is a byte-semantics theorem, not an Atomics64.load
event for a forwarded value, nor an issue/history origin for a queue entry. -/
theorem local_managed_load {state : State} {worker : Worker} {profile : Profile}
    {resources : Resources} {reference : Queue.ManagedRef}
    (valid : WellFormed state profile) (workerValid : WorkerValid state.world worker profile)
    (current : Queue.Current state.world resources reference) :
    loadQWord (localCPU state worker).memory reference.cell.address =
      match StoreBuffer.Mixed.newestQWord (payload worker.pending) reference.cell.address with
      | some origin => .ok origin.value
      | none => loadQWord (published state.world) reference.cell.address :=
  StoreBuffer.Mixed.view_loadQWord_newestQWord _ _ _
    (Bool.and_eq_true_iff.mp current.validCell.2.1).1
    (workerValid.managed_compatible valid.1 current)

/-- Byte agreement with current RAM over ANY live loan, including every peer's
code and original caller slot. Own pending writes cannot shadow protected bytes. -/
theorem local_loan_agrees {state : State} {worker : Worker} {identifier : Nat} {loan : Borrowing.Loan}
    {profile : Profile} (valid : WellFormed state profile)
    (workerValid : WorkerValid state.world worker profile)
    (live : state.world.legacy.shared.loans identifier = some loan) :
    MemoryAgreesOn (localCPU state worker).memory (published state.world) loan.region.base loan.region.length := by
  apply StoreBuffer.Mixed.view_agrees
  intro store member
  obtain ⟨pending, queued, same⟩ := List.mem_map.mp member
  subst store
  exact (workerValid.2 pending queued).loan_disjoint valid.1 live

theorem local_original_caller {state : State} {worker : Worker}
    {profile : Profile} (valid : WellFormed state profile)
    (workerValid : WorkerValid state.world worker profile) :
    readWord (localCPU state worker).memory worker.resources.callerAddress =
      readWord (published state.world) worker.resources.callerAddress := by
  have agreement := local_loan_agrees (profile := profile) valid workerValid workerValid.1.2.1.1
  rw [workerValid.1.2.2.1] at agreement
  exact readWord_congr _ _ _ agreement

/-- All shared loan cells survive every scheduler action. The frame is derived
from the existing borrowing mutation frame / current fetchAdd effect. -/
theorem step_loan_contents {state : State} {action : Action} {result : State × Observation}
    {profile : Profile} (valid : WellFormed state profile)
    (success : step state action profile = .ok result)
    {identifier : Nat} {loan : Borrowing.Loan}
    (live : state.world.legacy.shared.loans identifier = some loan) (address : Word)
    (inside : loan.region.Contains address) :
    result.1.world.legacy.shared.resources.space.cells address =
      state.world.legacy.shared.resources.space.cells address := by
  cases action with
  | issue tid af =>
    obtain ⟨worker, _, _, _, _, instruction, _, effect⟩ := issue_effect (profile := profile) success
    cases instruction with
    | ordinary instruction =>
      cases effect with
      | intro supported bounds decoded reads queue step finish => cases finish <;> rfl
    | locked instruction =>
      cases effect with
      | blocked => rfl
      | rmw bounds empty decoded selected changed executed =>
        exact Atomics64.fetchAdd_loan_contents _ _ _ _ _ valid.1 changed identifier loan live address inside
  | drain tid =>
    obtain ⟨_, _, _, _, _, _, _, changed, same⟩ := drain_effect (profile := profile) success
    rw [same]
    exact changed.loan_contents valid.1 identifier loan live address inside

theorem schedule_loan_contents {state : State} {actions : List Action} {result : State × List Observation}
    {profile : Profile} (valid : WellFormed state profile)
    (success : schedule state actions profile = .ok result)
    {identifier : Nat} {loan : Borrowing.Loan}
    (live : state.world.legacy.shared.loans identifier = some loan) (address : Word)
    (inside : loan.region.Contains address) :
    result.1.world.legacy.shared.resources.space.cells address =
      state.world.legacy.shared.resources.space.cells address := by
  induction actions generalizing state result with
  | nil => simp only [schedule, Except.ok.injEq] at success; subst result; rfl
  | cons action rest ih =>
    obtain ⟨head, tail, first, following, same⟩ := schedule_cons_ok (profile := profile) success
    have headLive : head.1.world.legacy.shared.loans identifier = some loan :=
      (congrFun (step_stable (profile := profile) first).loans identifier).trans live
    rw [same]
    exact (ih (result := tail) (step_wellFormed (profile := profile) valid first) following headLive).trans
      (step_loan_contents (profile := profile) valid first live address inside)

/-- Actual RET is distinct from publication. Its memory read uses the actual
RSP, but that RSP must equal the ORIGINAL caller address. -/
theorem checkRead_stack {state : State} {worker : Worker} {address : Word} {width : Nat}
    {profile : Profile}
    (success : checkRead state worker ⟨.stack, address, width⟩ profile = .ok ()) :
    address = worker.resources.callerAddress ∧ width = 8 ∧
      ∃ value, Borrowing.loadWord64 state.world.legacy.shared worker.resources.actor
        worker.resources.caller.identifier address = .ok value := by
  by_cases slot : address = worker.resources.callerAddress ∧ width = 8
  · rcases slot with ⟨rfl, rfl⟩
    cases read : Borrowing.loadWord64 state.world.legacy.shared worker.resources.actor
        worker.resources.caller.identifier worker.resources.callerAddress with
    | error fault => simp [checkRead, read, Except.mapError] at success
    | ok value => exact ⟨rfl, rfl, value, rfl⟩
  · by_cases addressEq : address = worker.resources.callerAddress
    · have widthNe : width ≠ 8 := fun same => slot ⟨addressEq, same⟩
      simp [checkRead, widthNe] at success
    · simp [checkRead, addressEq] at success

/-- Successful shared reads add only exact-address, currently authorized qwords.
No byte overlay is used to establish this authority. -/
theorem checkRead_data_for {state : State} {worker : Worker} {address : Word} {width : Nat}
    {profile : Profile}
    (success : checkRead state worker ⟨.data, address, width⟩ profile = .ok ()) :
    ((width = 4 ∧ ∃ ticket, ticket ∈ worker.resources.grants ∧
      StoreGate state.world worker.resources.actor ticket ⟨address, .dword 0⟩) ∨
    (width = 8 ∧ ∃ ticket, ticket ∈ worker.resources.grants ∧
      StoreGate state.world worker.resources.actor ticket ⟨address, .qword 0⟩)) ∨
    (profile = .sharedCell ∧ width = 8 ∧ ∃ reference : Queue.ManagedRef,
      Queue.Current state.world worker.resources reference ∧ reference.cell.address = address) := by
  by_cases four : width = 4
  · subst width
    cases grant : grantFor state.world worker.resources ⟨address, .dword 0⟩ with
    | some ticket => exact .inl (.inl ⟨rfl, ticket, grantFor_sound grant⟩)
    | none =>
      simp at grant
      cases profile <;> simp [checkRead, grant] at success
  · by_cases eight : width = 8
    · subst width
      cases grant : grantFor state.world worker.resources ⟨address, .qword 0⟩ with
      | some ticket => exact .inl (.inr ⟨rfl, ticket, grantFor_sound grant⟩)
      | none =>
        simp at grant
        cases profile with
        | ownedOnly => simp [checkRead, grant] at success
        | sharedCell =>
          cases selected : atomicFor state.world worker.resources address with
          | none => simp [checkRead, grant, selected] at success
          | some descriptor =>
            rcases descriptor with ⟨identifier, handle, cell⟩
            have current := atomicFor_sound selected
            exact .inr ⟨rfl, rfl, ⟨identifier, handle, cell⟩,
              ⟨current.1, current.2.1⟩, current.2.2⟩
    · have denied : checkRead state worker ⟨.data, address, width⟩ profile =
          .error .unsupported := by simp [checkRead, eight]
      rw [denied] at success
      cases success

/-- The default-facing fact retains its ordinary-only conclusion, even on
arbitrary input states. Managed read admission requires an explicit profile. -/
theorem checkRead_data {state : State} {worker : Worker} {address : Word} {width : Nat}
    (success : checkRead state worker ⟨.data, address, width⟩ = .ok ()) :
    (width = 4 ∧ ∃ ticket, ticket ∈ worker.resources.grants ∧
      StoreGate state.world worker.resources.actor ticket ⟨address, .dword 0⟩) ∨
    (width = 8 ∧ ∃ ticket, ticket ∈ worker.resources.grants ∧
      StoreGate state.world worker.resources.actor ticket ⟨address, .qword 0⟩) := by
  rcases checkRead_data_for success with ordinary | ⟨impossible, _⟩
  · exact ordinary
  · cases impossible

end EDSL.OS.TSO64
