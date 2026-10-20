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

/-- Byte agreement with current RAM over ANY live loan, including every peer's
code and original caller slot. Own pending writes cannot shadow protected bytes. -/
theorem local_loan_agrees {state : State} {worker : Worker} {identifier : Nat} {loan : Borrowing.Loan}
    (valid : WellFormed state) (workerValid : WorkerValid state.world worker)
    (live : state.world.legacy.shared.loans identifier = some loan) :
    MemoryAgreesOn (localCPU state worker).memory (published state.world) loan.region.base loan.region.length := by
  apply StoreBuffer.Mixed.view_agrees
  intro store member
  obtain ⟨pending, queued, same⟩ := List.mem_map.mp member
  subst store
  exact (workerValid.2 pending queued).2.loan_disjoint valid.1 live

theorem local_original_caller {state : State} {worker : Worker}
    (valid : WellFormed state) (workerValid : WorkerValid state.world worker) :
    readWord (localCPU state worker).memory worker.resources.callerAddress =
      readWord (published state.world) worker.resources.callerAddress := by
  have agreement := local_loan_agrees valid workerValid workerValid.1.2.1.1
  rw [workerValid.1.2.2.1] at agreement
  exact readWord_congr _ _ _ agreement

/-- All shared loan cells survive every scheduler action. The frame is derived
from the existing borrowing mutation frame / current fetchAdd effect. -/
theorem step_loan_contents {state : State} {action : Action} {result : State × Observation}
    (valid : WellFormed state) (success : step state action = .ok result)
    {identifier : Nat} {loan : Borrowing.Loan}
    (live : state.world.legacy.shared.loans identifier = some loan) (address : Word)
    (inside : loan.region.Contains address) :
    result.1.world.legacy.shared.resources.space.cells address =
      state.world.legacy.shared.resources.space.cells address := by
  cases action with
  | issue tid af =>
    obtain ⟨worker, _, _, _, _, instruction, _, effect⟩ := issue_effect success
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
    obtain ⟨_, _, _, _, _, _, _, changed, same⟩ := drain_effect success
    rw [same]
    exact publication_loans valid.1 changed identifier loan live address inside

theorem schedule_loan_contents {state : State} {actions : List Action} {result : State × List Observation}
    (valid : WellFormed state) (success : schedule state actions = .ok result)
    {identifier : Nat} {loan : Borrowing.Loan}
    (live : state.world.legacy.shared.loans identifier = some loan) (address : Word)
    (inside : loan.region.Contains address) :
    result.1.world.legacy.shared.resources.space.cells address =
      state.world.legacy.shared.resources.space.cells address := by
  induction actions generalizing state result with
  | nil => simp only [schedule, Except.ok.injEq] at success; subst result; rfl
  | cons action rest ih =>
    obtain ⟨head, tail, first, following, same⟩ := schedule_cons_ok success
    have headLive : head.1.world.legacy.shared.loans identifier = some loan :=
      (congrFun (step_stable first).loans identifier).trans live
    rw [same]
    exact (ih (result := tail) (step_wellFormed valid first) following headLive).trans
      (step_loan_contents valid first live address inside)

/-- Actual RET is distinct from publication. Its memory read uses the actual
RSP, but that RSP must equal the ORIGINAL caller address. -/
theorem checkRead_stack {state : State} {worker : Worker} {address : Word} {width : Nat}
    (success : checkRead state worker ⟨.stack, address, width⟩ = .ok ()) :
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

theorem checkRead_data {state : State} {worker : Worker} {address : Word} {width : Nat}
    (success : checkRead state worker ⟨.data, address, width⟩ = .ok ()) :
    (width = 4 ∧ ∃ ticket, ticket ∈ worker.resources.grants ∧
      StoreGate state.world worker.resources.actor ticket ⟨address, .dword 0⟩) ∨
    (width = 8 ∧ ∃ ticket, ticket ∈ worker.resources.grants ∧
      StoreGate state.world worker.resources.actor ticket ⟨address, .qword 0⟩) := by
  cases width with
  | zero => simp [checkRead] at success
  | succ width =>
    match width with
    | 3 =>
      simp only [checkRead, ok_bind, pure_ok] at success
      split at success
      next ticket grant => exact Or.inl ⟨rfl, ticket, grantFor_sound grant⟩
      next => cases success
    | 7 =>
      simp only [checkRead, ok_bind, pure_ok] at success
      split at success
      next ticket grant => exact Or.inr ⟨rfl, ticket, grantFor_sound grant⟩
      next => cases success
    | 0 | 1 | 2 | 4 | 5 | 6 | width + 8 => simp [checkRead] at success

end EDSL.OS.TSO64
