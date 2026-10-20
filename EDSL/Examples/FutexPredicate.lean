/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Examples.FutexClient
import EDSL.OS.Futex.Predicate.Contract
import EDSL.OS.Futex.Predicate.Guards
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Examples.FutexPredicate
open X86 OS OS.AddressSpace OS.Futex OS.Futex.Predicate
open Examples.Futex (checked checked_ok)

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! The loader installs the new loop before any allocation is adopted or
loan is issued. The two unchanged legacy clients retain their real code,
payload tickets and complete original return words. No old WAIT admission
or historical syscall-memory equality is used for this cohort. -/

def space : AddressSpace.Space where
  cells address :=
    if 4096 ≤ address.toNat ∧ address.toNat < 4126 then
      (Predicate.bytes[address.toNat - 4096]?).map fun byte => ⟨byte, readExecute⟩
    else FutexClient.space.cells address

/-- Actual resource preparation for the thirty-byte code allocation. W has
two compatible atomic handles and no read loan. Its live keeper pins its
lifetime; the two payloads have separate ownership tickets. -/
def prepareActions : List Examples.Futex.PrepareAction :=
  [.mutate (.adopt 7 ⟨65536, 4⟩), .mutate (.adopt 7 ⟨131072, 4⟩),
   .mutate (.adopt 7 ⟨262144, 4⟩),
   .mutate (.adopt 7 ⟨4096, 30⟩), .mutate (.adopt 7 ⟨8192, 32⟩),
   .mutate (.adopt 7 ⟨16384, 8⟩),
   .mutate (.adopt 7 ⟨32768, 8⟩), .mutate (.adopt 7 ⟨32800, 8⟩),
   .mutate (.adopt 7 ⟨32832, 8⟩), .mutate (.adopt 7 ⟨32864, 8⟩),
   .mutate (.adopt 8 ⟨196608, 4⟩),
   .issue 7 ⟨0, 0⟩ 90 65536, .issue 7 ⟨0, 0⟩ 11 65536,
   .loan 7 ⟨3, 0⟩ 10 ⟨4096, 30⟩, .loan 7 ⟨6, 0⟩ 10 ⟨32768, 8⟩,
   .loan 7 ⟨4, 0⟩ 11 ⟨8192, 32⟩, .loan 7 ⟨7, 0⟩ 11 ⟨32800, 8⟩,
   .loan 7 ⟨5, 0⟩ 12 ⟨16384, 8⟩, .loan 7 ⟨8, 0⟩ 12 ⟨32832, 8⟩,
   .loan 8 ⟨10, 0⟩ 99 ⟨196608, 4⟩]

def authoritySeed : Atomics.State := Atomics.empty (Borrowing.empty (Ownership.empty space))

def authority : Atomics.State := checked
  (Examples.Futex.prepareRun authoritySeed prepareActions) (by rfl)

theorem authority_valid : Atomics.WellFormed authority :=
  (Examples.Futex.prepareRun_history
    (checked_ok (Examples.Futex.prepareRun authoritySeed prepareActions) (by rfl))).wellFormed
    (Atomics.empty_wellFormed _ (Borrowing.empty_wellFormed _ (Ownership.empty_wellFormed space)))

theorem authority_space : authority.shared.resources.space = space := rfl

abbrev registration := FutexClient.registration
abbrev publisherGrant := FutexClient.publisherGrant
abbrev peerGrant := FutexClient.peerGrant
abbrev profile := FutexClient.profile

def waiter : Predicate.Client := ⟨FutexClient.context 0, 9, 0, 1, 0x6000⟩
abbrev publisher := FutexClient.publisher
abbrev peer := FutexClient.peer

def clients : List Kind := [.waitLoop waiter, .legacy publisher, .legacy peer]

def initial : OS.Futex.State :=
  Runtime.initial authority (some registration) (clients.map Kind.initialWorker)

def cohort : Predicate.Cohort :=
  ⟨initial, profile, registration, clients, 0, authority.nextHandle,
    [(0, registration.handle), (1, registration.callHandle 11)]⟩

theorem initial_payload {worker : Nat} {grant : Storage.Grant}
    (found : profile.payload worker = some grant) : grant.Valid authority := by
  rcases FutexClient.payload_cases found with ⟨_, rfl⟩ | ⟨_, rfl⟩
  all_goals exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

theorem client_cases {worker : Nat} {kind : Kind} (found : cohort.clients[worker]? = some kind) :
    (worker = 0 ∧ kind = .waitLoop waiter) ∨
    (worker = 1 ∧ kind = .legacy publisher) ∨ (worker = 2 ∧ kind = .legacy peer) := by
  cases worker with
  | zero => exact Or.inl ⟨rfl, by simpa [cohort, clients] using found.symm⟩
  | succ worker =>
    cases worker with
    | zero => exact Or.inr (Or.inl ⟨rfl, by simpa [cohort, clients] using found.symm⟩)
    | succ worker =>
      cases worker with
      | zero => exact Or.inr (Or.inr ⟨rfl, by simpa [cohort, clients] using found.symm⟩)
      | succ worker => simp [cohort, clients] at found

theorem static : Predicate.Static cohort := by
  refine ⟨rfl, ?_, by simp [cohort, registration, FutexClient.registration],
    ⟨waiter, rfl⟩, ?_, ?_, ?_⟩
  · intro identifier handle member
    simp only [cohort, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
    rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> change _ < 2 <;> omega
  · intro worker kind found
    rcases client_cases found with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩
    · refine ⟨?_, Or.inl rfl⟩
      refine ⟨rfl, rfl, rfl, rfl, ⟨publisherGrant, rfl, rfl⟩,
        ⟨11, 1⟩, registration.callHandle 11, rfl, ?_, rfl, rfl, rfl, rfl⟩
      simp [cohort, Cohort.legacyEnvironment]
    · exact ⟨⟨rfl, rfl, rfl, rfl, ⟨peerGrant, rfl, rfl⟩, rfl⟩, Or.inr rfl⟩
  · intro worker client found
    rcases client_cases found with ⟨rfl, same⟩ | ⟨_, same⟩ | ⟨_, same⟩
    · cases same
      exact ⟨by decide, by decide⟩
    · cases same
    · cases same
  · intro left a right b different atA atB
    rcases FutexClient.payload_cases atA with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals rcases FutexClient.payload_cases atB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (different rfl).elim
    · exact Clients.grants_separate authority_valid (initial_payload (worker := 1) rfl)
        (initial_payload (worker := 2) rfl) (by decide)
    · exact Clients.grants_separate authority_valid (initial_payload (worker := 2) rfl)
        (initial_payload (worker := 1) rfl) (by decide)
    · exact (different rfl).elim

theorem initial_runtime : Runtime.Invariant profile initial := by
  apply Runtime.initial_invariant profile authority (some registration) _ authority_valid
  intro worker member store queued
  obtain ⟨kind, _, same⟩ := List.mem_map.mp member
  subst worker
  cases queued

theorem initial_memory : initial.suspended.machine.memory = toMemory space := by
  change toMemory authority.shared.resources.space = toMemory space
  rw [authority_space]

private theorem loop_code : CodeAt (toMemory space) 4096 Predicate.bytes :=
  checkCode_sound _ _ _ (by decide)
private theorem publishing_code : CodeAt (toMemory space) 8192 Clients.publishingBytes :=
  checkCode_sound _ _ _ (by decide)
private theorem peer_code : CodeAt (toMemory space) 16384 Clients.peerBytes :=
  checkCode_sound _ _ _ (by decide)

theorem initial_protection : Predicate.Protected cohort initial := by
  intro worker kind found
  rcases client_cases found with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨⟨_, rfl, rfl, rfl⟩, ⟨_, rfl, rfl, rfl⟩,
      initial_memory ▸ loop_code, rfl, by decide, fun _ _ => rfl, fun _ _ => rfl⟩
  · exact ⟨⟨_, rfl, rfl, rfl⟩, ⟨_, rfl, rfl, rfl⟩,
      initial_memory ▸ publishing_code, rfl, by decide, fun _ _ => rfl, fun _ _ => rfl⟩
  · exact ⟨⟨_, rfl, rfl, rfl⟩, ⟨_, rfl, rfl, rfl⟩,
      initial_memory ▸ peer_code, rfl, by decide, fun _ _ => rfl, fun _ _ => rfl⟩

/-- Non-vacuous admission is proved from executed allocation/adoption,
borrowing and atomic-handle preparation, actual machine slots and exact
current code. It contains no replay, future service or return premise. -/
theorem initial_admitted : Predicate.Admitted cohort initial := by
  refine ⟨static, initial_runtime, rfl, Control.initial cohort authority (some registration),
    rfl, ?_, ?_, by rfl, ?_, ?_, initial_protection, Or.inl rfl⟩
  · intro identifier handle member
    simp only [cohort, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
    rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  · exact ⟨Nat.le_refl _, fun _ _ found => by cases found⟩
  · intro worker grant found
    exact initial_payload found
  · exact Control.fifo_authorized (Control.initial cohort authority (some registration)) static
      (fun _ _ found => initial_payload found)

/-- Generic managed histories already preserve the current resource part,
even before the separate cyclic-control preservation API is available. The
original floor and fixed keeper are retained across every fresh capture. -/
theorem schedule_resources {actions : List Runtime.Action}
    {result : Futex.State × List Runtime.Observation}
    (actual : Runtime.schedule profile initial actions = .ok result) :
    Runtime.Invariant profile result.1 ∧ Predicate.Protected cohort result.1 ∧
    Clients.PinDiscipline cohort.pinFloor result.1 ∧
    (∀ identifier handle, (identifier, handle) ∈ cohort.fixedHandles →
      result.1.authority.handles identifier = some handle) := by
  have trace := Runtime.schedule_trace profile initial actions result actual
  have pins := Runtime.trace_discipline trace initial_admitted.discipline
  refine ⟨(trace.invariant initial_runtime).1, ?_, pins.1, ?_⟩
  · intro worker kind member
    exact (initial_protection worker kind member).trace initial_runtime trace
  · intro identifier handle member
    exact (pins.2.1 identifier (static.fixedBelow identifier handle member)).trans
      (initial_admitted.fixed identifier handle member)

/-! All following states are results of checked schedules, never assigned
desired final machine states. Portable model schedules imply no fairness or
native execution claim. -/

def waiterEntry : List Runtime.Action := List.replicate 6 (.issue 0)
def publisherEntry : List Runtime.Action := List.replicate 4 (.issue 1)

/-- The peer returns buffered. The publisher actually queues its payload,
blocks on XCHG until its own FIFO drains, and remains just before XCHG. -/
def prepare : List Runtime.Action :=
  [.issue 2, .issue 2, .issue 2, .issue 1, .issue 1, .issue 1, .issue 1, .drain 1]

def prepared : Futex.State × List Runtime.Observation :=
  checked (Runtime.schedule profile initial prepare) (by rfl)
def entered : Futex.State × List Runtime.Observation :=
  checked (Runtime.schedule profile prepared.1 waiterEntry) (by rfl)
def queued : Futex.State × List Runtime.Observation :=
  checked (Runtime.schedule profile entered.1 [.service (.compare 0)]) (by rfl)

/-- ZF is deliberately true on resume; the loop's actual CMP must replace
it. RCX/R11 and all other bits of flags are full-width private clobbers. -/
def resumeFlags : Word := 0x11223344556677c0
def resumeRcx : Word := 0x8877665544332211
def resumeR11 : Word := 0xfedcba9876543210

def resume (invocation : Nat) : Runtime.Action :=
  .service (.resume invocation resumeFlags resumeRcx resumeR11)
def retry : List Runtime.Action := List.replicate 3 (.issue 0)
def checkAndReturn : List Runtime.Action := List.replicate 4 (.issue 0)
def finish (invocation : Nat) : List Runtime.Action :=
  [resume invocation] ++ retry ++ checkAndReturn

def spurious : Futex.State × List Runtime.Observation :=
  checked (Runtime.schedule profile queued.1 [.service (.spurious 0)]) (by rfl)
def spuriousResumed : Futex.State × List Runtime.Observation :=
  checked (Runtime.schedule profile spurious.1 [resume 0]) (by rfl)
def spuriousMoved : Futex.State × Suspend.Observation :=
  checked (Physical.issue profile spuriousResumed.1 0) (by rfl)
def spuriousCompared : Futex.State × Suspend.Observation :=
  checked (Physical.issue profile spuriousMoved.1 0) (by rfl)
def spuriousBackedge : Futex.State × Suspend.Observation :=
  checked (Physical.issue profile spuriousCompared.1 0) (by rfl)
def spuriousReentered : Futex.State × List Runtime.Observation :=
  checked (Runtime.schedule profile spuriousBackedge.1 waiterEntry) (by rfl)
def spuriousRequeued : Futex.State × List Runtime.Observation :=
  checked (Runtime.schedule profile spuriousReentered.1 [.service (.compare 1)]) (by rfl)

def queuedExchange : Futex.State × Suspend.Observation :=
  checked (Physical.issue profile queued.1 1) (by rfl)
def queuedWaking : Futex.State × List Runtime.Observation :=
  checked (Runtime.schedule profile queuedExchange.1 publisherEntry) (by rfl)
def selected : Futex.State × List Runtime.Observation :=
  checked (Runtime.schedule profile queuedWaking.1 [.service (.wake 1 (some 0))]) (by rfl)
def selectedResumed : Futex.State × List Runtime.Observation :=
  checked (Runtime.schedule profile selected.1 [resume 0]) (by rfl)
def selectedBackedge : Futex.State × List Runtime.Observation :=
  checked (Runtime.schedule profile selectedResumed.1 retry) (by rfl)
def selectedReturned : Futex.State × List Runtime.Observation :=
  checked (Runtime.schedule profile selectedBackedge.1 checkAndReturn) (by rfl)
def publisherReturned : Futex.State × List Runtime.Observation :=
  checked (Runtime.schedule profile selectedReturned.1 [resume 1, .issue 1]) (by rfl)
def peerDrained : Futex.State × List Runtime.Observation :=
  checked (Runtime.schedule profile publisherReturned.1 [.drain 2]) (by rfl)

/-- First capture remembers W0. The comparison instead sees actual current
W1 after the publisher's XCHG, producing full-width EAGAIN. -/
def betweenExchange : Futex.State × Suspend.Observation :=
  checked (Physical.issue profile entered.1 1) (by rfl)
def betweenCompared : Futex.State × List Runtime.Observation :=
  checked (Runtime.schedule profile betweenExchange.1 [.service (.compare 0)]) (by rfl)
def betweenWaking : Futex.State × List Runtime.Observation :=
  checked (Runtime.schedule profile betweenCompared.1 publisherEntry) (by rfl)
def betweenWoken : Futex.State × List Runtime.Observation :=
  checked (Runtime.schedule profile betweenWaking.1 [.service (.wake 1 none)]) (by rfl)
def betweenResumed : Futex.State × List Runtime.Observation :=
  checked (Runtime.schedule profile betweenWoken.1 [resume 0]) (by rfl)
def betweenReturned : Futex.State × List Runtime.Observation :=
  checked (Runtime.schedule profile betweenWoken.1 (finish 0)) (by rfl)

/-- Publication and its actual empty WAKE happen before the first LOAD.
The real nonzero-load branch returns without allocating any WAIT pin. -/
def lateWoken : Futex.State × List Runtime.Observation :=
  checked (Runtime.schedule profile prepared.1
    ([.issue 1] ++ publisherEntry ++ [.service (.wake 0 none)])) (by rfl)
def lateReturned : Futex.State × List Runtime.Observation :=
  checked (Runtime.schedule profile lateWoken.1 checkAndReturn) (by rfl)

/-- A service retry retains its invocation and pin, but repeats the actual
current-RAM comparison after the exchange. -/
def currentRecheck : Futex.State × List Runtime.Observation :=
  checked (Runtime.schedule profile queuedExchange.1
    [.service (.retry 0), .service (.compare 0)]) (by rfl)

/-- Publication interrupts the waiter after LOAD0, CMP0, JNZ fallthrough,
or MOV202 respectively. All stale cuts remain executable after W becomes1;
none is excluded by shortening the test to a fresh-load case. -/
def stalePrefix (issued : Nat) : List Runtime.Action := List.replicate issued (.issue 0)
def staleNotifyActions (issued : Nat) : List Runtime.Action :=
  stalePrefix issued ++ [.issue 1] ++ publisherEntry ++ [.service (.wake 0 none)]

def loadedBeforeNotification : Futex.State × List Runtime.Observation :=
  checked (Runtime.schedule profile prepared.1 [.issue 0]) (by rfl)
def staleExchange : Futex.State × Suspend.Observation :=
  checked (Physical.issue profile loadedBeforeNotification.1 1) (by rfl)
def staleWaking : Futex.State × List Runtime.Observation :=
  checked (Runtime.schedule profile staleExchange.1 publisherEntry) (by rfl)

def notifiedAfterLoad : Futex.State × List Runtime.Observation :=
  checked (Runtime.schedule profile prepared.1 (staleNotifyActions 1)) (by rfl)
def notifiedAfterCompare : Futex.State × List Runtime.Observation :=
  checked (Runtime.schedule profile prepared.1 (staleNotifyActions 2)) (by rfl)
def notifiedAfterBranch : Futex.State × List Runtime.Observation :=
  checked (Runtime.schedule profile prepared.1 (staleNotifyActions 3)) (by rfl)
def notifiedAfterNumber : Futex.State × List Runtime.Observation :=
  checked (Runtime.schedule profile prepared.1 (staleNotifyActions 4)) (by rfl)

def staleCut (issued : Nat) : Except Physical.Fault (Futex.State × List Runtime.Observation) :=
  Runtime.schedule profile prepared.1
    (staleNotifyActions issued ++ List.replicate (6 - issued) (.issue 0) ++
      [.service (.compare 1)])
def staleLoaded : Futex.State × List Runtime.Observation := checked (staleCut 1) (by rfl)
def staleCompared : Futex.State × List Runtime.Observation := checked (staleCut 2) (by rfl)
def staleBranched : Futex.State × List Runtime.Observation := checked (staleCut 3) (by rfl)
def staleNumbered : Futex.State × List Runtime.Observation := checked (staleCut 4) (by rfl)
def staleReturned : Futex.State × List Runtime.Observation :=
  checked (Runtime.schedule profile staleLoaded.1 (finish 1)) (by rfl)

/-- Repeated spurious completion has already consumed call0/pin2. Actual
publication and WAKE now select the fresh call1/pin3, not either old ID. -/
def repeatedWoken : Futex.State × List Runtime.Observation :=
  checked (Runtime.schedule profile spuriousRequeued.1
    ([.issue 1] ++ publisherEntry ++ [.service (.wake 2 (some 1))])) (by rfl)
def repeatedReturned : Futex.State × List Runtime.Observation :=
  checked (Runtime.schedule profile repeatedWoken.1 (finish 1)) (by rfl)

end EDSL.Examples.FutexPredicate

#audit_edsl
