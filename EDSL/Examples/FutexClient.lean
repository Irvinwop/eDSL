/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Examples.Futex
import EDSL.OS.Futex.ClientAdmission
import EDSL.OS.Futex.ClientGeometry
import EDSL.X86.CodeCheck

namespace EDSL.Examples.FutexClient
open X86 OS OS.AddressSpace OS.Futex.Clients

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def space : AddressSpace.Space where
  cells address :=
    if 4096 ≤ address.toNat ∧ address.toNat < 4109 then
      ((Role.wait 0).bytes[address.toNat - 4096]?).map fun byte => ⟨byte, readExecute⟩
    else if 8192 ≤ address.toNat ∧ address.toNat < 8224 then
      (publishingBytes[address.toNat - 8192]?).map fun byte => ⟨byte, readExecute⟩
    else if 16384 ≤ address.toNat ∧ address.toNat < 16392 then
      (peerBytes[address.toNat - 16384]?).map fun byte => ⟨byte, readExecute⟩
    else if (32768 ≤ address.toNat ∧ address.toNat < 32776) ∨
        (32800 ≤ address.toNat ∧ address.toNat < 32808) ∨
        (32832 ≤ address.toNat ∧ address.toNat < 32840) ∨
        (32864 ≤ address.toNat ∧ address.toNat < 32872) then
      some ⟨if address.toNat % 32 = 1 then
        BitVec.ofNat 8 (0x60 + (address.toNat - 32768) / 32) else 0, readOnly⟩
    else if (65536 ≤ address.toNat ∧ address.toNat < 65540) ∨
        (131072 ≤ address.toNat ∧ address.toNat < 131076) ∨
        (262144 ≤ address.toNat ∧ address.toNat < 262148) then some ⟨0, readWrite⟩
    else if 196608 ≤ address.toNat ∧ address.toNat < 196612 then some ⟨0xa5, readOnly⟩
    else none

/-- Loader-installed cells are adopted without rewriting code, stacks or data.
The mutable futex and the two ordinary payloads have distinct allocation IDs. -/
def prepareActions : List Examples.Futex.PrepareAction :=
  [.mutate (.adopt 7 ⟨65536, 4⟩), .mutate (.adopt 7 ⟨131072, 4⟩),
   .mutate (.adopt 7 ⟨262144, 4⟩),
   .mutate (.adopt 7 ⟨4096, 13⟩), .mutate (.adopt 7 ⟨8192, 32⟩),
   .mutate (.adopt 7 ⟨16384, 8⟩),
   .mutate (.adopt 7 ⟨32768, 8⟩), .mutate (.adopt 7 ⟨32800, 8⟩),
   .mutate (.adopt 7 ⟨32832, 8⟩), .mutate (.adopt 7 ⟨32864, 8⟩),
   .mutate (.adopt 8 ⟨196608, 4⟩),
   .issue 7 ⟨0, 0⟩ 90 65536, .issue 7 ⟨0, 0⟩ 11 65536,
   .loan 7 ⟨3, 0⟩ 10 ⟨4096, 13⟩, .loan 7 ⟨6, 0⟩ 10 ⟨32768, 8⟩,
   .loan 7 ⟨4, 0⟩ 11 ⟨8192, 32⟩, .loan 7 ⟨7, 0⟩ 11 ⟨32800, 8⟩,
   .loan 7 ⟨5, 0⟩ 12 ⟨16384, 8⟩, .loan 7 ⟨8, 0⟩ 12 ⟨32832, 8⟩,
   .loan 7 ⟨3, 0⟩ 13 ⟨4096, 13⟩, .loan 7 ⟨9, 0⟩ 13 ⟨32864, 8⟩,
   .loan 8 ⟨10, 0⟩ 99 ⟨196608, 4⟩]

def authoritySeed : Atomics.State := Atomics.empty (Borrowing.empty (Ownership.empty space))

def authority : Atomics.State := Examples.Futex.checked
  (Examples.Futex.prepareRun authoritySeed prepareActions) (by rfl)

theorem authority_valid : Atomics.WellFormed authority :=
  (Examples.Futex.prepareRun_history
    (Examples.Futex.checked_ok (Examples.Futex.prepareRun authoritySeed prepareActions) (by rfl))).wellFormed
    (Atomics.empty_wellFormed _ (Borrowing.empty_wellFormed _ (Ownership.empty_wellFormed space)))

theorem authority_space : authority.shared.resources.space = space := rfl

def registration : OS.Futex.Resources.Registration := ⟨7, ⟨0, 0⟩, 90, 65536, 0⟩
def publisherGrant : OS.Futex.Storage.Grant := ⟨7, ⟨2, 0⟩, 262144⟩
def peerGrant : OS.Futex.Storage.Grant := ⟨7, ⟨1, 0⟩, 131072⟩

def profile : OS.Futex.Physical.Profile where
  service := ⟨0, 90, ⟨4096, 2^47⟩⟩
  payload worker := if worker = 1 then some publisherGrant else if worker = 2 then some peerGrant else none
  atomic worker := if worker = 1 then some ⟨11, 1⟩ else none

def context (worker : Nat) : Threads.Context where
  registers register :=
    if register = .rsp then BitVec.ofNat 64 (32768 + 32 * worker)
    else if register = .rdi then 65536
    else if register = .rsi ∧ worker = 1 then 262144
    else if register = .rsi ∧ worker = 2 then 131072
    else if register = .rdx ∨ register = .r10 ∨ register = .r8 ∨ register = .r9 then 0
    else 0xdeadbeefabcdef01
  rip := if worker = 1 then 8192 else if worker = 2 then 16384 else 4096
  flags := 0x246

def waiter : Client := ⟨.wait 0, context 0, 9, 0, 1, 0x6000⟩
def publisher : Client := ⟨.publishPayloadWake, context 1, 10, 2, 3, 0x6100⟩
def peer : Client := ⟨.payloadPeer, context 2, 11, 4, 5, 0x6200⟩
def otherWaiter : Client := ⟨.wait 0, context 3, 12, 6, 7, 0x6300⟩
def clients : List Client := [waiter, publisher, peer, otherWaiter]

def initial : OS.Futex.State :=
  OS.Futex.Runtime.initial authority (some registration) (clients.map fun client => ⟨client.entry, false, []⟩)

def cohort : Cohort :=
  ⟨initial, profile, registration, clients, 2,
    [(0, registration.handle), (1, registration.callHandle 11)]⟩

theorem payload_cases {worker : Nat} {grant : OS.Futex.Storage.Grant}
    (found : profile.payload worker = some grant) :
    (worker = 1 ∧ grant = publisherGrant) ∨ (worker = 2 ∧ grant = peerGrant) := by
  by_cases one : worker = 1
  · subst worker
    exact Or.inl ⟨rfl, by simpa [profile] using found.symm⟩
  · by_cases two : worker = 2
    · subst worker
      exact Or.inr ⟨rfl, by simpa [profile] using found.symm⟩
    · simp [profile, one, two] at found

theorem initial_payload {worker : Nat} {grant : OS.Futex.Storage.Grant}
    (found : profile.payload worker = some grant) : grant.Valid authority := by
  rcases payload_cases found with ⟨_, rfl⟩ | ⟨_, rfl⟩
  all_goals exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

theorem client_cases {worker : Nat} {client : Client} (found : cohort.clients[worker]? = some client) :
    (worker = 0 ∧ client = waiter) ∨ (worker = 1 ∧ client = publisher) ∨
      (worker = 2 ∧ client = peer) ∨ (worker = 3 ∧ client = otherWaiter) := by
  cases worker with
  | zero => exact Or.inl ⟨rfl, by simpa [cohort, clients] using found.symm⟩
  | succ worker =>
    cases worker with
    | zero => exact Or.inr (Or.inl ⟨rfl, by simpa [cohort, clients] using found.symm⟩)
    | succ worker =>
      cases worker with
      | zero => exact Or.inr (Or.inr (Or.inl ⟨rfl, by simpa [cohort, clients] using found.symm⟩))
      | succ worker =>
        cases worker with
        | zero => exact Or.inr (Or.inr (Or.inr ⟨rfl, by simpa [cohort, clients] using found.symm⟩))
        | succ worker => simp [cohort, clients] at found

theorem static : Static cohort := by
  refine ⟨rfl, ?_, by simp [cohort, registration], ?_, ?_⟩
  · intro identifier handle member
    simp only [cohort, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
    rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> change _ < 2 <;> omega
  · intro worker client found
    rcases client_cases found with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · refine ⟨rfl, rfl, rfl, rfl, ⟨publisherGrant, rfl, rfl⟩,
        ⟨11, 1⟩, registration.callHandle 11, rfl, ?_, rfl, rfl, rfl, rfl⟩
      simp [cohort]
    · exact ⟨rfl, rfl, rfl, rfl, ⟨peerGrant, rfl, rfl⟩, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro left a right b different atA atB
    rcases payload_cases atA with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals rcases payload_cases atB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (different rfl).elim
    · exact grants_separate authority_valid (initial_payload (worker := 1) rfl)
        (initial_payload (worker := 2) rfl) (by decide)
    · exact grants_separate authority_valid (initial_payload (worker := 2) rfl)
        (initial_payload (worker := 1) rfl) (by decide)
    · exact (different rfl).elim

theorem initial_control : Control cohort initial.suspended := by
  intro worker actual live
  change (clients.map fun client => (⟨client.entry, false, []⟩ : TSO.Worker))[worker]? = some actual at live
  rw [List.getElem?_map] at live
  cases atClient : clients[worker]? with
  | none => simp [atClient] at live
  | some client =>
    simp only [atClient, Option.map_some, Option.some.injEq] at live
    subst actual
    refine ⟨client, atClient, .running .start (by cases client.role <;> trivial) ?_ rfl rfl ?_⟩
    · simp [Stage.context, Stage.offset]
    · cases kind : client.role <;> simp [Stage.FIFO, Stage.bufferCondition, kind]

theorem initial_runtime : OS.Futex.Runtime.Invariant profile initial := by
  apply OS.Futex.Runtime.initial_invariant profile authority (some registration) _ authority_valid
  intro worker member store queued
  obtain ⟨client, _, same⟩ := List.mem_map.mp member
  subst worker
  cases queued

theorem initial_memory : initial.suspended.machine.memory = toMemory space := by
  change toMemory authority.shared.resources.space = toMemory space
  rw [authority_space]

private theorem wait_code : CodeAt (toMemory space) 4096 (Role.wait 0).bytes :=
  checkCode_sound _ _ _ (by decide)
private theorem publishing_code : CodeAt (toMemory space) 8192 publishingBytes :=
  checkCode_sound _ _ _ (by decide)
private theorem peer_code : CodeAt (toMemory space) 16384 peerBytes :=
  checkCode_sound _ _ _ (by decide)

theorem initial_protection : Protected cohort initial := by
  intro worker client atClient
  rcases client_cases atClient with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨⟨_, rfl, rfl, rfl⟩, ⟨_, rfl, rfl, rfl⟩,
      initial_memory ▸ wait_code, rfl, by decide, fun _ _ => rfl, fun _ _ => rfl⟩
  · exact ⟨⟨_, rfl, rfl, rfl⟩, ⟨_, rfl, rfl, rfl⟩,
      initial_memory ▸ publishing_code, rfl, by decide, fun _ _ => rfl, fun _ _ => rfl⟩
  · exact ⟨⟨_, rfl, rfl, rfl⟩, ⟨_, rfl, rfl, rfl⟩,
      initial_memory ▸ peer_code, rfl, by decide, fun _ _ => rfl, fun _ _ => rfl⟩
  · exact ⟨⟨_, rfl, rfl, rfl⟩, ⟨_, rfl, rfl, rfl⟩,
      initial_memory ▸ wait_code, rfl, by decide, fun _ _ => rfl, fun _ _ => rfl⟩

theorem initial_admitted : Admitted cohort initial := by
  refine ⟨static, initial_runtime, rfl, initial_control, rfl, ?_, ?_, by rfl, ?_, ?_, initial_protection⟩
  · intro identifier handle member
    simp only [cohort, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
    rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  · exact ⟨Nat.le_refl _, fun _ _ found => by cases found⟩
  · intro worker grant found
    exact initial_payload found
  · intro worker actual live store queued
    change (clients.map fun client => (⟨client.entry, false, []⟩ : TSO.Worker))[worker]? = some actual at live
    rw [List.getElem?_map] at live
    cases atClient : clients[worker]? with
    | none => simp [atClient] at live
    | some client =>
      simp only [atClient, Option.map_some, Option.some.injEq] at live
      subst actual
      cases queued

end EDSL.Examples.FutexClient
