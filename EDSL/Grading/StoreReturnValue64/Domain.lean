/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.StoreReturnValue64.Contract
import EDSL.Grading.Domain

set_option warningAsError true

namespace EDSL.Grading.StoreReturnValue64.Domain
open EDSL EDSL.X86 EDSL.X86.Sequential EDSL.OS AddressSpace
open EDSL.OS.WordResources64

def target : Region := ⟨262144, 8⟩

/-- A fresh complete eight-byte allocation, retaining the code, stack and
array loans of the shared decoder-independent domain. -/
def shared (bytes : List Byte) : Shared :=
  { Grading.Domain.shared bytes with resources := (Ownership.install (Grading.Domain.world bytes)
      (mapUnchecked (Grading.Domain.space bytes) target readWrite) 11 target) }

theorem target_free (bytes : List Byte) (bound : bytes.length ≤ 4096) :
    allUnmapped (Grading.Domain.space bytes) target = true := by
  apply List.all_eq_true.mpr
  intro address member
  have inside := Ownership.addresses_inside target (by decide) address member
  change 262144 ≤ address.toNat ∧ address.toNat < 262144 + 8 at inside
  rw [Grading.Domain.cells_far bytes bound address (by omega)]
  have a : ¬Grading.Domain.stackRegion.Contains address := by
    change ¬(65544 ≤ address.toNat ∧ address.toNat < 65544 + 8); omega
  have b : ¬Grading.Domain.regionA.Contains address := by
    change ¬(131072 ≤ address.toNat ∧ address.toNat < 131072 + 16); omega
  have c : ¬Grading.Domain.regionB.Contains address := by
    change ¬(196608 ≤ address.toNat ∧ address.toNat < 196608 + 8); omega
  simp [Grading.Domain.payload, a, b, c]

/-- Checked allocation establishes a genuine current owner and epoch. No
candidate decoding or future program/store success is assumed. -/
theorem allocated (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) :
    Borrowing.mutate (Grading.Domain.shared bytes) (.allocate 11 target readWrite) =
      .ok (shared bytes, some ⟨4, 0⟩) := by
  have allowed : Borrowing.allowed (Grading.Domain.shared bytes) (.allocate 11 target readWrite) = true := by
    apply List.all_eq_true.mpr
    intro identifier _
    cases (Grading.Domain.shared bytes).loans identifier <;> rfl
  have allocation := Ownership.allocate_success (Grading.Domain.world bytes) 11 target readWrite
    (Grading.Domain.world_valid bytes positive bound) (by decide) (by decide) (target_free bytes bound)
  simp only [Borrowing.mutate, allowed, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  simp [Ownership.Mutation.run, Grading.Domain.shared, allocation, Except.map, Except.mapError, shared]
  exact ⟨rfl, rfl⟩

def call (bytes : List Byte) : WordResources64.Call :=
  ⟨10, ⟨4, 0⟩, 262144, 4096, 65544, 8192, bytes, 0, 1⟩

/-- Arguments and all otherwise unconstrained registers/flags are parameters.
Neither universal admission predicate fixes RAX, flags, or a chosen fixture. -/
def initial (bytes : List Byte) (argument : Word := 0xfeedface89abcdef)
    (registers : Register → Word := fun _ => 0xfedcba9876543210)
    (flags : Word := 0x602) : State where
  memory := toMemory (shared bytes).resources.space
  rip := 4096
  registers register := match register with
    | .rdi => 262144
    | .rsi => argument
    | .rsp => 65544
    | _ => registers register
  flags := flags

/-- Every nonempty bounded byte span has complete current authority, an
unborrowed target, live original loans and full machine RAM coupling. -/
theorem arbitrary_current (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) (argument : Word := 0xfeedface89abcdef)
    (registers : Register → Word := fun _ => 0xfedcba9876543210)
    (flags : Word := 0x602) :
    Current (call bytes) (shared bytes) (initial bytes argument registers flags) ∧
      loadQWord (initial bytes argument registers flags).memory (call bytes).targetPointer = .ok 0 := by
  have allocation := allocated bytes positive bound
  have history : Borrowing.History (Grading.Domain.shared bytes) (shared bytes) :=
    .next (.mutate allocation) .refl
  have base := Grading.Domain.contractA bytes positive bound
  have framed := base.frame history ⟨by rfl, by rfl, by intros; rfl⟩
  have wellFormed := history.wellFormed base.wellFormed
  have writable : canStoreQWord (toMemory (shared bytes).resources.space) 262144 = true := by
    simp [canStoreQWord, qwordAddressable, qwordWritable, toMemory, shared,
      Ownership.install, mapUnchecked, target, Region.Contains, readWrite, canonical]
  have word : WordValid (shared bytes) (Threads.principal (call bytes).worker)
      (call bytes).ticket (call bytes).targetPointer :=
    ⟨⟨11, 0, target⟩, rfl, rfl, rfl, by rfl, writable⟩
  have unborrowed : ∀ identifier loan, (shared bytes).loans identifier = some loan →
      loan.ticket.identifier ≠ (call bytes).ticket.identifier := by
    intro identifier loan live
    by_cases below : identifier < 4
    · simp only [shared, Grading.Domain.shared, below, ↓reduceIte, Option.some.injEq] at live
      subst loan
      change identifier ≠ 4
      omega
    · simp [shared, Grading.Domain.shared, below] at live
  have codeLoan : Threads.HasLoan (shared bytes) (call bytes).worker (call bytes).codeLoan
      ⟨(call bytes).code, (call bytes).bytes.length⟩ := framed.held.code
  have stackLoan : Threads.HasLoan (shared bytes) (call bytes).worker (call bytes).stackLoan
      ⟨(call bytes).stack, 8⟩ := framed.held.stack
  refine ⟨⟨⟨wellFormed, codeLoan, stackLoan, framed.code, framed.stack, word, unborrowed,
      word_hasLoan_disjoint wellFormed word codeLoan unborrowed,
      word_hasLoan_disjoint wellFormed word stackLoan unborrowed,
      by change canonical 8192 = true; decide,
      by change (65544 : Word).toNat + 8 < 2^64; decide,
      by change canonical ((65544 : Word) + 8) = true; decide⟩, rfl⟩, ?_⟩
  simp [initial, call, loadQWord, readDataByte, toMemory, shared, Ownership.install,
    mapUnchecked, target, Region.Contains, readWrite, canonical, joinQWord]

def resource (bytes : List Byte) (argument : Word := 0xfeedface89abcdef) : Resources :=
  ⟨shared bytes, call bytes, argument, 0⟩

/-- Reusable raw and resource admissions use only present bytes/RAM/authority.
Usefulness remains a separate fact, so even same-value inputs are admitted. -/
theorem resource_pre (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) (argument : Word := 0xfeedface89abcdef)
    (registers : Register → Word := fun _ => 0xfedcba9876543210)
    (flags : Word := 0x602) :
    ResourcePre bytes (resource bytes argument) (initial bytes argument registers flags) :=
  ⟨(arbitrary_current bytes positive bound argument registers flags).1,
    rfl, rfl, rfl, rfl, rfl, (arbitrary_current bytes positive bound argument registers flags).2⟩

theorem raw_pre (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) (argument : Word := 0xfeedface89abcdef)
    (registers : Register → Word := fun _ => 0xfedcba9876543210)
    (flags : Word := 0x602) :
    Pre bytes (resourceInput (resource bytes argument)) (initial bytes argument registers flags) :=
  (resource_pre bytes positive bound argument registers flags).machine

structure CandidateWitness (bytes : List Byte) where
  resource : Resources
  initial : State
  pre : ResourcePre bytes resource initial
  useful : Useful (resourceInput resource)

def candidateWith (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) (argument : Word) (different : (0 : Word) ≠ argument)
    (registers : Register → Word := fun _ => 0xfedcba9876543210)
    (flags : Word := 0x602) : CandidateWitness bytes where
  resource := resource bytes argument
  initial := initial bytes argument registers flags
  pre := resource_pre bytes positive bound argument registers flags
  useful := different

def candidate (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) : CandidateWitness bytes :=
  candidateWith bytes positive bound 0xfeedface89abcdef (by decide)

/-- The low32 bits agree with the old value; the full64 value still changes. -/
def upperOnly (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) : CandidateWitness bytes :=
  candidateWith bytes positive bound 0x100000000 (by decide)

def unsupported : CandidateWitness [0xff] := candidate [0xff] (by decide) (by decide)

theorem unsupported_rejected :
    Sequential.decodeAt unsupported.initial = .error (.unsupportedOpcode 0xff) := rfl

end EDSL.Grading.StoreReturnValue64.Domain
