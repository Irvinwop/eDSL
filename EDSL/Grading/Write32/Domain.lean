/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.WordResources
import EDSL.Grading.Domain

set_option warningAsError true

namespace EDSL.Grading.Write32.Domain
open EDSL EDSL.X86 EDSL.X86.Sequential EDSL.OS EDSL.Grading AddressSpace
open EDSL.OS.WordResources

def target : Region := ⟨262144, 4⟩

/-- Extend the existing decoder-independent domain with a fresh writable
owned word; all four original loans remain live and unchanged. -/
def shared (bytes : List Byte) : Shared :=
  { Grading.Domain.shared bytes with resources := (Ownership.install (Grading.Domain.world bytes)
      (mapUnchecked (Grading.Domain.space bytes) target readWrite) 11 target) }

theorem target_free (bytes : List Byte) (bound : bytes.length ≤ 4096) :
    allUnmapped (Grading.Domain.space bytes) target = true := by
  apply List.all_eq_true.mpr
  intro address member
  have inside := Ownership.addresses_inside target (by decide) address member
  change 262144 ≤ address.toNat ∧ address.toNat < 262144 + 4 at inside
  rw [Grading.Domain.cells_far bytes bound address (by omega)]
  have a : ¬Grading.Domain.stackRegion.Contains address := by
    change ¬(65544 ≤ address.toNat ∧ address.toNat < 65544 + 8); omega
  have b : ¬Grading.Domain.regionA.Contains address := by
    change ¬(131072 ≤ address.toNat ∧ address.toNat < 131072 + 16); omega
  have c : ¬Grading.Domain.regionB.Contains address := by
    change ¬(196608 ≤ address.toNat ∧ address.toNat < 196608 + 8); omega
  simp [Grading.Domain.payload, a, b, c]

theorem allocated (bytes : List Byte) (positive : 0 < bytes.length) (bound : bytes.length ≤ 4096) :
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

def call (bytes : List Byte) : Call :=
  ⟨10, ⟨4, 0⟩, 262144, 4096, 65544, 8192, bytes, 0, 1⟩

def initial (bytes : List Byte) : State where
  memory := toMemory (shared bytes).resources.space
  rip := 4096
  registers register := match register with
    | .rdi => 262144
    | .rsi => 0xfeedface89abcdef
    | .rsp => 65544
    | _ => 0xfedcba9876543210
  flags := 0x602

/-- Every nonempty bounded candidate has an actual current resource admission.
No selected byte is interpreted while this witness is constructed. -/
theorem arbitrary_code_current (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) :
    Current (call bytes) (shared bytes) (initial bytes) ∧
      loadDWord (initial bytes).memory (call bytes).targetPointer = .ok 0 ∧
      ((initial bytes).registers .rsi).setWidth 32 ≠ (0 : BitVec 32) := by
  have allocation := allocated bytes positive bound
  have history : Borrowing.History (Grading.Domain.shared bytes) (shared bytes) :=
    .next (.mutate allocation) .refl
  have base := Grading.Domain.contractA bytes positive bound
  have framed := base.frame history ⟨by rfl, by rfl, by intros; rfl⟩
  have wellFormed := history.wellFormed base.wellFormed
  have writable : canStoreDWord (toMemory (shared bytes).resources.space) 262144 = true := by
    simp [canStoreDWord, dwordAddressable, dwordWritable, toMemory, shared,
      Ownership.install, mapUnchecked, target, Region.Contains, readWrite, canonical]
  have word : Mutex.WordValid (shared bytes) (Threads.principal (call bytes).worker)
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
  refine ⟨⟨⟨wellFormed, codeLoan, stackLoan, framed.code, framed.stack,
      word, unborrowed,
      word_hasLoan_disjoint wellFormed word codeLoan unborrowed,
      word_hasLoan_disjoint wellFormed word stackLoan unborrowed,
      by change canonical 8192 = true; decide,
      by change (65544 : Word).toNat + 8 < 2^64; decide,
      by change canonical ((65544 : Word) + 8) = true; decide⟩, rfl⟩, ?_,
    by change ((0xfeedface89abcdef : Word).setWidth 32) ≠ 0; decide⟩
  simp [initial, call, loadDWord, readDataByte, toMemory, shared, Ownership.install,
    mapUnchecked, target, Region.Contains, readWrite, canonical, joinDWord]

/-- All present raw machine facts needed by an independent store/RET contract.
Value is an arbitrary machine argument; it is never inferred from candidate code. -/
structure RawFacts (bytes : List Byte) (call : Call) (machine : State)
    (oldValue : BitVec 32) : Prop where
  codeBytes : call.bytes = bytes
  code : CodeAt machine.memory machine.rip bytes
  entry : machine.rip = call.code
  stackPointer : machine.registers .rsp = call.stack
  targetPointer : machine.registers .rdi = call.targetPointer
  old : loadDWord machine.memory call.targetPointer = .ok oldValue
  writable : canStoreDWord machine.memory call.targetPointer = true
  codeDisjoint : DWordDisjoint call.targetPointer machine.rip bytes.length
  stackDisjoint : DWordDisjoint call.targetPointer (machine.registers .rsp) 8
  stack : readWord machine.memory (machine.registers .rsp) = .ok call.returnAddress
  returnCanonical : canonical call.returnAddress = true
  stackBound : (machine.registers .rsp).toNat + 8 < 2^64
  postStackCanonical : canonical (machine.registers .rsp + 8) = true
  useful : oldValue ≠ (machine.registers .rsi).setWidth 32

theorem arbitrary_code_rawFacts (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) :
    RawFacts bytes (call bytes) (initial bytes) 0 := by
  obtain ⟨current, old, useful⟩ := arbitrary_code_current bytes positive bound
  have contract := current.contract
  refine ⟨rfl, ?_, rfl, rfl, rfl, old, ?_, contract.codeDisjoint,
    contract.stackDisjoint, ?_, contract.returnCanonical, contract.stackBound,
    contract.postStackCanonical, Ne.symm useful⟩
  · rw [current.coupled]
    exact contract.code
  · rw [current.coupled]
    exact contract.word.writable
  · rw [current.coupled]
    exact contract.stack

/-- Resource inhabitedness uses arbitrary code, current OS authority, useful
writable input and full RAM coupling; it is not a raw-only nonvacuity witness. -/
structure CandidateWitness (bytes : List Byte) where
  shared : Shared
  call : Call
  initial : State
  oldValue : BitVec 32
  current : Current call shared initial
  raw : RawFacts bytes call initial oldValue

def candidate (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) : CandidateWitness bytes where
  shared := shared bytes
  call := call bytes
  initial := initial bytes
  oldValue := 0
  current := (arbitrary_code_current bytes positive bound).1
  raw := arbitrary_code_rawFacts bytes positive bound

/-- A truncated FF group instruction still has the complete useful current
resource domain. The opcode is present; its required ModRM byte is absent. -/
def unsupported : CandidateWitness [0xff] := candidate [0xff] (by decide) (by decide)

/-- The ModRM fetch at entry 4096 + 1 fails independently of domain inhabitedness. -/
theorem unsupported_rejected :
    Sequential.decodeAt unsupported.initial = .error (.inaccessibleInstruction 4097) := by
  rfl


end EDSL.Grading.Write32.Domain
