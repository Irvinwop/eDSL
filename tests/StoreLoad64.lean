/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.StoreLoad64
import EDSL.Grading.Domain
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.StoreLoad64
open EDSL EDSL.X86 EDSL.X86.Sequential EDSL.OS EDSL.Grading AddressSpace
open EDSL.OS.WordResources64
open EDSL.StoreLoad64

/-- Every actual return in an arbitrary world has the complete result and
eight-byte frame; the statement is independent of a chosen evaluation fuel. -/
theorem actual_return_contract {input initial choices result}
    (pre : Pre bytes input initial)
    (execution : Sequential.Executes choices initial result) :
    result.state.registers .rax = input.argument ∧
      loadQWord result.state.memory input.address = .ok input.argument ∧
      (∀ query, 8 ≤ (query - input.address).toNat →
        result.state.memory.read query = initial.memory.read query) ∧
      result.state.memory.writable = initial.memory.writable ∧
      result.state.memory.executable = initial.memory.executable ∧
      result.instructions = 3 ∧
      result.reads = [⟨.data, input.address, 8⟩, ⟨.stack, initial.registers .rsp, 8⟩] := by
  have contract := Sequential.AllExecutions.project (raw_semantics pre) ⟨choices, execution⟩
  exact ⟨contract.1.result, contract.1.value, contract.1.outside,
    contract.1.writable, contract.1.executable, contract.2⟩

-- A fresh, checked EIGHT-byte allocation; the old32 four-byte witness is not used.
private def target : Region := ⟨262144, 8⟩
private def shared (codeBytes : List Byte) : Shared :=
  { Grading.Domain.shared codeBytes with resources := (Ownership.install (Grading.Domain.world codeBytes)
      (mapUnchecked (Grading.Domain.space codeBytes) target readWrite) 11 target) }

private theorem target_free (codeBytes : List Byte) (bound : codeBytes.length ≤ 4096) :
    allUnmapped (Grading.Domain.space codeBytes) target = true := by
  apply List.all_eq_true.mpr
  intro address member
  have inside := Ownership.addresses_inside target (by decide) address member
  change 262144 ≤ address.toNat ∧ address.toNat < 262144 + 8 at inside
  rw [Grading.Domain.cells_far codeBytes bound address (by omega)]
  have a : ¬Grading.Domain.stackRegion.Contains address := by
    change ¬(65544 ≤ address.toNat ∧ address.toNat < 65544 + 8); omega
  have b : ¬Grading.Domain.regionA.Contains address := by
    change ¬(131072 ≤ address.toNat ∧ address.toNat < 131072 + 16); omega
  have c : ¬Grading.Domain.regionB.Contains address := by
    change ¬(196608 ≤ address.toNat ∧ address.toNat < 196608 + 8); omega
  simp [Grading.Domain.payload, a, b, c]

private theorem allocated (codeBytes : List Byte) (positive : 0 < codeBytes.length)
    (bound : codeBytes.length ≤ 4096) :
    Borrowing.mutate (Grading.Domain.shared codeBytes) (.allocate 11 target readWrite) =
      .ok (shared codeBytes, some ⟨4, 0⟩) := by
  have allowed : Borrowing.allowed (Grading.Domain.shared codeBytes) (.allocate 11 target readWrite) = true := by
    apply List.all_eq_true.mpr
    intro identifier _
    cases (Grading.Domain.shared codeBytes).loans identifier <;> rfl
  have allocation := Ownership.allocate_success (Grading.Domain.world codeBytes) 11 target readWrite
    (Grading.Domain.world_valid codeBytes positive bound) (by decide) (by decide) (target_free codeBytes bound)
  simp only [Borrowing.mutate, allowed, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  simp [Ownership.Mutation.run, Grading.Domain.shared, allocation, Except.map, Except.mapError, shared]
  exact ⟨rfl, rfl⟩

private def call (codeBytes : List Byte) : WordResources64.Call :=
  ⟨10, ⟨4, 0⟩, 262144, 4096, 65544, 8192, codeBytes, 0, 1⟩

private def initial (codeBytes : List Byte) : State where
  memory := toMemory (shared codeBytes).resources.space
  rip := 4096
  registers register := match register with
    | .rdi => 262144
    | .rsi => 0xfeedface89abcdef
    | .rsp => 65544
    | _ => 0xfedcba9876543210
  flags := 0x602

/-- Inhabited current64 authority for any nonempty bounded executable bytes.
No byte is interpreted to construct this current-world witness. -/
private theorem arbitrary_current (codeBytes : List Byte) (positive : 0 < codeBytes.length)
    (bound : codeBytes.length ≤ 4096) :
    Current (call codeBytes) (shared codeBytes) (initial codeBytes) ∧
      loadQWord (initial codeBytes).memory (call codeBytes).targetPointer = .ok 0 := by
  have allocation := allocated codeBytes positive bound
  have history : Borrowing.History (Grading.Domain.shared codeBytes) (shared codeBytes) :=
    .next (.mutate allocation) .refl
  have base := Grading.Domain.contractA codeBytes positive bound
  have framed := base.frame history ⟨by rfl, by rfl, by intros; rfl⟩
  have wellFormed := history.wellFormed base.wellFormed
  have writable : canStoreQWord (toMemory (shared codeBytes).resources.space) 262144 = true := by
    simp [canStoreQWord, qwordAddressable, qwordWritable, toMemory, shared,
      Ownership.install, mapUnchecked, target, Region.Contains, readWrite, canonical]
  have word : WordValid (shared codeBytes) (Threads.principal (call codeBytes).worker)
      (call codeBytes).ticket (call codeBytes).targetPointer :=
    ⟨⟨11, 0, target⟩, rfl, rfl, rfl, by rfl, writable⟩
  have unborrowed : ∀ identifier loan, (shared codeBytes).loans identifier = some loan →
      loan.ticket.identifier ≠ (call codeBytes).ticket.identifier := by
    intro identifier loan live
    by_cases below : identifier < 4
    · simp only [shared, Grading.Domain.shared, below, ↓reduceIte, Option.some.injEq] at live
      subst loan
      change identifier ≠ 4
      omega
    · simp [shared, Grading.Domain.shared, below] at live
  have codeLoan : Threads.HasLoan (shared codeBytes) (call codeBytes).worker (call codeBytes).codeLoan
      ⟨(call codeBytes).code, (call codeBytes).bytes.length⟩ := framed.held.code
  have stackLoan : Threads.HasLoan (shared codeBytes) (call codeBytes).worker (call codeBytes).stackLoan
      ⟨(call codeBytes).stack, 8⟩ := framed.held.stack
  refine ⟨⟨⟨wellFormed, codeLoan, stackLoan, framed.code, framed.stack, word, unborrowed,
      word_hasLoan_disjoint wellFormed word codeLoan unborrowed,
      word_hasLoan_disjoint wellFormed word stackLoan unborrowed,
      by change canonical 8192 = true; decide,
      by change (65544 : Word).toNat + 8 < 2^64; decide,
      by change canonical ((65544 : Word) + 8) = true; decide⟩, rfl⟩, ?_⟩
  simp [initial, call, loadQWord, readDataByte, toMemory, shared, Ownership.install,
    mapUnchecked, target, Region.Contains, readWrite, canonical, joinQWord]

private def resource : Resources := ⟨shared bytes, call bytes, 0xfeedface89abcdef, 0⟩

private theorem admitted : ResourcePre bytes resource (initial bytes) :=
  ⟨(arbitrary_current bytes (by decide) (by decide)).1, rfl, rfl, rfl, rfl, rfl,
    (arbitrary_current bytes (by decide) (by decide)).2⟩

/-- Actual checked OS witness exercises all three machine instructions. The
high32 value is nonzero and the full64 RAX/readback must match it. -/
theorem runs_full_value (choices : Choices) :
    ∃ result, Sequential.run choices 3 (initial bytes) = .ok result ∧
      result.state.registers .rax = 0xfeedface89abcdef ∧
      loadQWord result.state.memory 262144 = .ok 0xfeedface89abcdef ∧
      result.state.rip = 8192 ∧ result.state.registers .rsp = 65552 ∧
      result.instructions = 3 ∧
      result.reads = [⟨.data, 262144, 8⟩, ⟨.stack, 65544, 8⟩] ∧
      ResourceReturn resource (initial bytes) result := by
  obtain ⟨result, execution, post, returned⟩ := (resource_semantics admitted).1 choices
  refine ⟨result, run_complete execution (Nat.le_of_eq post.2.1), post.1.result,
    post.1.value, post.1.returnAddress, ?_, post.2.1, post.2.2, returned⟩
  exact post.1.stackPointer

/-- Returned resources permit a second full64 mutation with the SAME low32
and different high32, with exact readback, permissions and all original loans
still framed on the actual returning trace. -/
theorem returned_authority_stores_again :
    ∃ result evolved nextWorld,
      Sequential.run (fun _ => false) 3 (initial bytes) = .ok result ∧
      Current (call bytes) evolved result.state ∧
      Grading.Trace.LiftedExecutes (resourceRules (call bytes)) (fun _ => false)
        (initial bytes) (shared bytes) result evolved ∧
      Borrowing.mutate evolved (.store64 11 ⟨4, 0⟩ 262144 0x0123456789abcdef) = .ok (nextWorld, none) ∧
      loadQWord (toMemory nextWorld.resources.space) 262144 = .ok 0x0123456789abcdef ∧
      nextWorld.resources.allocations = (shared bytes).resources.allocations ∧
      nextWorld.loans = (shared bytes).loans ∧
      (∀ query, (nextWorld.resources.space.cells query).map Cell.permissions =
        ((shared bytes).resources.space.cells query).map Cell.permissions) ∧
      (∀ query, ¬(qwordRegion 262144).Contains query →
        nextWorld.resources.space.cells query = (shared bytes).resources.space.cells query) := by
  obtain ⟨result, execution, contract, returned⟩ :=
    (resource_semantics admitted).1 (fun _ => false)
  obtain ⟨evolved, lifted, currentReturn, frame, _, again⟩ := returned _ execution
  obtain ⟨nextWorld, stored⟩ := again 0x0123456789abcdef
  have second := Borrowing.store64_effect stored
  refine ⟨result, evolved, nextWorld, run_complete execution (Nat.le_of_eq contract.2.1),
    currentReturn, lifted, stored, second.readback,
    second.allocations.trans frame.allocations, second.loans.trans frame.loans, ?_, ?_⟩
  · intro query
    exact (second.permissions query).trans (frame.permissions query)
  · intro query outside
    exact (second.outside query outside).trans (frame.outside query outside)

-- Current64 admission is independent of selected successful instructions.
example : Current (call [0xff]) (shared [0xff]) (initial [0xff]) :=
  (arbitrary_current [0xff] (by decide) (by decide)).1

end EDSL.Tests.StoreLoad64

#print axioms EDSL.StoreLoad64.raw_semantics
#print axioms EDSL.StoreLoad64.resource_semantics
#print axioms EDSL.Tests.StoreLoad64.actual_return_contract
#print axioms EDSL.Tests.StoreLoad64.runs_full_value
#print axioms EDSL.Tests.StoreLoad64.returned_authority_stores_again

#audit_edsl
