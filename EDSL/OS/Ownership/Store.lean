/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Ownership.Lifetime

namespace EDSL.OS.Ownership
open X86 AddressSpace

theorem containsWord_inside (allocation : Allocation) (address query : Word)
    (checked : containsWord allocation address = true) (inside : (wordRegion address).Contains query) :
    allocation.region.Contains query := by
  have bounds : allocation.region.base.toNat ≤ address.toNat ∧
      address.toNat + 4 ≤ allocation.region.base.toNat + allocation.region.length := of_decide_eq_true checked
  have lower := inside.1
  change address.toNat ≤ query.toNat at lower
  have upper := inside.2
  change query.toNat < address.toNat + 4 at upper
  exact ⟨by omega, by omega⟩

theorem storeWord_ok (world : World) (owner : Nat) (ticket : Ticket) (address : Word) (value : BitVec 32)
    (result : World) (success : storeWord world owner ticket address value = .ok result) :
    ∃ allocation space, authorize world owner ticket = .ok allocation ∧
      containsWord allocation address = true ∧
      AddressSpace.storeWord world.space address value = .ok space ∧ result = { world with space := space } := by
  cases authorized : authorize world owner ticket with
  | error fault => simp [storeWord, authorized] at success
  | ok allocation =>
    by_cases fits : containsWord allocation address = true
    · cases stored : AddressSpace.storeWord world.space address value with
      | error fault => simp [storeWord, authorized, fits, stored, Except.mapError] at success
      | ok space =>
        simp [storeWord, authorized, fits, stored, Except.mapError] at success
        exact ⟨allocation, space, rfl, fits, rfl, success.symm⟩
    · simp [storeWord, authorized, fits] at success

theorem storeWord_success (world : World) (owner : Nat) (ticket : Ticket) (address : Word) (value : BitVec 32)
    (allocation : Allocation) (authorized : authorize world owner ticket = .ok allocation)
    (fits : containsWord allocation address = true) (allowed : canStoreDWord (toMemory world.space) address = true) :
    storeWord world owner ticket address value =
      .ok { world with space := writeWordCells world.space address value } := by
  have stored := AddressSpace.storeWord_success world.space address value allowed
  simp [storeWord, authorized, fits, stored, Except.mapError]

theorem storeWord_wellFormed (world : World) (owner : Nat) (ticket : Ticket) (address : Word) (value : BitVec 32)
    (result : World) (valid : WellFormed world)
    (success : storeWord world owner ticket address value = .ok result) :
    WellFormed result ∧ Current result owner ticket ∧
    result.allocations = world.allocations ∧ result.frontier = world.frontier ∧
    X86.storeDWord (toMemory world.space) address value = .ok (toMemory result.space) ∧
    loadDWord (toMemory result.space) address = .ok value ∧
    (∀ query, (result.space.cells query).map Cell.permissions = (world.space.cells query).map Cell.permissions) ∧
    (∀ query allocation, authorize world owner ticket = .ok allocation → ¬allocation.region.Contains query →
      result.space.cells query = world.space.cells query) := by
  obtain ⟨allocation, space, authorized, fits, stored, resultEq⟩ := storeWord_ok _ _ _ _ _ _ success
  have current := authorize_current world owner ticket allocation authorized
  have sound := storeWord_sound world.space space address value stored
  subst result
  refine ⟨changeSpace_wellFormed world space valid ?_, current, rfl, rfl,
    sound.1, sound.2.1, sound.2.2.1, ?_⟩
  · intro identifier entry found query inside
    obtain ⟨old, existing⟩ := (valid.1 _ _ found).2.2 query inside
    have same := sound.2.2.1 query
    cases live : space.cells query with
    | none => simp [live, existing] at same
    | some cell => exact ⟨cell, rfl⟩
  · intro query other same outside
    have equal := Except.ok.inj (authorized.symm.trans same)
    cases equal
    exact sound.2.2.2 query (fun inside => outside (containsWord_inside allocation address query fits inside))

/-- The authority gate justifies this modeled store; the exact machine bytes
implement its OS-cell update. Hardware does not inspect ticket/owner fields.
The ordinary code/stack framing premises remain explicit. -/
theorem owned_store32_correct (world : World) (owner : Nat) (ticket : Ticket)
    (result : World) (initial : State) (returnAddress : Word)
    (success : storeWord world owner ticket (initial.registers .rdi)
      ((initial.registers .rsi).setWidth 32) = .ok result)
    (code : CodeAt (toMemory world.space) initial.rip Examples.Compiler.MemoryOps.storeBytes)
    (codeDisjoint : DWordDisjoint (initial.registers .rdi) initial.rip Examples.Compiler.MemoryOps.storeBytes.length)
    (stackDisjoint : DWordDisjoint (initial.registers .rdi) (initial.registers .rsp) 8)
    (stack : readWord (toMemory world.space) (initial.registers .rsp) = .ok returnAddress)
    (returnValid : canonical returnAddress = true) :
    let entry := { initial with memory := toMemory world.space }
    Executes entry (storeFinalWithSpace entry result.space returnAddress) 2 ∧
    ¬ Diverges entry ∧ ∀ final count, Executes entry final count →
      final = storeFinalWithSpace entry result.space returnAddress ∧ count = 2 := by
  obtain ⟨_, space, _, _, stored, resultEq⟩ := storeWord_ok _ _ _ _ _ _ success
  subst result
  exact store32_updates_space world.space space initial returnAddress stored code codeDisjoint
    stackDisjoint stack returnValid

end EDSL.OS.Ownership
