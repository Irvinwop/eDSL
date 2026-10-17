/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Ownership.Model
import EDSL.X86.StackRead64

namespace EDSL.OS.Ownership
open X86 AddressSpace

inductive ReadFault where
  | authority (fault : Fault)
  | outsideAllocation
  | machine (fault : X86.Error)
  deriving DecidableEq, Repr

@[simp] theorem readThrow_error (fault : ReadFault) :
    (throw fault : Except ReadFault α) = .error fault := rfl

/-- Current owner/epoch authority for one complete qword observation. This
creates no loan or mutation authority; CPU read permission is checked now. -/
def loadWord64 (world : World) (owner : Nat) (ticket : Ticket) (address : Word) :
    Except ReadFault Word := do
  let allocation ← (authorize world owner ticket).mapError ReadFault.authority
  if !containsQWord allocation address then throw .outsideAllocation
  (loadQWord (toMemory world.space) address).mapError ReadFault.machine

theorem loadWord64_ok (world : World) (owner : Nat) (ticket : Ticket) (address value : Word)
    (success : loadWord64 world owner ticket address = .ok value) :
    ∃ authorizedAllocation, authorize world owner ticket = .ok authorizedAllocation ∧
      containsQWord authorizedAllocation address = true ∧
      loadQWord (toMemory world.space) address = .ok value := by
  cases authorized : authorize world owner ticket with
  | error fault => simp [loadWord64, authorized, Except.mapError] at success
  | ok allocation =>
    by_cases fits : containsQWord allocation address = true
    · cases observed : loadQWord (toMemory world.space) address with
      | error fault => simp [loadWord64, authorized, fits, observed, Except.mapError] at success
      | ok word =>
        simp [loadWord64, authorized, fits, observed, Except.mapError] at success
        cases success
        exact ⟨allocation, rfl, fits, rfl⟩
    · simp [loadWord64, authorized, fits, Except.mapError] at success

theorem loadWord64_success (world : World) (owner : Nat) (ticket : Ticket) (address value : Word)
    (authorizedAllocation : Allocation)
    (authorized : authorize world owner ticket = .ok authorizedAllocation)
    (fits : containsQWord authorizedAllocation address = true)
    (observed : loadQWord (toMemory world.space) address = .ok value) :
    loadWord64 world owner ticket address = .ok value := by
  simp [loadWord64, authorized, fits, observed, Except.mapError]

theorem loadWord64_success_iff (world : World) (owner : Nat) (ticket : Ticket) (address value : Word) :
    loadWord64 world owner ticket address = .ok value ↔
      ∃ authorizedAllocation, authorize world owner ticket = .ok authorizedAllocation ∧
        containsQWord authorizedAllocation address = true ∧
        loadQWord (toMemory world.space) address = .ok value := by
  constructor
  · exact loadWord64_ok world owner ticket address value
  · rintro ⟨allocation, authorized, fits, observed⟩
    exact loadWord64_success world owner ticket address value allocation authorized fits observed

theorem loadWord64_current (world : World) (owner : Nat) (ticket : Ticket) (address value : Word)
    (success : loadWord64 world owner ticket address = .ok value) : Current world owner ticket := by
  obtain ⟨allocation, authorized, _, _⟩ := loadWord64_ok _ _ _ _ _ success
  exact authorize_current _ _ _ _ authorized

/-- This is the actual existing RET operand primitive, with no execution or
future-state premise and no claim that the loaded address is a valid target. -/
theorem loadWord64_readWord (world : World) (owner : Nat) (ticket : Ticket) (address value : Word)
    (success : loadWord64 world owner ticket address = .ok value) :
    readWord (toMemory world.space) address = .ok value := by
  obtain ⟨_, _, _, observed⟩ := loadWord64_ok _ _ _ _ _ success
  exact readWord_of_loadQWord _ _ _ observed

/-- A present complete store preflight supplies readability as well as
canonicality and nonwrapping. Ownership alone supplies neither permission. -/
theorem loadWord64_exists (world : World) (owner : Nat) (ticket : Ticket) (address : Word)
    (authorizedAllocation : Allocation)
    (authorized : authorize world owner ticket = .ok authorizedAllocation)
    (fits : containsQWord authorizedAllocation address = true)
    (readable : canStoreQWord (toMemory world.space) address = true) :
    ∃ value, loadWord64 world owner ticket address = .ok value := by
  obtain ⟨value, observed⟩ := loadQWord_of_canStoreQWord _ _ readable
  exact ⟨value, loadWord64_success _ _ _ _ _ authorizedAllocation authorized fits observed⟩

end EDSL.OS.Ownership
