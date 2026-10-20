/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.ClientFrames

namespace EDSL.OS.Futex.Clients
open X86 AddressSpace

/-- Different live payload allocation identities give modular four-byte
separation, derived from present ownership rather than a replay assumption. -/
theorem grants_separate {state : Atomics.State} {left right : Storage.Grant}
    (valid : Atomics.WellFormed state) (leftReady : left.Valid state) (rightReady : right.Valid state)
    (different : left.ticket.identifier ≠ right.ticket.identifier) :
    StoreBuffer.Separate left.address right.address := by
  obtain ⟨a, authorizedA, fitsA, _, _, _⟩ := leftReady
  obtain ⟨b, authorizedB, fitsB, _, _, _⟩ := rightReady
  have atA := (Ownership.authorize_ok _ _ _ _ authorizedA).1
  have atB := (Ownership.authorize_ok _ _ _ _ authorizedB).1
  have validA := (valid.shared.1.1 _ _ atA).2.1
  have validB := (valid.shared.1.1 _ _ atB).2.1
  have separate := valid.shared.1.2 _ _ _ _ atA atB different
  have inside (allocation : Ownership.Allocation) (address query : Word)
      (regionValid : allocation.region.valid = true) (fits : Ownership.containsWord allocation address = true)
      (small : (query - address).toNat < 4) : allocation.region.Contains query := by
    have bounds := of_decide_eq_true fits
    have limit := (of_decide_eq_true regionValid).2.1
    have noWrap : address.toNat + 3 < 2^64 := by
      change allocation.region.base.toNat ≤ address.toNat ∧
        address.toNat + 4 ≤ allocation.region.base.toNat + allocation.region.length at bounds
      omega
    exact Ownership.containsWord_inside _ _ _ fits ((word_contains_iff address query noWrap).mpr small)
  intro query
  by_cases outside : 4 ≤ (query - left.address).toNat
  · exact Or.inl outside
  · right
    by_cases outsideB : 4 ≤ (query - right.address).toNat
    · exact outsideB
    · exact False.elim (Ownership.disjoint_outside separate
        (inside b right.address query validB fitsB (by omega))
        (inside a left.address query validA fitsA (by omega)))

end EDSL.OS.Futex.Clients
