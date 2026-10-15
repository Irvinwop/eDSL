/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.Physical

namespace EDSL.OS.Futex.Physical
open X86 AddressSpace

/-- Every successful synchronization also has an independently derived
physical RAM interpretation, including complete resource history. -/
theorem synchronize_sound (profile : Profile) (authority next : Atomics.State)
    (before after : Memory) (observation : Suspend.Observation)
    (valid : Atomics.WellFormed authority)
    (memory : toMemory authority.shared.resources.space = before)
    (effect : Effect before after observation)
    (success : synchronize profile authority observation = .ok next) :
    toMemory next.shared.resources.space = after ∧
      Atomics.History authority next ∧ Atomics.WellFormed next := by
  cases observation with
  | machine observed =>
    cases observed with
    | drained worker store =>
      cases atGrant : profile.payload worker with
      | none => simp [synchronize, atGrant] at success
      | some grant =>
        by_cases address : grant.address = store.address
        · cases published : Storage.publish authority grant store.value with
          | error fault => simp [synchronize, atGrant, address, published, Except.mapError] at success
          | ok result =>
            simp [synchronize, atGrant, address, published, Except.mapError] at success
            subst next
            have facts := Storage.publish_effect published
            have afterEq : after = writeDWordUnchecked before store.address store.value := by
              dsimp only [Effect] at effect
              unfold storeDWord at effect
              split at effect
              · exact Except.ok.inj effect.symm
              · cases effect
            exact ⟨by rw [facts.2.1, memory, address, afterEq],
              .next facts.1 .refl, facts.1.wellFormed valid⟩
        · simp [synchronize, atGrant, address] at success
    | retired worker event =>
      cases event with
      | none =>
        simp only [synchronize, Except.ok.injEq] at success
        subst next
        exact ⟨memory.trans effect.symm, .refl, valid⟩
      | some event =>
        cases atAccess : profile.atomic worker with
        | none => simp [synchronize, atAccess] at success
        | some access =>
          cases authorized : Atomics.authorize authority access.actor access.handle with
          | error fault => simp [synchronize, atAccess, authorized, Except.mapError] at success
          | ok handle =>
            by_cases address : handle.address = event.address
            · cases exchanged : Atomics.exchange authority access.actor access.handle event.after with
              | error fault => simp [synchronize, atAccess, authorized, address, exchanged, Except.mapError] at success
              | ok result =>
                by_cases old : result.2 = event.before
                · simp [synchronize, atAccess, authorized, address, exchanged, old, Except.mapError] at success
                  subst next
                  obtain ⟨selected, checked, actual⟩ := Atomics.exchange_sound _ _ _ _ _ exchanged
                  have same := Except.ok.inj (authorized.symm.trans checked)
                  subst selected
                  refine ⟨?_, .next (.exchange exchanged) .refl,
                    Atomics.exchange_wellFormed _ _ _ _ _ valid exchanged⟩
                  exact actual.2.2.2.trans (by rw [memory, address]; exact effect.2.2.2.symm)
                · simp [synchronize, atAccess, authorized, address, exchanged, old, Except.mapError] at success
            · simp [synchronize, atAccess, authorized, address, Except.mapError] at success
    | blocked worker =>
      simp only [synchronize, Except.ok.injEq] at success
      subst next
      exact ⟨memory.trans effect.symm, .refl, valid⟩
  | entered worker invocation | parked worker invocation | resumed worker invocation raw | idle =>
    simp only [synchronize, Except.ok.injEq] at success
    subst next
    exact ⟨memory.trans effect.symm, .refl, valid⟩

/-- Replay never changes handle identities or records, loans or allocation
metadata. Capture is the separate transition that retains a fresh call pin. -/
theorem synchronize_frames (profile : Profile) (authority next : Atomics.State)
    (observation : Suspend.Observation)
    (success : synchronize profile authority observation = .ok next) :
    next.handles = authority.handles ∧ next.nextHandle = authority.nextHandle ∧
      next.shared.loans = authority.shared.loans ∧ next.shared.nextLoan = authority.shared.nextLoan ∧
      next.shared.resources.allocations = authority.shared.resources.allocations ∧
      next.shared.resources.frontier = authority.shared.resources.frontier := by
  cases observation with
  | machine observed =>
    cases observed with
    | drained worker store =>
      cases atGrant : profile.payload worker with
      | none => simp [synchronize, atGrant] at success
      | some grant =>
        by_cases address : grant.address = store.address
        · cases published : Storage.publish authority grant store.value with
          | error fault => simp [synchronize, atGrant, address, published, Except.mapError] at success
          | ok result =>
            simp [synchronize, atGrant, address, published, Except.mapError] at success
            subst next
            cases mutation : Atomics.mutate authority (.store grant.owner grant.ticket grant.address store.value) with
            | error fault => simp [Storage.publish, mutation] at published
            | ok changed =>
              simp [Storage.publish, mutation] at published
              subst result
              obtain ⟨_, shared, modified, same⟩ := Atomics.mutate_ok _ _ _ mutation
              obtain ⟨_, resources, owned, sharedEq⟩ := Borrowing.mutate_ok _ _ _ modified
              cases stored : Ownership.storeWord authority.shared.resources grant.owner grant.ticket grant.address store.value with
              | error fault => simp [Ownership.Mutation.run, stored, Except.map] at owned
              | ok world =>
                simp [Ownership.Mutation.run, stored, Except.map] at owned
                subst resources
                obtain ⟨_, _, _, _, _, worldEq⟩ := Ownership.storeWord_ok _ _ _ _ _ _ stored
                rw [same, sharedEq, worldEq]
                exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
        · simp [synchronize, atGrant, address] at success
    | retired worker event =>
      cases event with
      | none => simp only [synchronize, Except.ok.injEq] at success; subst next; exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
      | some event =>
        cases atAccess : profile.atomic worker with
        | none => simp [synchronize, atAccess] at success
        | some access =>
          cases authorized : Atomics.authorize authority access.actor access.handle with
          | error fault => simp [synchronize, atAccess, authorized, Except.mapError] at success
          | ok handle =>
            by_cases address : handle.address = event.address
            · cases exchanged : Atomics.exchange authority access.actor access.handle event.after with
              | error fault => simp [synchronize, atAccess, authorized, address, exchanged, Except.mapError] at success
              | ok result =>
                by_cases old : result.2 = event.before
                · simp [synchronize, atAccess, authorized, address, exchanged, old, Except.mapError] at success
                  subst next
                  obtain ⟨chosen, shared, _, exchange, same⟩ := Atomics.exchange_ok _ _ _ _ _ exchanged
                  have gate := AtomicExchange.exchangeWord_guarded _ _ _ _ _ _ exchange
                  obtain ⟨_, resources, owned, sharedEq⟩ := Borrowing.mutate_ok _ _ _ gate
                  cases stored : Ownership.storeWord authority.shared.resources chosen.owner chosen.ticket chosen.address event.after with
                  | error fault => simp [Ownership.Mutation.run, stored, Except.map] at owned
                  | ok world =>
                    simp [Ownership.Mutation.run, stored, Except.map] at owned
                    subst resources
                    obtain ⟨_, _, _, _, _, worldEq⟩ := Ownership.storeWord_ok _ _ _ _ _ _ stored
                    have projected := congrArg Prod.fst sharedEq
                    dsimp only at projected
                    rw [same, projected, worldEq]
                    exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
                · simp [synchronize, atAccess, authorized, address, exchanged, old, Except.mapError] at success
            · simp [synchronize, atAccess, authorized, address, Except.mapError] at success
    | blocked worker => simp only [synchronize, Except.ok.injEq] at success; subst next; exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
  | entered worker invocation | parked worker invocation | resumed worker invocation raw | idle =>
    simp only [synchronize, Except.ok.injEq] at success
    subst next
    exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

end EDSL.OS.Futex.Physical
