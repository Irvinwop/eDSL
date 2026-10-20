/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.Queue.Authority
import EDSL.OS.TSO64.ManagedPublication

namespace EDSL.OS.TSO64.Queue
open X86 AddressSpace

/-- Recheck the retained authority at the current world before publication.
The default policy rejects a managed entry even in an arbitrary initial queue.
This policy operation performs no instruction execution or implicit drain. -/
def publish (world : World) (resources : Resources) (entry : Entry)
    (profile : Profile := .ownedOnly) : Except Fault (World × Option Atomics64.StoreEvent64) := do
  if ¬Valid world resources entry profile then throw .resource
  match entry with
  | .ordinary ticket store =>
      let result ← (Atomics64.mutate world (operation resources.actor ticket store)).mapError Fault.os
      return (result.1, none)
  | .managed reference value _ =>
      let result ← (Atomics64.publishStore world resources.actor reference.identifier value).mapError Fault.os
      return (result.1, some result.2)

/-- The checked OS operation underlying an actual tagged publication. A managed
store always has its store event, including when the value does not change. -/
inductive Effect (world : World) (resources : Resources) :
    Entry → (World × Option Atomics64.StoreEvent64) → Prop where
  | ordinary {ticket store output}
      (changed : Atomics64.mutate world (operation resources.actor ticket store) = .ok output) :
      Effect world resources (.ordinary ticket store) (output.1, none)
  | managed {reference value occurrence output}
      (current : Current world resources reference)
      (changed : Atomics64.publishStore world resources.actor reference.identifier value = .ok output) :
      Effect world resources (.managed reference value occurrence) (output.1, some output.2)

theorem publish_effect {world : World} {resources : Resources} {entry : Entry}
    {profile : Profile} {result : World × Option Atomics64.StoreEvent64}
    (success : publish world resources entry profile = .ok result) :
    Valid world resources entry profile ∧ Effect world resources entry result := by
  by_cases valid : Valid world resources entry profile
  · cases entry with
    | ordinary ticket store =>
      cases changed : Atomics64.mutate world (operation resources.actor ticket store) with
      | error fault => simp [publish, valid, changed, Except.mapError] at success
      | ok output =>
        simp [publish, valid, changed, Except.mapError] at success
        subst result
        exact ⟨valid, .ordinary changed⟩
    | managed reference value occurrence =>
      cases changed : Atomics64.publishStore world resources.actor reference.identifier value with
      | error fault => simp [publish, valid, changed, Except.mapError] at success
      | ok output =>
        simp [publish, valid, changed, Except.mapError] at success
        subst result
        exact ⟨valid, .managed valid.2 changed⟩
  · simp [publish, valid] at success

theorem Effect.publication {world : World} {resources : Resources} {entry : Entry}
    {result : World × Option Atomics64.StoreEvent64} (effect : Effect world resources entry result) :
    Publication world result.1 entry.store := by
  cases effect with
  | ordinary changed => exact TSO64.publication changed
  | managed current changed =>
      exact publishStore_publication_of_authorized changed current.2

theorem Effect.wellFormed {world : World} {resources : Resources} {entry : Entry}
    {result : World × Option Atomics64.StoreEvent64} (effect : Effect world resources entry result)
    (valid : Atomics64.WellFormed world) : Atomics64.WellFormed result.1 := by
  cases effect with
  | ordinary changed => exact Atomics64.mutate_wellFormed _ _ _ valid changed
  | managed current changed => exact Atomics64.publishStore_wellFormed _ _ _ _ _ valid changed

/-- Live code and caller loans retain their complete original bytes under
either publication case. No equality of just the selected word is substituted. -/
theorem Effect.loan_contents {world : World} {resources : Resources} {entry : Entry}
    {result : World × Option Atomics64.StoreEvent64} (effect : Effect world resources entry result)
    (valid : Atomics64.WellFormed world) (identifier : Nat) (loan : Borrowing.Loan)
    (live : world.legacy.shared.loans identifier = some loan) (address : Word)
    (inside : loan.region.Contains address) :
    result.1.legacy.shared.resources.space.cells address = world.legacy.shared.resources.space.cells address := by
  cases effect with
  | ordinary changed => exact publication_loans valid changed identifier loan live address inside
  | managed current changed =>
      exact Atomics64.publishStore_loan_contents _ _ _ _ _ valid changed identifier loan live address inside

/-- Enabledness follows from present invariants and present authority. It is
not checked by speculatively executing the desired future publication. -/
theorem publish_enabled {world : World} {resources : Resources} {entry : Entry} {profile : Profile}
    (worldValid : Atomics64.WellFormed world) (valid : Valid world resources entry profile) :
    ∃ result, publish world resources entry profile = .ok result := by
  cases entry with
  | ordinary ticket store =>
      obtain ⟨after, changed⟩ := valid.2.enabled
      exact ⟨(after, none), by simp [publish, valid, changed, Except.mapError]⟩
  | managed reference value occurrence =>
      obtain ⟨result, changed⟩ := Atomics64.publishStore_enabled world resources.actor
        reference.identifier value reference.handle reference.cell worldValid valid.2.2
      exact ⟨(result.1, some result.2), by simp [publish, valid, changed, Except.mapError]⟩

/-- A managed head cannot reach even the primitive in the default policy.
There is no well-formedness or reachability premise hiding forged inputs. -/
@[simp] theorem publish_managed_ownedOnly (world : World) (resources : Resources)
    (reference : ManagedRef) (value : Word) (occurrence : Nat) :
    publish world resources (.managed reference value occurrence) .ownedOnly = .error .resource := by
  simp [publish]

/-- Successful default publication exposes the actual outer ordinary mutation.
The fetch-add-only history can use this fact without treating a managed store
as silent or assuming that initial queues were empty. -/
theorem publish_ownedOnly {world : World} {resources : Resources} {entry : Entry}
    {result : World × Option Atomics64.StoreEvent64}
    (success : publish world resources entry .ownedOnly = .ok result) :
    ∃ ticket store output, entry = .ordinary ticket store ∧
      Atomics64.mutate world (operation resources.actor ticket store) = .ok output ∧
      result = (output.1, none) := by
  obtain ⟨valid, effect⟩ := publish_effect success
  cases effect with
  | ordinary changed => exact ⟨_, _, _, rfl, changed, rfl⟩
  | managed current changed => exact False.elim (not_valid_managed_ownedOnly _ _ _ _ _ valid)

/-- Publish exactly the oldest retained entry. The returned tail is literal;
no peer queue, return instruction or partial overlay causes publication. -/
def publishHead (world : World) (resources : Resources) (entries : List Entry)
    (profile : Profile := .ownedOnly) :
    Except Fault (World × List Entry × Option Atomics64.StoreEvent64) := do
  let head :: tail := entries | throw .emptyBuffer
  let result ← publish world resources head profile
  return (result.1, tail, result.2)

theorem publishHead_effect {world : World} {resources : Resources} {entries : List Entry}
    {profile : Profile} {result : World × List Entry × Option Atomics64.StoreEvent64}
    (success : publishHead world resources entries profile = .ok result) :
    ∃ head tail output, entries = head :: tail ∧
      publish world resources head profile = .ok output ∧
      result = (output.1, tail, output.2) := by
  cases entries with
  | nil => simp [publishHead] at success
  | cons head tail =>
      cases published : publish world resources head profile with
      | error fault => simp [publishHead, published] at success
      | ok output =>
          simp [publishHead, published] at success
          exact ⟨head, tail, output, rfl, published, success.symm⟩

/-- The exact head publishes to current RAM, while the issuing worker's actual
Mixed overlay remains identical after removing that head. -/
theorem publishHead_fifo {world : World} {resources : Resources} {entries : List Entry}
    {profile : Profile} {result : World × List Entry × Option Atomics64.StoreEvent64}
    (success : publishHead world resources entries profile = .ok result) :
    ∃ head tail, entries = head :: tail ∧ result.2.1 = tail ∧
      Publication world result.1 head.store ∧
      StoreBuffer.Mixed.view (published result.1) (payload result.2.1) =
        StoreBuffer.Mixed.view (published world) (payload entries) := by
  obtain ⟨head, tail, output, original, changed, same⟩ := publishHead_effect success
  have effect := (publish_effect changed).2.publication
  subst result
  refine ⟨head, tail, original, rfl, effect, ?_⟩
  rw [original, payload_cons, effect.projection]
  rfl

/-- Publication preserves current authority for every remaining entry, including
mixed ordinary and managed tails. It does not turn authority into provenance. -/
theorem publishHead_preserves {world : World} {resources : Resources} {entries : List Entry}
    {profile : Profile} {result : World × List Entry × Option Atomics64.StoreEvent64}
    (worldValid : Atomics64.WellFormed world)
    (queueValid : ∀ entry ∈ entries, Valid world resources entry profile)
    (success : publishHead world resources entries profile = .ok result) :
    Atomics64.WellFormed result.1 ∧
      ∀ entry ∈ result.2.1, Valid result.1 resources entry profile := by
  obtain ⟨head, tail, output, original, changed, same⟩ := publishHead_effect success
  have effect := (publish_effect changed).2
  subst result
  refine ⟨effect.wellFormed worldValid, ?_⟩
  intro entry member
  apply effect.publication.stable.queueEntry
  apply queueValid entry
  rw [original]
  exact List.mem_cons_of_mem head member

/-- Every nonempty queue with present authority can publish its head under the
selected policy. No eventual-success or fairness assumption is required. -/
theorem publishHead_enabled {world : World} {resources : Resources} {head : Entry} {tail : List Entry}
    {profile : Profile} (worldValid : Atomics64.WellFormed world)
    (headValid : Valid world resources head profile) :
    ∃ result, publishHead world resources (head :: tail) profile = .ok result := by
  obtain ⟨output, changed⟩ := publish_enabled worldValid headValid
  exact ⟨(output.1, tail, output.2), by simp [publishHead, changed]⟩

end EDSL.OS.TSO64.Queue
