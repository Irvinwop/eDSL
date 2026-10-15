/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.CounterThreads

namespace EDSL.CounterCertificate
open X86 OS.AddressSpace OS.CounterThreads

def accepts (candidate : List Byte) : Bool := decide (candidate = bytes)

/-- Resource and private-context prerequisites; the artifact supplies the
missing code-binding proof for each registered entry. Actor IDs and native
start/join conformance retain their explicit abstract-model interpretation. -/
def Prepared (state : OS.CounterThreads.State) : Prop :=
  OS.Atomics.WellFormed state.shared ∧ ∀ identifier worker, state.workers identifier = some worker →
    identifier < state.nextThread ∧ (CodeAt (toMemory state.shared.shared.resources.space) worker.entry.rip bytes →
      WorkerValid state.shared identifier worker)

def Outcome (state : OS.CounterThreads.State) (address : Word) (initial : BitVec 32) (joined : OS.CounterThreads.State × List Word) : Prop :=
  WellFormed joined.1 ∧ joined.2 = List.replicate (liveIds state).length 0 ∧
    (∀ identifier, joined.1.workers identifier = none) ∧
    loadDWord (toMemory joined.1.shared.shared.resources.space) address = .ok (initial + BitVec.ofNat 32 (requested state))

def Execution (state : OS.CounterThreads.State) (address : Word) (initial : BitVec 32) : Prop :=
  ∃ finished events selections joined,
    finishWorkers state (liveIds state) = .ok (finished, events) ∧
    schedule state selections = .ok (finished, events) ∧
    collect finished 0 (liveIds finished) = .ok joined ∧ Outcome state address initial joined

/-- Every successful completing supplied schedule and checked collection has
the same independent counter/return/resource outcome. Progress is separate. -/
def CompletedSpecification (state : OS.CounterThreads.State) (address : Word) (initial : BitVec 32) : Prop :=
  ∀ selections result, schedule state selections = .ok result →
    (∀ identifier worker, result.1.workers identifier = some worker → worker.phase = .completed) →
    ∀ joined, collect result.1 0 (liveIds result.1) = .ok joined → Outcome state address initial joined

theorem sound (candidate : List Byte) (accepted : accepts candidate = true)
    (state : OS.CounterThreads.State) (address : Word) (initial : BitVec 32) (prepared : Prepared state)
    (code : ∀ identifier worker, state.workers identifier = some worker →
      CodeAt (toMemory state.shared.shared.resources.space) worker.entry.rip candidate)
    (allAt : AllAt state address)
    (observed : loadDWord (toMemory state.shared.shared.resources.space) address = .ok initial)
    (started : ∀ identifier worker, state.workers identifier = some worker → worker.phase = .entry) :
    Execution state address initial ∧ CompletedSpecification state address initial := by
  have same : candidate = bytes := of_decide_eq_true accepted
  subst candidate
  have valid : WellFormed state := ⟨prepared.1, fun identifier worker live =>
    ⟨(prepared.2 _ _ live).1, (prepared.2 _ _ live).2 (code identifier worker live)⟩⟩
  constructor
  · obtain ⟨finished, events, selections, joined, finishedOk, scheduled, collected, joinedValid, zeros, removed, counter⟩ :=
      finish_collect_counter state address initial valid allAt observed started
    have ids := schedule_liveIds _ _ _ valid scheduled
    exact ⟨finished, events, selections, joined, finishedOk, scheduled, collected,
      joinedValid, by simpa only [ids] using zeros, removed, counter⟩
  · intro selections result scheduled completed joined collected
    have finalValid := schedule_wellFormed _ _ _ valid scheduled
    have counter := completed_counter state selections result address initial valid allAt observed started scheduled completed
    obtain ⟨actual, actualCollected, joinedValid, zeros, removed, resources⟩ := collect_all result.1 finalValid completed
    have equal := Except.ok.inj (actualCollected.symm.trans collected)
    subst actual
    have ids := schedule_liveIds _ _ _ valid scheduled
    exact ⟨joinedValid, by simpa only [ids] using zeros, removed, by rw [resources]; exact counter⟩

end EDSL.CounterCertificate
