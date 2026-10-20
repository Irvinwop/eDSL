/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.Effects

namespace EDSL.OS.TSO64
open X86 AddressSpace

theorem WorkerValid.stable {before after : World} (frame : Stable before after)
    {worker : Worker} (valid : WorkerValid before worker) : WorkerValid after worker :=
  ⟨frame.resources valid.1, fun pending member => frame.pending (valid.2 pending member)⟩

theorem install_valid {state : State} {tid : Nat} {world : World} {worker : Worker}
    (valid : WellFormed state) (frame : Stable state.world world)
    (worldValid : Atomics64.WellFormed world) (workerValid : WorkerValid world worker) :
    WellFormed (install state tid world worker) := by
  refine ⟨worldValid, ?_⟩
  intro other member
  rcases List.mem_or_eq_of_mem_set member with old | rfl
  · exact (valid.2 other old).stable frame
  · exact workerValid

theorem QueueEffect.valid {state : State} {worker : Worker} {instruction : Sequential.Instruction}
    {pending : List Pending} (effect : QueueEffect state worker instruction pending)
    (valid : WorkerValid state.world worker) :
    ∀ entry ∈ pending, PendingValid state.world worker.resources entry := by
  cases effect with
  | unchanged => exact valid.2
  | enqueued intent grant =>
    intro entry member
    rcases List.mem_append.mp member with old | newest
    · exact valid.2 entry old
    · have same := List.mem_singleton.mp newest
      subst entry
      exact grantFor_sound grant

theorem OrdinaryEffect.wellFormed {state : State} {tid : Nat} {worker : Worker}
    {instruction : Sequential.Instruction} {af : Bool} {result : State × Observation}
    (effect : OrdinaryEffect state tid worker instruction af result)
    (valid : WellFormed state) (live : state.workers[tid]? = some worker) : WellFormed result.1 := by
  have workerValid := valid.2 worker (List.mem_of_getElem? live)
  cases effect with
  | intro supported bounds decoded reads queue step finish =>
    have pending := queue.valid workerValid
    cases finish with
    | next outcome => exact install_valid valid (Stable.refl _) valid.1 ⟨workerValid.1, pending⟩
    | returned outcome => exact install_valid valid (Stable.refl _) valid.1 ⟨workerValid.1, pending⟩

theorem LockedEffect.wellFormed {state : State} {tid : Nat} {worker : Worker}
    {instruction : LockedAdd64.Instruction} {result : State × Observation}
    (effect : LockedEffect state tid worker instruction result)
    (valid : WellFormed state) (live : state.workers[tid]? = some worker) : WellFormed result.1 := by
  have workerValid := valid.2 worker (List.mem_of_getElem? live)
  cases effect with
  | blocked => exact valid
  | rmw bounds empty decoded selected changed executed =>
    have frame := fetchAdd_stable changed
    exact install_valid valid frame (Atomics64.fetchAdd_wellFormed _ _ _ _ _ valid.1 changed)
      ⟨frame.resources workerValid.1, fun pending member => frame.pending (workerValid.2 pending member)⟩

theorem issue_wellFormed {state : State} {tid : Nat} {af : Bool} {result : State × Observation}
    (valid : WellFormed state) (success : issue state tid af = .ok result) : WellFormed result.1 := by
  obtain ⟨worker, live, _, _, _, instruction, _, effect⟩ := issue_effect success
  cases instruction with
  | ordinary instruction => exact effect.wellFormed valid live
  | locked instruction => exact effect.wellFormed valid live

theorem drain_wellFormed {state : State} {tid : Nat} {result : State × Observation}
    (valid : WellFormed state) (success : drain state tid = .ok result) : WellFormed result.1 := by
  obtain ⟨worker, head, tail, output, live, pending, _, changed, same⟩ := drain_effect success
  have workerValid := valid.2 worker (List.mem_of_getElem? live)
  have frame := (publication changed).stable
  rw [same]
  apply install_valid valid frame (Atomics64.mutate_wellFormed _ _ _ valid.1 changed)
  refine ⟨frame.resources workerValid.1, ?_⟩
  intro entry member
  exact frame.pending (workerValid.2 entry (by rw [pending]; exact List.mem_cons_of_mem head member))

/-- Resource/lifetime and OS invariants are consequences of actual gates and
checked effects. No successor-WF test appears in the executable scheduler. -/
theorem step_wellFormed {state : State} {action : Action} {result : State × Observation}
    (valid : WellFormed state) (success : step state action = .ok result) : WellFormed result.1 := by
  cases action with
  | issue tid af => exact issue_wellFormed valid success
  | drain tid => exact drain_wellFormed valid success

theorem step_stable {state : State} {action : Action} {result : State × Observation}
    (success : step state action = .ok result) : Stable state.world result.1.world := by
  cases action with
  | issue tid af =>
    obtain ⟨_, _, _, _, _, instruction, _, effect⟩ := issue_effect success
    cases instruction with
    | ordinary instruction =>
      cases effect with
      | intro supported bounds decoded reads queue step finish => cases finish <;> exact Stable.refl _
    | locked instruction =>
      cases effect with
      | blocked => exact Stable.refl _
      | rmw bounds empty decoded selected changed executed => exact fetchAdd_stable changed
  | drain tid =>
    obtain ⟨_, _, _, _, _, _, _, changed, same⟩ := drain_effect success
    rw [same]
    exact (publication changed).stable

theorem install_peer {state : State} {tid peer : Nat} {world : World} {worker : Worker}
    (different : peer ≠ tid) : (install state tid world worker).workers[peer]? = state.workers[peer]? :=
  List.getElem?_set_ne different.symm

/-- Peer RF/RIP/flags/phase, original resources, and pending grants survive
every successful issue/drain literally, without stale RAM in the context. -/
theorem step_peer {state : State} {action : Action} {result : State × Observation} {peer : Nat}
    (success : step state action = .ok result)
    (different : peer ≠ (match action with | .issue tid _ | .drain tid => tid)) :
    result.1.workers[peer]? = state.workers[peer]? := by
  cases action with
  | issue tid af =>
    obtain ⟨_, _, _, _, _, instruction, _, effect⟩ := issue_effect success
    cases instruction with
    | ordinary instruction =>
      cases effect with
      | intro supported bounds decoded reads queue step finish => cases finish <;> exact install_peer different
    | locked instruction =>
      cases effect with
      | blocked => rfl
      | rmw => exact install_peer different
  | drain tid =>
    obtain ⟨_, _, _, _, _, _, _, _, same⟩ := drain_effect success
    rw [same]
    exact install_peer different

theorem schedule_cons_ok {state : State} {action : Action} {rest : List Action}
    {result : State × List Observation} (success : schedule state (action :: rest) = .ok result) :
    ∃ head tail, step state action = .ok head ∧ schedule head.1 rest = .ok tail ∧
      result = (tail.1, head.2 :: tail.2) := by
  cases first : step state action with
  | error fault => simp [schedule, first] at success
  | ok head =>
    cases following : schedule head.1 rest with
    | error fault => simp [schedule, first, following] at success
    | ok tail =>
      simp [schedule, first, following] at success
      exact ⟨head, tail, rfl, following, success.symm⟩

theorem schedule_wellFormed {state : State} {actions : List Action} {result : State × List Observation}
    (valid : WellFormed state) (success : schedule state actions = .ok result) : WellFormed result.1 := by
  induction actions generalizing state result with
  | nil => simp only [schedule, Except.ok.injEq] at success; subst result; exact valid
  | cons action rest ih =>
    obtain ⟨head, tail, first, following, same⟩ := schedule_cons_ok success
    rw [same]
    exact ih (result := tail) (step_wellFormed valid first) following

/-- The local view is always synthesized from CURRENT published RAM; its byte
origin is the newest matching own pending byte, or the current shared byte. -/
theorem local_read (state : State) (worker : Worker) (query : Word) :
    (localCPU state worker).memory.read query =
      (StoreBuffer.Mixed.forward (payload worker.pending) query).or ((published state.world).read query) :=
  StoreBuffer.Mixed.view_read _ _ _

theorem drain_fifo {state : State} {tid : Nat} {result : State × Observation}
    (success : drain state tid = .ok result) :
    ∃ worker head tail world,
      state.workers[tid]? = some worker ∧ worker.pending = head :: tail ∧
      result = (install state tid world { worker with pending := tail }, .drained tid head) ∧
      published world = head.store.publish (published state.world) ∧
      StoreBuffer.Mixed.view (published world) (payload tail) = (localCPU state worker).memory ∧
      result.2.retired = 0 := by
  obtain ⟨worker, head, tail, output, live, pending, _, changed, same⟩ := drain_effect success
  have effect := publication changed
  refine ⟨worker, head, tail, output.1, live, pending, same, effect.projection, ?_, ?_⟩
  · rw [effect.projection]
    change StoreBuffer.Mixed.view _ _ = StoreBuffer.Mixed.view _ (payload worker.pending)
    rw [pending]
    rfl
  · rw [same]; rfl

/-- A reachable queue always has a publication step; RET does not remove it.
This derives enabledness from the CURRENT invariant, without a future-success
or fairness hypothesis. -/
theorem drain_enabled {state : State} {tid : Nat} {worker : Worker} {head : Pending} {tail : List Pending}
    (valid : WellFormed state) (live : state.workers[tid]? = some worker)
    (pending : worker.pending = head :: tail) : ∃ result, drain state tid = .ok result := by
  have gate := (valid.2 worker (List.mem_of_getElem? live)).2 head (by rw [pending]; exact List.mem_cons_self)
  obtain ⟨world, changed⟩ := gate.2.enabled
  exact ⟨(install state tid world { worker with pending := tail }, .drained tid head),
    by simp [drain, live, pending, gate, changed, Except.mapError]⟩

end EDSL.OS.TSO64
