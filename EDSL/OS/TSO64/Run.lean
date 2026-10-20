/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.Frames

namespace EDSL.OS.TSO64
open X86 AddressSpace

/-- Exhaustive origin for an actual successful scheduler action. In particular
an atomic label carries the actual decoded instruction and joint current-world
bridge, rather than reconstructing an input from after minus before. -/
inductive Origin (state : State) : Action → State × Observation → Prop where
  | ordinary {tid af worker instruction result}
      (live : state.workers[tid]? = some worker)
      (running : worker.phase ≠ .returned)
      (code : LeaseCurrent state.world worker.resources.actor worker.resources.code)
      (caller : LeaseCurrent state.world worker.resources.actor worker.resources.caller)
      (fetched : decode (fetchCPU state worker) = .ok (.ordinary instruction))
      (effect : OrdinaryEffect state tid worker instruction af result) :
      Origin state (.issue tid af) result
  | blocked {tid af worker instruction}
      (live : state.workers[tid]? = some worker)
      (running : worker.phase ≠ .returned)
      (code : LeaseCurrent state.world worker.resources.actor worker.resources.code)
      (caller : LeaseCurrent state.world worker.resources.actor worker.resources.caller)
      (fetched : decode (fetchCPU state worker) = .ok (.locked instruction))
      (bounds : codeFits worker instruction.length) (nonempty : worker.pending ≠ []) :
      Origin state (.issue tid af) (state, .blocked tid)
  | rmw {tid af worker instruction identifier output machine}
      (live : state.workers[tid]? = some worker)
      (running : worker.phase ≠ .returned)
      (code : LeaseCurrent state.world worker.resources.actor worker.resources.code)
      (caller : LeaseCurrent state.world worker.resources.actor worker.resources.caller)
      (fetched : decode (fetchCPU state worker) = .ok (.locked instruction))
      (bounds : codeFits worker instruction.length)
      (empty : worker.pending = [])
      (grant : identifier ∈ worker.resources.atomics)
      (effect : Atomics64.FetchAddMachineEffect state.world worker.resources.actor identifier
        (sharedCPU state worker) instruction output machine) :
      Origin state (.issue tid af)
        (install state tid output.1 { worker with context := .ofCPU machine.state }, .rmw tid output.2)
  | drained {tid worker head tail output}
      (live : state.workers[tid]? = some worker) (fifo : worker.pending = head :: tail)
      (gate : PendingValid state.world worker.resources head)
      (changed : Atomics64.mutate state.world (operation worker.resources.actor head.ticket head.store) = .ok output)
      (effect : Publication state.world output.1 head.store) :
      Origin state (.drain tid)
        (install state tid output.1 { worker with pending := tail }, .drained tid head)

theorem step_origin {state : State} {action : Action} {result : State × Observation}
    (success : step state action = .ok result) : Origin state action result := by
  cases action with
  | issue tid af =>
    obtain ⟨worker, live, running, code, caller, instruction, fetched, effect⟩ := issue_effect success
    cases instruction with
    | ordinary instruction => exact .ordinary live running code caller fetched effect
    | locked instruction =>
      cases effect with
      | blocked bounds nonempty => exact .blocked live running code caller fetched bounds nonempty
      | rmw bounds empty decoded selected changed executed =>
        exact .rmw live running code caller fetched bounds empty (atomicFor_sound selected).1
          (locked_coupled decoded selected changed executed)
  | drain tid =>
    obtain ⟨worker, head, tail, output, live, fifo, gate, changed, same⟩ := drain_effect success
    rw [same]
    exact .drained live fifo gate changed (publication changed)

/-- Blocking returns the WHOLE input state, not just a matching observation.
It emits no event and retires no user instruction. -/
theorem blocked_unchanged {state : State} {action : Action} {after : State} {tid : Nat}
    (success : step state action = .ok (after, .blocked tid)) : after = state := by
  cases step_origin success with
  | ordinary live running code caller fetched effect =>
    cases effect with
    | intro supported bounds decoded reads queue step finish => cases finish
  | blocked => rfl

/-- All executable code, including code outside worker loans, is retained by
every successful action. Ordinary stores cannot publish into executable bytes. -/
theorem step_code {state : State} {action : Action} {result : State × Observation}
    (success : step state action = .ok result) {base : Word} {bytes : List Byte}
    (code : CodeAt (published state.world) base bytes) :
    CodeAt (published result.1.world) base bytes := by
  cases step_origin success with
  | ordinary live running codeLease caller fetched effect =>
    cases effect with
    | intro supported bounds decoded reads queue step finish => cases finish <;> exact code
  | blocked => exact code
  | rmw live running codeLease caller fetched bounds empty grant effect =>
    have preserved := effect.preserves_all_code base bytes code
    rw [effect.memory] at preserved
    exact preserved
  | drained live fifo gate changed effect =>
    dsimp only [install]
    rw [effect.projection]
    exact dataOnly_preserves_code gate.2.2.2.1 code

private theorem install_resource_frame {state : State} {tid thread : Nat} {world : World}
    {subject replacement prior current : Worker}
    (subjectLive : state.workers[tid]? = some subject)
    (priorLive : state.workers[thread]? = some prior)
    (currentLive : (install state tid world replacement).workers[thread]? = some current)
    (resources : replacement.resources = subject.resources) :
    current.resources = prior.resources := by
  by_cases same : thread = tid
  · subst thread
    have priorEq : prior = subject := Option.some.inj (priorLive.symm.trans subjectLive)
    have installed : (install state tid world replacement).workers[tid]? = some replacement :=
      List.getElem?_set_self (List.getElem_of_getElem? subjectLive).1
    have currentEq : current = replacement := Option.some.inj (currentLive.symm.trans installed)
    subst prior
    subst current
    exact resources
  · rw [install_peer same] at currentLive
    have currentEq : current = prior := Option.some.inj (currentLive.symm.trans priorLive)
    subst current
    rfl

/-- Every worker retains its ORIGINAL code/caller resources, owner, ticket and
atomic grant lists across every action, including its own RSP-changing RMW. -/
theorem step_resources {state : State} {action : Action} {result : State × Observation}
    (success : step state action = .ok result) {thread : Nat} {prior current : Worker}
    (priorLive : state.workers[thread]? = some prior)
    (currentLive : result.1.workers[thread]? = some current) : current.resources = prior.resources := by
  cases step_origin success with
  | ordinary live running code caller fetched effect =>
    cases effect with
    | intro supported bounds decoded reads queue step finish =>
      cases finish <;> exact install_resource_frame live priorLive currentLive rfl
  | blocked =>
    have same : current = prior := Option.some.inj (currentLive.symm.trans priorLive)
    subst current
    rfl
  | rmw live running code caller fetched bounds empty grant effect =>
    exact install_resource_frame live priorLive currentLive rfl
  | drained live fifo gate changed effect => exact install_resource_frame live priorLive currentLive rfl

/-- Removing the checked ticket wrapper refines EXACTLY the existing Mixed
FIFO primitive. OS publication is checked; Mixed itself grants no authority. -/
theorem drain_mixed {state : State} {tid : Nat} {result : State × Observation}
    (success : drain state tid = .ok result) :
    ∃ prior current, state.workers[tid]? = some prior ∧ result.1.workers[tid]? = some current ∧
      current.context = prior.context ∧ current.resources = prior.resources ∧ current.phase = prior.phase ∧
      StoreBuffer.Mixed.publishOldest (published state.world) (payload prior.pending) =
        some (published result.1.world, payload current.pending) ∧ result.2.retired = 0 := by
  obtain ⟨worker, head, tail, output, live, pending, gate, changed, same⟩ := drain_effect success
  let current : Worker := { worker with pending := tail }
  refine ⟨worker, current, live, ?_, rfl, rfl, rfl, ?_, ?_⟩
  · rw [same]
    exact List.getElem?_set_self (List.getElem_of_getElem? live).1
  · rw [same]
    change StoreBuffer.Mixed.publishOldest (published state.world) (payload worker.pending) =
      some (published output.1, payload tail)
    rw [pending, (publication changed).projection]
    rfl
  · rw [same]; rfl

/-- Finite publication of any reachable worker, including an already returned
one. The suffix is exactly its pending length, with no fairness or future
success assumption. Context, phase and original resources do not advance. -/
theorem publish_worker (count : Nat) {state : State} {tid : Nat} {worker : Worker}
    (valid : WellFormed state) (live : state.workers[tid]? = some worker)
    (length : worker.pending.length = count) :
    ∃ result final,
      schedule state (List.replicate count (.drain tid)) = .ok result ∧
      result.1.workers[tid]? = some final ∧ final.pending = [] ∧
      final.context = worker.context ∧ final.phase = worker.phase ∧ final.resources = worker.resources ∧
      StoreBuffer.Mixed.view (published result.1.world) (payload final.pending) = (localCPU state worker).memory ∧
      (∀ observation ∈ result.2, observation.retired = 0) := by
  induction count generalizing state worker with
  | zero =>
    have empty : worker.pending = [] := List.length_eq_zero_iff.mp length
    exact ⟨(state, []), worker, rfl, live, empty, rfl, rfl, rfl, rfl, by simp⟩
  | succ count ih =>
    cases pending : worker.pending with
    | nil => simp [pending] at length
    | cons head tail =>
      have gate := (valid.2 worker (List.mem_of_getElem? live)).2 head (by rw [pending]; exact List.mem_cons_self)
      obtain ⟨world, changed⟩ := gate.2.enabled
      let nextWorker : Worker := { worker with pending := tail }
      let after := install state tid world nextWorker
      have drained : drain state tid = .ok (after, .drained tid head) := by
        simp [drain, live, pending, gate, changed, Except.mapError, after, nextWorker]
      have afterLive : after.workers[tid]? = some nextWorker :=
        List.getElem?_set_self (List.getElem_of_getElem? live).1
      have tailLength : nextWorker.pending.length = count := by
        simp only [pending, List.length_cons] at length
        exact Nat.add_right_cancel length
      obtain ⟨result, final, scheduled, finalLive, empty, context, phase, resources, view, retired⟩ :=
        ih (drain_wellFormed valid drained) afterLive tailLength
      refine ⟨(result.1, .drained tid head :: result.2), final, ?_, finalLive, empty,
        context, phase, resources, ?_, ?_⟩
      · simp [List.replicate_succ, schedule, step, drained, scheduled]
      · apply view.trans
        change StoreBuffer.Mixed.view (published world) (payload tail) = _
        rw [(publication changed).projection]
        change _ = StoreBuffer.Mixed.view _ (payload worker.pending)
        rw [pending]
        rfl
      · intro observation member
        rcases List.mem_cons.mp member with rfl | rest
        · rfl
        · exact retired observation rest

end EDSL.OS.TSO64
