/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.WordProjection.Core

/-!
Projection of actual queue, publication and locked effects to the finite
managed-word reference fragment. These lemmas do not execute another scheduler.
In particular, the quiet queue case records only its endpoint: a caller must
still classify managed reads and supply their reference read steps.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.OS.TSO64.WordProjection
open X86 Concurrency

/-- Filtering an actual ordinary enqueue retains the complete managed FIFO. -/
theorem managed_enqueue_ordinary (entries : List Pending) (ticket : Ownership.Ticket)
    (store : Store) :
    managed (entries ++ [.ordinary ticket store]) = managed entries := by
  rw [managed_append]
  exact List.append_nil _

/-- An actual managed enqueue becomes a newest-first reference prepend. -/
theorem managed_enqueue (entries : List Pending) (reference : Queue.ManagedRef)
    (value : Word) (occurrence : Nat) :
    (managed (entries ++ [.managed reference value occurrence])).reverse =
      (reference.handle.cell, value) :: (managed entries).reverse := by
  rw [managed_append, List.reverse_append]
  rfl

/-- Exact enqueue endpoint, including every peer's buffer and current memory.
The pending equality describes the actual installation, not its projection. -/
theorem managed_enqueue_install {state : TSO64.State} {tid : Nat} {world : World}
    {worker replacement : Worker} {reference : Queue.ManagedRef} {value : Word}
    {occurrence : Nat} (live : state.workers[tid]? = some worker)
    (sameMemory : memory world = memory state.world)
    (pending : replacement.pending =
      worker.pending ++ [.managed reference value occurrence]) :
    project (install state tid world replacement) =
      TSOWord.writeBuffered (project state) tid reference.handle.cell value := by
  refine reference_ext (first := project (install state tid world replacement))
    (second := TSOWord.writeBuffered (project state) tid reference.handle.cell value) sameMemory ?_ rfl
  change buffers (install state tid world replacement) =
    TSOWord.setBuffer (buffers state) tid
      ((reference.handle.cell, value) :: buffers state tid)
  rw [buffers_install live, pending, managed_enqueue, buffers_live live]

/-- Store classification and endpoint algebra for an actual ordinary effect.
`quiet` does not assert that an instruction is semantically silent: managed
loads also have no store intent and need a separate read witness from callers. -/
inductive QueueProjection (state : TSO64.State) (tid : Nat) (worker : Worker)
    (instruction : Sequential.Instruction) (result : TSO64.State × Observation)
    (profile : Profile) : Prop where
  | quiet (intent : storeIntent instruction (localCPU state worker) = none)
      (same : project result.1 = project state) :
      QueueProjection state tid worker instruction result profile
  | owned (store : Store) (ticket : Ownership.Ticket)
      (intent : storeIntent instruction (localCPU state worker) = some store)
      (admission : Queue.Admission state.world worker.resources store worker.nextStore
        profile (.ordinary ticket store))
      (same : project result.1 = project state) :
      QueueProjection state tid worker instruction result profile
  | managed (store : Store) (reference : Queue.ManagedRef) (value : Word)
      (occurrence : Nat)
      (intent : storeIntent instruction (localCPU state worker) = some store)
      (admission : Queue.Admission state.world worker.resources store worker.nextStore
        profile (.managed reference value occurrence))
      (same : project result.1 =
        TSOWord.writeBuffered (project state) tid reference.handle.cell value) :
      QueueProjection state tid worker instruction result profile

/-- Match the real admission and finish effects; no projected poststate is
assumed. Both ordinary retirement and return install the admitted actual FIFO. -/
theorem ordinary_queue_projection {state : TSO64.State} {tid : Nat} {worker : Worker}
    {instruction : Sequential.Instruction} {af : Bool}
    {result : TSO64.State × Observation} {profile : Profile}
    (effect : OrdinaryEffect state tid worker instruction af result profile)
    (live : state.workers[tid]? = some worker) :
    QueueProjection state tid worker instruction result profile := by
  cases effect with
  | intro supported bounds decoded reads queue executed finish =>
    cases queue with
    | unchanged intent =>
      refine .quiet intent ?_
      cases finish <;> exact erased_install live rfl rfl
    | enqueued intent admission =>
      cases admission with
      | ordinary ticket selected =>
        refine .owned _ ticket intent (.ordinary ticket selected) ?_
        cases finish <;> exact erased_install live rfl (managed_enqueue_ordinary _ _ _)
      | managed reference value ordinaryAbsent shared qword selected =>
        refine .managed _ reference value _ intent
          (.managed reference value ordinaryAbsent shared qword selected) ?_
        cases finish <;> exact managed_enqueue_install live rfl rfl

/-- Whole projected memory is retained when the actual observation has no
managed write. Ordinary publication uses the checked registered-cell frame
inside `memory_step`, for every current location. -/
theorem memory_step_unchanged {state : TSO64.State} {action : Action}
    {result : TSO64.State × Observation} {profile : Profile} {family : RMWFamily}
    (valid : WellFormed state profile) (success : step state action profile family = .ok result)
    (silent : PublishedHistory.writeOf result.2 = none) :
    memory result.1.world = memory state.world := by
  funext query
  simpa only [silent] using memory_step valid success query

/-- Turn the exact current-memory effect into reference memory update algebra.
The update's orientation is normalized without an address-distinctness premise. -/
theorem memory_step_written {state : TSO64.State} {action : Action}
    {result : TSO64.State × Observation} {profile : Profile} {family : RMWFamily}
    {cause : PublishedHistory.WriteCause}
    (valid : WellFormed state profile) (success : step state action profile family = .ok result)
    (written : PublishedHistory.writeOf result.2 = some cause) :
    memory result.1.world =
      TSOWord.setMemory (memory state.world) cause.cell cause.value := by
  funext query
  have actual := memory_step valid success query
  simp only [written] at actual
  change memory result.1.world query =
    if query = cause.cell then some cause.value else memory state.world query
  by_cases selected : query = cause.cell
  · subst query
    simpa only [↓reduceIte] using actual
  · simpa only [ite_eq_right selected, ite_eq_right (Ne.symm selected)] using actual

/-- Exact observed tags distinguish an erased ordinary head from one actual
managed publication. Neither constructor changes which concrete head drained. -/
inductive DrainProjection (state : TSO64.State) (tid : Nat)
    (result : TSO64.State × Observation) : Prop where
  | ordinary (ticket : Ownership.Ticket) (store : Store)
      (observed : result.2 = .drained tid (.ordinary ticket store))
      (same : project result.1 = project state) :
      DrainProjection state tid result
  | managed (reference : Queue.ManagedRef) (value : Word) (occurrence : Nat)
      (observed : result.2 = .drained tid (.managed reference value occurrence))
      (path : TSOWord.Path (project state) [.tau] (project result.1)) :
      DrainProjection state tid result

/-- Project the actual FIFO head only. Ordinary heads stutter after their
checked frame; a managed head is the oldest managed entry in the reversed
buffer and publishes through exactly one reference Tau transition. -/
theorem drain_projection {state : TSO64.State} {tid : Nat}
    {result : TSO64.State × Observation} {profile : Profile}
    (valid : WellFormed state profile)
    (success : drain state tid profile = .ok result) :
    DrainProjection state tid result := by
  have stepped : step state (.drain tid) profile = .ok result := success
  obtain ⟨worker, head, tail, output, live, fifo, _gate, _changed, same⟩ :=
    drain_effect success
  subst result
  cases head with
  | ordinary ticket store =>
    refine .ordinary ticket store rfl ?_
    apply erased_install live (memory_step_unchanged valid stepped rfl)
    change managed tail = managed worker.pending
    rw [fifo]
    rfl
  | managed reference value occurrence =>
    refine .managed reference value occurrence rfl ?_
    have oldest : (project state).buffers tid =
        (managed tail).reverse ++ [(reference.handle.cell, value)] := by
      change buffers state tid = _
      rw [buffers_live live, fifo]
      simp only [managed, List.reverse_cons]
    have memoryChanged : memory output.1 =
        TSOWord.setMemory (memory state.world) reference.handle.cell value :=
      memory_step_written (cause := .buffered tid reference value occurrence) valid stepped rfl
    have endpoint : project (install state tid output.1 { worker with pending := tail }) =
        TSOWord.publish (project state) tid (managed tail).reverse
          reference.handle.cell value :=
      reference_ext memoryChanged (buffers_install live) rfl
    rw [endpoint]
    exact TSOWord.Path.cons (TSOWord.Step.publishOldest (Or.inl rfl) oldest)
      (TSOWord.Path.nil _)

/-- Reuse the actual current-world machine/OS bridge, the full concrete FIFO
emptiness check, the primitive's old read and the exact projected memory step.
The reference helper expands to acquire/read/enqueue/publication/unlock, keeping
every peer buffer and restoring the free lock, including for unchanged values. -/
theorem rmw_path_of_effect {state : TSO64.State} {action : Action} {tid : Nat}
    {worker : Worker} {instruction : AddRMW64.Instruction}
    {identifier : Atomics64.HandleId64} {output : World × Atomics64.FetchAddEvent}
    {machine : AddRMW64.Observation} {profile : Profile} {family : RMWFamily}
    (valid : WellFormed state profile) (live : state.workers[tid]? = some worker)
    (empty : worker.pending = [])
    (effect : Atomics64.AddRMWMachineEffect state.world worker.resources.actor identifier
      (sharedCPU state worker) instruction output machine)
    (success : step state action profile family =
      .ok (install state tid output.1 { worker with context := .ofCPU machine.state },
        .rmw tid output.2)) :
    TSOWord.Path (project state)
      [.lock tid, .read tid output.2.cell output.2.arithmetic.event.before,
        .write tid output.2.cell output.2.arithmetic.event.after, .tau, .unlock tid]
      (project (install state tid output.1 { worker with context := .ofCPU machine.state })) := by
  have bufferEmpty : (project state).buffers tid = [] := by
    change buffers state tid = []
    rw [buffers_live live, empty]
    rfl
  obtain ⟨handle, cell, _found, _acts, linked, _cellValid, identity, address⟩ := effect.context
  have eventLive : state.world.cells output.2.cell = some cell := by
    rw [identity]
    exact linked
  have primitiveOld := Atomics64.fetchAdd_old _ _ _ _ _ effect.checked
  rw [address] at primitiveOld
  have memoryOld : (project state).memory output.2.cell =
      some output.2.arithmetic.event.before := memory_read eventLive primitiveOld
  have memoryChanged : memory output.1 =
      TSOWord.setMemory (memory state.world) output.2.cell output.2.arithmetic.event.after :=
    memory_step_written (cause := .rmw tid output.2) valid success rfl
  have endpoint :
      project (install state tid output.1 { worker with context := .ofCPU machine.state }) =
        { project state with memory := (TSOWord.setMemory (project state).memory
            output.2.cell output.2.arithmetic.event.after) } := by
    rw [project_install live, ← buffers_live live, setBuffer_current]
    exact reference_ext memoryChanged rfl rfl
  rw [endpoint]
  exact TSOWord.lockedWrite_path (project state) tid output.2.cell
    output.2.arithmetic.event.before output.2.arithmetic.event.after rfl bufferEmpty memoryOld

/-- An actual successful RMW observation has the explicit five-label reference
path. The origin supplies the checked joint effect and the real empty own FIFO;
no delta is reconstructed from event values and no atomic shortcut rule is used. -/
theorem rmw_path {state after : TSO64.State} {action : Action} {profile : Profile}
    {family : RMWFamily} {tid : Nat} {event : Atomics64.FetchAddEvent}
    (valid : WellFormed state profile)
    (success : step state action profile family = .ok (after, .rmw tid event)) :
    TSOWord.Path (project state)
      [.lock tid, .read tid event.cell event.arithmetic.event.before,
        .write tid event.cell event.arithmetic.event.after, .tau, .unlock tid]
      (project after) := by
  cases step_origin success with
  | ordinary live running code caller fetched effect =>
    cases effect with
    | intro supported bounds decoded reads queue executed finish => cases finish
  | rmw live running code caller fetched bounds empty grant effect =>
    exact rmw_path_of_effect valid live empty (RMWFamily.MachineEffect.arithmetic effect) success

end EDSL.OS.TSO64.WordProjection
