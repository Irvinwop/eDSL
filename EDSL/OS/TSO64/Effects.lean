/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.Queue.Publication
import EDSL.OS.TSO64.Setup

namespace EDSL.OS.TSO64
open X86 AddressSpace

inductive QueueEffect (state : State) (worker : Worker) (instruction : Sequential.Instruction) :
    Queue.Cursor → (profile : Profile := .ownedOnly) → Prop where
  | unchanged {profile : Profile}
      (intent : storeIntent instruction (localCPU state worker) = none) :
      QueueEffect state worker instruction ⟨worker.pending, worker.nextStore⟩ profile
  | enqueued {store : Store} {entry : Pending} {profile : Profile}
      (intent : storeIntent instruction (localCPU state worker) = some store)
      (admission : Queue.Admission state.world worker.resources store worker.nextStore profile entry) :
      QueueEffect state worker instruction ⟨worker.pending ++ [entry], worker.nextStore + 1⟩ profile

theorem prepareQueue_effect {state : State} {worker : Worker} {instruction : Sequential.Instruction}
    {update : Queue.Cursor} {profile : Profile}
    (success : prepareQueue state worker instruction profile = .ok update) :
    QueueEffect state worker instruction update profile := by
  cases intent : storeIntent instruction (localCPU state worker) with
  | none =>
    simp [prepareQueue, intent] at success
    subst update
    exact .unchanged intent
  | some store =>
    have enqueued : (Queue.Cursor.mk worker.pending worker.nextStore).enqueue
        state.world worker.resources store profile = .ok update := by
      simpa only [prepareQueue, intent] using success
    obtain ⟨entry, admission, pending, counter⟩ := Queue.Cursor.enqueue_effect
      ⟨worker.pending, worker.nextStore⟩ state.world worker.resources store profile update enqueued
    rcases update with ⟨entries, nextStore⟩
    change entries = worker.pending ++ [entry] at pending
    change nextStore = worker.nextStore + 1 at counter
    subst entries
    subst nextStore
    exact .enqueued intent admission

inductive FinishEffect (state : State) (tid : Nat) (worker : Worker)
    (pending : List Pending) (observation : Sequential.Observation) :
    State × Observation → (nextStore : Nat := worker.nextStore) → Prop where
  | next {output} {nextStore : Nat} (outcome : observation.result = .next output) :
      FinishEffect state tid worker pending observation
        (install state tid state.world
          { worker with context := .ofCPU output, pending := pending, nextStore := nextStore }, .ordinary tid)
        nextStore
  | returned {output} {nextStore : Nat} (outcome : observation.result = .returned output) :
      FinishEffect state tid worker pending observation
        (install state tid state.world
          { worker with
            context := .ofCPU output
            phase := .returned
            pending := pending
            nextStore := nextStore }, .returned tid)
        nextStore

theorem finishOrdinary_effect {state : State} {tid : Nat} {worker : Worker} {pending : List Pending}
    {observation : Sequential.Observation} {result : State × Observation} {nextStore : Nat}
    (success : finishOrdinary state tid worker pending observation nextStore = .ok result) :
    FinishEffect state tid worker pending observation result nextStore := by
  cases outcome : observation.result <;> simp [finishOrdinary, outcome] at success
  all_goals subst result
  · exact .next outcome
  · exact .returned outcome

inductive OrdinaryEffect (state : State) (tid : Nat) (worker : Worker)
    (instruction : Sequential.Instruction) (af : Bool) (result : State × Observation)
    (profile : Profile := .ownedOnly) : Prop where
  | intro {update : Queue.Cursor} {observation : Sequential.Observation}
      (supported : supported instruction = true)
      (bounds : codeFits worker instruction.length)
      (decoded : Sequential.decodeAt (localCPU state worker) = .ok instruction)
      (reads : ∃ units, (instruction.operandReads (localCPU state worker)).mapM
        (fun read => checkRead state worker read profile) = .ok units)
      (queue : QueueEffect state worker instruction update profile)
      (step : Sequential.step af (localCPU state worker) = .ok observation)
      (finish : FinishEffect state tid worker update.pending observation result update.nextStore) :
      OrdinaryEffect state tid worker instruction af result profile

theorem ordinary_effect {state : State} {tid : Nat} {worker : Worker}
    {instruction : Sequential.Instruction} {af : Bool} {result : State × Observation} {profile : Profile}
    (success : ordinary state tid worker instruction af profile = .ok result) :
    OrdinaryEffect state tid worker instruction af result profile := by
  by_cases admitted : supported instruction = true
  · by_cases bounds : codeFits worker instruction.length
    · cases decoded : Sequential.decodeAt (localCPU state worker) with
      | error fault => simp [ordinary, admitted, bounds, decoded, Except.mapError] at success
      | ok actual =>
        by_cases same : actual = instruction
        · subst actual
          cases reads : (instruction.operandReads (localCPU state worker)).mapM
              (fun read => checkRead state worker read profile) with
          | error fault => simp [ordinary, admitted, bounds, decoded, reads, Except.mapError] at success
          | ok units =>
            cases pending : prepareQueue state worker instruction profile with
            | error fault => simp [ordinary, admitted, bounds, decoded, reads, pending, Except.mapError] at success
            | ok update =>
              cases executed : Sequential.execute (localCPU state worker) instruction af with
              | error fault => simp [ordinary, admitted, bounds, decoded, reads, pending, executed, Except.mapError] at success
              | ok observation =>
                have finished : finishOrdinary state tid worker update.pending observation update.nextStore = .ok result := by
                  simpa [ordinary, admitted, bounds, decoded, reads, pending, executed, Except.mapError] using success
                exact .intro admitted bounds decoded ⟨units, reads⟩ (prepareQueue_effect pending)
                  (by rw [Sequential.step_eq_execute af decoded]; exact executed)
                  (finishOrdinary_effect finished)
        · simp [ordinary, admitted, bounds, decoded, same, Except.mapError] at success
    · simp [ordinary, admitted, bounds] at success
  · simp [ordinary, admitted] at success

inductive LockedEffect (state : State) (tid : Nat) (worker : Worker)
    (instruction : LockedAdd64.Instruction) : State × Observation → Prop where
  | blocked (bounds : codeFits worker instruction.length) (nonempty : worker.pending ≠ []) :
      LockedEffect state tid worker instruction (state, .blocked tid)
  | rmw {identifier handle cell output machine}
      (bounds : codeFits worker instruction.length) (empty : worker.pending = [])
      (decoded : LockedAdd64.decodeAt (sharedCPU state worker) = .ok instruction)
      (selected : atomicFor state.world worker.resources
        ((sharedCPU state worker).registers instruction.base) = some (identifier, handle, cell))
      (changed : Atomics64.fetchAdd state.world worker.resources.actor identifier
        ((sharedCPU state worker).registers instruction.source) = .ok output)
      (executed : LockedAdd64.step (sharedCPU state worker) = .ok machine) :
      LockedEffect state tid worker instruction
        (install state tid output.1 { worker with context := .ofCPU machine.state }, .rmw tid output.2)

theorem locked_effect {state : State} {tid : Nat} {worker : Worker}
    {instruction : LockedAdd64.Instruction} {result : State × Observation}
    (success : locked state tid worker instruction = .ok result) :
    LockedEffect state tid worker instruction result := by
  by_cases bounds : codeFits worker instruction.length
  · cases empty : worker.pending.isEmpty with
    | false =>
      simp [locked, bounds, empty] at success
      subst result
      exact .blocked bounds (by intro same; simp [same] at empty)
    | true =>
      cases decoded : LockedAdd64.decodeAt (sharedCPU state worker) with
      | error fault => simp [locked, bounds, empty, decoded, Except.mapError] at success
      | ok actual =>
        by_cases same : actual = instruction
        · subst actual
          cases selected : atomicFor state.world worker.resources ((sharedCPU state worker).registers instruction.base) with
          | none => simp [locked, bounds, empty, decoded, selected, Except.mapError] at success
          | some grant =>
            rcases grant with ⟨identifier, handle, cell⟩
            cases changed : Atomics64.fetchAdd state.world worker.resources.actor identifier
                ((sharedCPU state worker).registers instruction.source) with
            | error fault => simp [locked, bounds, empty, decoded, selected, changed, Except.mapError] at success
            | ok output =>
              cases executed : LockedAdd64.step (sharedCPU state worker) with
              | error fault => simp [locked, bounds, empty, decoded, selected, changed, executed, Except.mapError] at success
              | ok machine =>
                simp [locked, bounds, empty, decoded, selected, changed, executed, Except.mapError] at success
                subst result
                exact .rmw bounds (List.isEmpty_iff.mp empty) decoded selected changed executed
        · simp [locked, bounds, empty, decoded, same, Except.mapError] at success
  · simp [locked, bounds] at success

/-- Converse from actual dispatch to the CURRENT OS/machine joint effect.
The captured delta is the actual prestate source, including base aliases/RSP. -/
theorem locked_coupled {state : State} {worker : Worker} {instruction : LockedAdd64.Instruction}
    {identifier : Atomics64.HandleId64} {handle : Atomics64.Handle} {cell : Atomics64.Cell}
    {output : World × Atomics64.FetchAddEvent} {machine : LockedAdd64.Observation}
    (decoded : LockedAdd64.decodeAt (sharedCPU state worker) = .ok instruction)
    (selected : atomicFor state.world worker.resources ((sharedCPU state worker).registers instruction.base) =
      some (identifier, handle, cell))
    (changed : Atomics64.fetchAdd state.world worker.resources.actor identifier
      ((sharedCPU state worker).registers instruction.source) = .ok output)
    (executed : LockedAdd64.step (sharedCPU state worker) = .ok machine) :
    Atomics64.FetchAddMachineEffect state.world worker.resources.actor identifier
      (sharedCPU state worker) instruction output machine := by
  obtain ⟨_, authorized, operand⟩ := atomicFor_sound selected
  have bridge := Atomics64.fetchAdd_step_effect _ _ _ _ _ _ _ _ changed authorized rfl operand.symm decoded
  have same := Except.ok.inj (bridge.step.symm.trans executed)
  subst machine
  exact bridge

theorem issue_effect {state : State} {tid : Nat} {af : Bool} {result : State × Observation} {profile : Profile}
    (success : issue state tid af profile = .ok result) :
    ∃ worker, state.workers[tid]? = some worker ∧ worker.phase ≠ .returned ∧
      LeaseCurrent state.world worker.resources.actor worker.resources.code ∧
      LeaseCurrent state.world worker.resources.actor worker.resources.caller ∧
      ∃ instruction, decode (fetchCPU state worker) = .ok instruction ∧
        (match instruction with
        | .ordinary instruction => OrdinaryEffect state tid worker instruction af result profile
        | .locked instruction => LockedEffect state tid worker instruction result) := by
  cases live : state.workers[tid]? with
  | none => simp [issue, live] at success
  | some worker =>
    by_cases returned : worker.phase = .returned
    · simp [issue, live, returned] at success
    · by_cases code : LeaseCurrent state.world worker.resources.actor worker.resources.code
      · by_cases caller : LeaseCurrent state.world worker.resources.actor worker.resources.caller
        · cases decoded : decode (fetchCPU state worker) with
          | error fault => simp [issue, live, returned, code, caller, decoded] at success
          | ok instruction =>
            refine ⟨worker, rfl, returned, code, caller, instruction, decoded, ?_⟩
            cases instruction with
            | ordinary instruction =>
              apply ordinary_effect
              simpa [issue, live, returned, code, caller, decoded] using success
            | locked instruction =>
              apply locked_effect
              simpa [issue, live, returned, code, caller, decoded] using success
        · simp [issue, live, returned, caller] at success
      · simp [issue, live, returned, code] at success

theorem drain_effect {state : State} {tid : Nat} {result : State × Observation} {profile : Profile}
    (success : drain state tid profile = .ok result) :
    ∃ worker head tail output,
      state.workers[tid]? = some worker ∧ worker.pending = head :: tail ∧
      PendingValid state.world worker.resources head profile ∧
      Queue.Effect state.world worker.resources head output ∧
      result = (install state tid output.1 { worker with pending := tail }, .drained tid head) := by
  cases live : state.workers[tid]? with
  | none => simp [drain, live] at success
  | some worker =>
    cases pending : worker.pending with
    | nil => simp [drain, live, pending] at success
    | cons head tail =>
      cases changed : Queue.publish state.world worker.resources head profile with
      | error fault => simp [drain, live, pending, changed] at success
      | ok output =>
        simp [drain, live, pending, changed] at success
        obtain ⟨gate, effect⟩ := Queue.publish_effect changed
        exact ⟨worker, head, tail, output, rfl, pending, gate, effect, success.symm⟩

/-- Successful default publication exposes the ordinary tag and the real outer
mutation. This holds for arbitrary initial inputs, without a WF or provenance
premise, so managed publication cannot enter the old quiet arithmetic history. -/
theorem drain_effect_owned {state : State} {tid : Nat} {result : State × Observation}
    (success : drain state tid .ownedOnly = .ok result) :
    ∃ worker ticket store tail output,
      state.workers[tid]? = some worker ∧
      worker.pending = .ordinary ticket store :: tail ∧
      PendingValid state.world worker.resources (.ordinary ticket store) .ownedOnly ∧
      Atomics64.mutate state.world (operation worker.resources.actor ticket store) = .ok output ∧
      result = (install state tid output.1 { worker with pending := tail },
        .drained tid (.ordinary ticket store)) := by
  obtain ⟨worker, head, tail, output, live, pending, gate, effect, same⟩ := drain_effect success
  cases effect with
  | ordinary changed => exact ⟨worker, _, _, tail, _, live, pending, gate, changed, same⟩
  | managed current changed =>
    exact False.elim (Queue.not_valid_managed_ownedOnly _ _ _ _ _ gate)

theorem drain_managed_ownedOnly {state : State} {tid : Nat} {worker : Worker}
    {reference : Queue.ManagedRef} {value : Word} {occurrence : Nat} {tail : List Pending}
    (live : state.workers[tid]? = some worker)
    (pending : worker.pending = .managed reference value occurrence :: tail) :
    drain state tid .ownedOnly = .error .resource := by
  simp [drain, live, pending, Queue.publish_managed_ownedOnly]

end EDSL.OS.TSO64
