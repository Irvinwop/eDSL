/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.Publication
import EDSL.OS.TSO64.Setup

namespace EDSL.OS.TSO64
open X86 AddressSpace

theorem grantFor_sound {world : World} {resources : Resources} {store : Store} {ticket : Ownership.Ticket}
    (selected : grantFor world resources store = some ticket) :
    ticket ∈ resources.grants ∧ StoreGate world resources.actor ticket store :=
  ⟨List.mem_of_find?_eq_some selected,
    of_decide_eq_true (List.find?_some (p := fun candidate => decide (StoreGate world resources.actor candidate store)) selected)⟩

theorem atomicFor_sound {world : World} {resources : Resources} {address : Word}
    {identifier : Atomics64.HandleId64} {handle : Atomics64.Handle} {cell : Atomics64.Cell}
    (selected : atomicFor world resources address = some (identifier, handle, cell)) :
    identifier ∈ resources.atomics ∧ Atomics64.authorize world resources.actor identifier = .ok (handle, cell) ∧
      cell.address = address := by
  obtain ⟨id, member, selected⟩ := List.exists_of_findSome?_eq_some selected
  cases authorized : Atomics64.authorize world resources.actor id with
  | error fault => simp [authorized] at selected
  | ok pair =>
    by_cases same : pair.2.address = address
    · simp [authorized, same] at selected
      rcases selected with ⟨rfl, rfl, rfl⟩
      exact ⟨member, authorized, same⟩
    · simp [authorized, same] at selected

inductive QueueEffect (state : State) (worker : Worker) (instruction : Sequential.Instruction) :
    List Pending → Prop where
  | unchanged (intent : storeIntent instruction (localCPU state worker) = none) :
      QueueEffect state worker instruction worker.pending
  | enqueued {store ticket} (intent : storeIntent instruction (localCPU state worker) = some store)
      (grant : grantFor state.world worker.resources store = some ticket) :
      QueueEffect state worker instruction (worker.pending ++ [⟨ticket, store⟩])

theorem prepareQueue_effect {state : State} {worker : Worker} {instruction : Sequential.Instruction}
    {pending : List Pending} (success : prepareQueue state worker instruction = .ok pending) :
    QueueEffect state worker instruction pending := by
  cases intent : storeIntent instruction (localCPU state worker) with
  | none =>
    simp [prepareQueue, intent] at success
    subst pending
    exact .unchanged intent
  | some store =>
    cases grant : grantFor state.world worker.resources store with
    | none => simp [prepareQueue, intent, grant] at success
    | some ticket =>
      simp [prepareQueue, intent, grant] at success
      subst pending
      exact .enqueued intent grant

inductive FinishEffect (state : State) (tid : Nat) (worker : Worker)
    (pending : List Pending) (observation : Sequential.Observation) : State × Observation → Prop where
  | next {output} (outcome : observation.result = .next output) :
      FinishEffect state tid worker pending observation
        (install state tid state.world { worker with context := .ofCPU output, pending := pending }, .ordinary tid)
  | returned {output} (outcome : observation.result = .returned output) :
      FinishEffect state tid worker pending observation
        (install state tid state.world
          { worker with context := .ofCPU output, phase := .returned, pending := pending }, .returned tid)

theorem finishOrdinary_effect {state : State} {tid : Nat} {worker : Worker} {pending : List Pending}
    {observation : Sequential.Observation} {result : State × Observation}
    (success : finishOrdinary state tid worker pending observation = .ok result) :
    FinishEffect state tid worker pending observation result := by
  cases outcome : observation.result <;> simp [finishOrdinary, outcome] at success
  all_goals subst result
  · exact .next outcome
  · exact .returned outcome

inductive OrdinaryEffect (state : State) (tid : Nat) (worker : Worker)
    (instruction : Sequential.Instruction) (af : Bool) (result : State × Observation) : Prop where
  | intro {pending observation}
      (supported : supported instruction = true)
      (bounds : codeFits worker instruction.length)
      (decoded : Sequential.decodeAt (localCPU state worker) = .ok instruction)
      (reads : ∃ units, (instruction.operandReads (localCPU state worker)).mapM (checkRead state worker) = .ok units)
      (queue : QueueEffect state worker instruction pending)
      (step : Sequential.step af (localCPU state worker) = .ok observation)
      (finish : FinishEffect state tid worker pending observation result) :
      OrdinaryEffect state tid worker instruction af result

theorem ordinary_effect {state : State} {tid : Nat} {worker : Worker}
    {instruction : Sequential.Instruction} {af : Bool} {result : State × Observation}
    (success : ordinary state tid worker instruction af = .ok result) :
    OrdinaryEffect state tid worker instruction af result := by
  by_cases admitted : supported instruction = true
  · by_cases bounds : codeFits worker instruction.length
    · cases decoded : Sequential.decodeAt (localCPU state worker) with
      | error fault => simp [ordinary, admitted, bounds, decoded, Except.mapError] at success
      | ok actual =>
        by_cases same : actual = instruction
        · subst actual
          cases reads : (instruction.operandReads (localCPU state worker)).mapM (checkRead state worker) with
          | error fault => simp [ordinary, admitted, bounds, decoded, reads, Except.mapError] at success
          | ok units =>
            cases pending : prepareQueue state worker instruction with
            | error fault => simp [ordinary, admitted, bounds, decoded, reads, pending, Except.mapError] at success
            | ok queue =>
              cases executed : Sequential.execute (localCPU state worker) instruction af with
              | error fault => simp [ordinary, admitted, bounds, decoded, reads, pending, executed, Except.mapError] at success
              | ok observation =>
                have finished : finishOrdinary state tid worker queue observation = .ok result := by
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

theorem issue_effect {state : State} {tid : Nat} {af : Bool} {result : State × Observation}
    (success : issue state tid af = .ok result) :
    ∃ worker, state.workers[tid]? = some worker ∧ worker.phase ≠ .returned ∧
      LeaseCurrent state.world worker.resources.actor worker.resources.code ∧
      LeaseCurrent state.world worker.resources.actor worker.resources.caller ∧
      ∃ instruction, decode (fetchCPU state worker) = .ok instruction ∧
        (match instruction with
        | .ordinary instruction => OrdinaryEffect state tid worker instruction af result
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

theorem drain_effect {state : State} {tid : Nat} {result : State × Observation}
    (success : drain state tid = .ok result) :
    ∃ worker head tail output,
      state.workers[tid]? = some worker ∧ worker.pending = head :: tail ∧
      PendingValid state.world worker.resources head ∧
      Atomics64.mutate state.world (operation worker.resources.actor head.ticket head.store) = .ok output ∧
      result = (install state tid output.1 { worker with pending := tail }, .drained tid head) := by
  cases live : state.workers[tid]? with
  | none => simp [drain, live] at success
  | some worker =>
    cases pending : worker.pending with
    | nil => simp [drain, live, pending] at success
    | cons head tail =>
      by_cases gate : PendingValid state.world worker.resources head
      · cases changed : Atomics64.mutate state.world (operation worker.resources.actor head.ticket head.store) with
        | error fault => simp [drain, live, pending, gate, changed, Except.mapError] at success
        | ok output =>
          simp [drain, live, pending, gate, changed, Except.mapError] at success
          exact ⟨worker, head, tail, output, rfl, pending, gate, changed, success.symm⟩
      · simp [drain, live, pending, gate] at success

end EDSL.OS.TSO64
