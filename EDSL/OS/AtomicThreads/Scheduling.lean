/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.AtomicThreads.History

namespace EDSL.OS.AtomicThreads
open X86 AddressSpace

def Phase.remaining : Phase → Nat
  | .preparing _ => 3
  | .exchanging _ => 2
  | .returning _ _ => 1
  | .completed _ _ => 0

theorem dispatch_remaining (state : State) (identifier query : Nat) (worker : Worker)
    (result : State × Option AtomicEvent) (valid : WellFormed state)
    (live : state.workers query = some worker) (success : dispatch state identifier = .ok result) :
    ∃ current, result.1.workers query = some current ∧
      current.phase.remaining + (if identifier = query then 1 else 0) = worker.phase.remaining := by
  by_cases selected : identifier = query
  · subst identifier
    obtain ⟨actual, found, effect⟩ := dispatch_effect _ _ _ valid success
    have same := Option.some.inj (found.symm.trans live)
    subst actual
    cases effect with
    | preparing phase => exact ⟨{ worker with phase := .exchanging (prepared worker.entry) },
        by simp [replace], by simp [Phase.remaining, phase]⟩
    | @exchanging context shared phase _ =>
      exact ⟨{ worker with phase := .returning shared.2 (exchanged worker.entry shared.2) },
        by simp [replace], by simp [Phase.remaining, phase]⟩
    | @returning old context phase =>
      exact ⟨{ worker with phase := .completed old (worker.entry.returned old worker.returnAddress) },
        by simp [replace], by simp [Phase.remaining, phase]⟩
  · have kept := (dispatch_frame _ _ _ valid success).2 query (Ne.symm selected)
    exact ⟨worker, kept.trans live, by simp [selected]⟩

def recordEvent (identifier : Nat) (event : Option AtomicEvent) (tail : List (Nat × AtomicEvent)) :
    List (Nat × AtomicEvent) := match event with
  | none => tail
  | some event => (identifier, event) :: tail

/-- A successful supplied schedule counts actual selected user instructions
and retains emitted RMW events with the selected thread IDs. -/
def schedule (state : State) : List Nat → Except Fault (State × List (Nat × AtomicEvent))
  | [] => .ok (state, [])
  | identifier :: rest => do
    let first ← dispatch state identifier
    let tail ← schedule first.1 rest
    return (tail.1, recordEvent identifier first.2 tail.2)

theorem schedule_cons_ok (state : State) (identifier : Nat) (rest : List Nat)
    (result : State × List (Nat × AtomicEvent)) (success : schedule state (identifier :: rest) = .ok result) :
    ∃ first tail, dispatch state identifier = .ok first ∧ schedule first.1 rest = .ok tail ∧
      result = (tail.1, recordEvent identifier first.2 tail.2) := by
  cases head : dispatch state identifier with
  | error fault => simp [schedule, head] at success
  | ok first =>
    cases next : schedule first.1 rest with
    | error fault => simp [schedule, head, next] at success
    | ok tail =>
      simp [schedule, head, next] at success
      exact ⟨first, tail, rfl, next, success.symm⟩

theorem schedule_history (state : State) (selections : List Nat) (result : State × List (Nat × AtomicEvent))
    (success : schedule state selections = .ok result) : History state result.1 := by
  induction selections generalizing state result with
  | nil => simp [schedule] at success; cases success; exact .refl
  | cons identifier rest induction =>
    obtain ⟨first, tail, selected, scheduled, same⟩ := schedule_cons_ok _ _ _ _ success
    rw [same]
    exact .next (.dispatch selected) (induction first.1 tail scheduled)

theorem schedule_wellFormed (state : State) (selections : List Nat) (result : State × List (Nat × AtomicEvent))
    (valid : WellFormed state) (success : schedule state selections = .ok result) : WellFormed result.1 :=
  (schedule_history _ _ _ success).wellFormed valid

theorem schedule_remaining (state : State) (selections : List Nat) (query : Nat) (worker : Worker)
    (result : State × List (Nat × AtomicEvent)) (valid : WellFormed state)
    (live : state.workers query = some worker) (success : schedule state selections = .ok result) :
    ∃ current, result.1.workers query = some current ∧
      current.phase.remaining + selections.count query = worker.phase.remaining := by
  induction selections generalizing state worker result with
  | nil =>
    simp [schedule] at success
    cases success
    exact ⟨worker, live, by simp⟩
  | cons identifier rest induction =>
    obtain ⟨first, tail, selected, scheduled, same⟩ := schedule_cons_ok _ _ _ _ success
    obtain ⟨middle, middleAt, progress⟩ := dispatch_remaining _ _ _ _ _ valid live selected
    obtain ⟨current, currentAt, remaining⟩ := induction first.1 middle tail
      (dispatch_wellFormed _ _ _ valid selected) middleAt scheduled
    rw [same]
    refine ⟨current, currentAt, ?_⟩
    by_cases own : identifier = query
    · simp [own] at progress ⊢
      omega
    · simp [own, eq_comm] at progress ⊢
      omega

theorem schedule_three_completes (state : State) (selections : List Nat) (query : Nat) (worker : Worker)
    (result : State × List (Nat × AtomicEvent)) (valid : WellFormed state)
    (live : state.workers query = some worker) (preparing : ∃ context, worker.phase = .preparing context)
    (success : schedule state selections = .ok result) (selected : selections.count query = 3) :
    ∃ current old context, result.1.workers query = some current ∧ current.phase = .completed old context := by
  obtain ⟨current, atCurrent, remaining⟩ := schedule_remaining _ _ _ _ _ valid live success
  obtain ⟨initialContext, initialPhase⟩ := preparing
  simp only [initialPhase, Phase.remaining, selected] at remaining
  cases phase : current.phase with
  | preparing context | exchanging context | returning old context => simp [phase] at remaining
  | completed old context => exact ⟨current, old, context, atCurrent, phase⟩

theorem finishLoan_enabled (state : Atomics.State) (borrower identifier : Nat) (loan : Borrowing.Loan)
    (live : state.shared.loans identifier = some loan) (actor : loan.borrower = borrower) :
    ∃ after, Atomics.finishLoan state borrower identifier = .ok after := by
  refine ⟨{ state with shared := { state.shared with loans := fun query =>
    if query = identifier then none else state.shared.loans query } }, ?_⟩
  simp [Atomics.finishLoan, Borrowing.finishLoan, Borrowing.authorize, live, actor, Except.mapError]

theorem join_enabled (state : State) (identifier : Nat) (worker : Worker)
    (valid : WellFormed state) (live : state.workers identifier = some worker)
    (completed : ∃ old context, worker.phase = .completed old context) :
    ∃ result, join state 0 identifier = .ok result := by
  have workerValid := (valid.2 _ _ live).2
  obtain ⟨old, context, phase⟩ := completed
  obtain ⟨handle, authorized, _⟩ := workerValid.authorized
  let data : Atomics.State := { state.shared with handles := fun query => if query = worker.handle then none else state.shared.handles query }
  have d : Atomics.close state.shared (principal identifier) worker.handle = .ok data := by
    simp [Atomics.close, authorized, data]
  obtain ⟨codeLoan, codeAt, codeActor, _⟩ := workerValid.code
  have codeAfter : data.shared.loans worker.codeLoan = some codeLoan := by rw [close_shared d]; exact codeAt
  obtain ⟨code, c⟩ := finishLoan_enabled data _ _ codeLoan codeAfter codeActor
  obtain ⟨stackLoan, stackAt, stackActor, _⟩ := workerValid.stack
  have stackAfter : code.shared.loans worker.stackLoan = some stackLoan :=
    (finishLoan_other c (Ne.symm workerValid.distinct)).trans
      ((congrArg (fun shared => shared.loans worker.stackLoan) (close_shared d)).trans stackAt)
  obtain ⟨stack, s⟩ := finishLoan_enabled code _ _ stackLoan stackAfter stackActor
  exact ⟨({ replace state identifier none with shared := stack }, context.registers .rax), by
    simp [join, live, workerValid.parent, phase, d, c, s, Except.mapError]⟩

/-- Selecting a live worker for exactly its remaining user instructions
always succeeds. This supplies a finite schedule, without imposing fairness
on arbitrary environment choices. -/
theorem schedule_own_enabled (steps : Nat) (state : State) (identifier : Nat) (worker : Worker)
    (valid : WellFormed state) (live : state.workers identifier = some worker)
    (remaining : worker.phase.remaining = steps) :
    ∃ result, schedule state (List.replicate steps identifier) = .ok result := by
  induction steps generalizing state worker with
  | zero => exact ⟨(state, []), rfl⟩
  | succ steps induction =>
    have unfinished : ∀ old context, worker.phase ≠ .completed old context := by
      intro old context phase
      simp [phase, Phase.remaining] at remaining
    obtain ⟨first, selected⟩ := dispatch_enabled state identifier worker valid live unfinished
    obtain ⟨middle, middleAt, progress⟩ := dispatch_remaining state identifier identifier worker first valid live selected
    have nextRank : middle.phase.remaining = steps := by simp at progress; omega
    obtain ⟨tail, scheduled⟩ := induction first.1 middle
      (dispatch_wellFormed _ _ _ valid selected) middleAt nextRank
    exact ⟨(tail.1, recordEvent identifier first.2 tail.2), by
      simp [List.replicate_succ, schedule, selected, scheduled]⟩

/-- Every well-formed preparing worker has a successful three-instruction
schedule followed by a checked join. Resource preservation applies to the
resulting collected state. -/
theorem three_dispatches_join (state : State) (identifier : Nat) (worker : Worker)
    (valid : WellFormed state) (live : state.workers identifier = some worker)
    (preparing : ∃ context, worker.phase = .preparing context) :
    ∃ final events joined, schedule state [identifier, identifier, identifier] = .ok (final, events) ∧
      join final 0 identifier = .ok joined ∧ WellFormed joined.1 := by
  have rank : worker.phase.remaining = 3 := by
    obtain ⟨context, phase⟩ := preparing
    simp [phase, Phase.remaining]
  obtain ⟨result, scheduled⟩ := schedule_own_enabled 3 state identifier worker valid live rank
  have scheduledThree : schedule state [identifier, identifier, identifier] = .ok result := by
    simpa using scheduled
  obtain ⟨current, old, context, currentAt, completed⟩ := schedule_three_completes state
    [identifier, identifier, identifier] identifier worker result valid live preparing scheduledThree (by simp)
  have afterValid := schedule_wellFormed _ _ _ valid scheduledThree
  obtain ⟨joined, collected⟩ := join_enabled result.1 identifier current afterValid currentAt ⟨old, context, completed⟩
  exact ⟨result.1, result.2, joined, scheduledThree, collected,
    join_wellFormed _ _ _ _ afterValid collected⟩

/-- An independently observed initial word determines the actual singleton
exchange event, joined return value and final shared word when this preparing
worker executes its three instructions without peer selections. -/
theorem three_dispatches_spec (state : State) (identifier : Nat) (worker : Worker) (old : BitVec 32)
    (valid : WellFormed state) (live : state.workers identifier = some worker)
    (preparing : ∃ context, worker.phase = .preparing context)
    (observed : loadDWord (toMemory state.shared.shared.resources.space) (worker.entry.registers .rdi) = .ok old) :
    ∃ final joined,
      schedule state [identifier, identifier, identifier] = .ok (final,
        [(identifier, ⟨worker.entry.registers .rdi, old, (worker.entry.registers .rsi).setWidth 32⟩)]) ∧
      join final 0 identifier = .ok joined ∧ joined.2 = old.setWidth 64 ∧
      loadDWord (toMemory joined.1.shared.shared.resources.space) (worker.entry.registers .rdi) =
        .ok ((worker.entry.registers .rsi).setWidth 32) ∧ WellFormed joined.1 := by
  obtain ⟨context, phase⟩ := preparing
  let movedWorker := { worker with phase := .exchanging (prepared worker.entry) }
  let moved := replace state identifier (some movedWorker)
  have first : dispatch state identifier = .ok (moved, none) :=
    dispatch_preparing state identifier worker context live (valid.2 _ _ live).2 phase
  have movedAt : moved.workers identifier = some movedWorker := by simp [moved, replace]
  have movedValid := dispatch_wellFormed _ _ _ valid first
  have movedWorkerValid := (movedValid.2 _ _ movedAt).2
  obtain ⟨handle, authorized, _⟩ := movedWorkerValid.authorized
  obtain ⟨swapped, exchangedOk⟩ := Atomics.exchange_enabled moved.shared (principal identifier)
    movedWorker.handle handle ((worker.entry.registers .rsi).setWidth 32) movedValid.1 authorized
  let returningWorker := { movedWorker with phase := .returning swapped.2 (exchanged worker.entry swapped.2) }
  let returningState := { replace moved identifier (some returningWorker) with shared := swapped.1 }
  let event : AtomicEvent := ⟨worker.entry.registers .rdi, swapped.2, (worker.entry.registers .rsi).setWidth 32⟩
  have second : dispatch moved identifier = .ok (returningState, some event) :=
    dispatch_exchanging moved identifier movedWorker (prepared worker.entry) swapped movedAt movedWorkerValid rfl exchangedOk
  obtain ⟨_, _, _, _, _, _, beforeRead, afterRead, _⟩ := dispatch_atomic_spec _ _ _ _ movedValid second
  have oldEq : swapped.2 = old := Except.ok.inj (beforeRead.symm.trans observed)
  have returningAt : returningState.workers identifier = some returningWorker := by simp [returningState, replace]
  have returningValid := dispatch_wellFormed _ _ _ movedValid second
  let completedWorker := { returningWorker with phase := .completed swapped.2 (worker.entry.returned swapped.2 worker.returnAddress) }
  let final := replace returningState identifier (some completedWorker)
  have third : dispatch returningState identifier = .ok (final, none) :=
    dispatch_returning returningState identifier returningWorker swapped.2 (exchanged worker.entry swapped.2)
      returningAt (returningValid.2 _ _ returningAt).2 rfl
  have finalAt : final.workers identifier = some completedWorker := by simp [final, replace]
  have finalValid := dispatch_wellFormed _ _ _ returningValid third
  obtain ⟨joined, collected⟩ := join_enabled final identifier completedWorker finalValid finalAt ⟨_, _, rfl⟩
  have value := dispatched_join_value identifier event movedValid second (.next (.dispatch third) .refl) 0 joined collected
  refine ⟨final, joined, ?_, collected, ?_, ?_, join_wellFormed _ _ _ _ finalValid collected⟩
  · simp [schedule, first, second, third, recordEvent, event, oldEq]
  · simpa only [event, oldEq] using value
  · rw [join_resources _ _ _ _ collected]
    exact afterRead

/-- Unrestricted scheduler choice admits infinite idling. Selection-count
termination does not supply fairness or a bound on elapsed time. -/
theorem idle_trace (state : State) :
    ∃ trace : Nat → State, trace 0 = state ∧ ∀ index, Step (trace index) (trace (index + 1)) :=
  ⟨fun _ => state, rfl, fun _ => .idle⟩

end EDSL.OS.AtomicThreads
