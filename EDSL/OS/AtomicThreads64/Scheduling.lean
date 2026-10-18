/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.AtomicThreads64.History

namespace EDSL.OS.AtomicThreads64
open X86 AddressSpace

/-- Every selection supplies its own undefined AF choice, including RET. -/
abbrev Selection := Nat × Bool
/-- All selected instructions are retained. `none` denotes the actual RET,
not an erased scheduling position or a manufactured RMW. -/
abbrev Observation := Selection × Option Atomics64.Event

def Phase.remaining : Phase → Nat
  | .applying _ => 2
  | .returning _ _ => 1
  | .completed _ _ => 0

/-- One actual instruction per supplied selection, including no-event RET.
Failures expose no partial schedule result. -/
def schedule (state : State) : List Selection → Except Fault (State × List Observation)
  | [] => .ok (state, [])
  | selection :: rest => do
    let first ← dispatch state selection.1 selection.2
    let tail ← schedule first.1 rest
    return (tail.1, (selection, first.2) :: tail.2)

def events (observations : List Observation) : List Atomics64.Event :=
  observations.filterMap Prod.snd

def selectedCount (selections : List Selection) (identifier : Nat) : Nat :=
  (selections.map Prod.fst).count identifier

theorem schedule_cons_ok (state : State) (selection : Selection) (rest : List Selection)
    (result : State × List Observation) (success : schedule state (selection :: rest) = .ok result) :
    ∃ first tail, dispatch state selection.1 selection.2 = .ok first ∧
      schedule first.1 rest = .ok tail ∧ result = (tail.1, (selection, first.2) :: tail.2) := by
  cases head : dispatch state selection.1 selection.2 with
  | error fault => simp [schedule, head] at success
  | ok first =>
    cases next : schedule first.1 rest with
    | error fault => simp [schedule, head, next] at success
    | ok tail =>
      simp [schedule, head, next] at success
      exact ⟨first, tail, rfl, next, success.symm⟩

theorem schedule_selections (state : State) (selections : List Selection) (result : State × List Observation)
    (success : schedule state selections = .ok result) : result.2.map Prod.fst = selections := by
  induction selections generalizing state result with
  | nil => simp [schedule] at success; cases success; rfl
  | cons selection rest induction =>
    obtain ⟨first, tail, _, scheduled, same⟩ := schedule_cons_ok _ _ _ _ success
    rw [same]
    simp only [List.map_cons, induction first.1 tail scheduled]

theorem schedule_history (state : State) (selections : List Selection) (result : State × List Observation)
    (success : schedule state selections = .ok result) : History state (result.2.map Prod.snd) result.1 := by
  induction selections generalizing state result with
  | nil => simp [schedule] at success; cases success; exact .refl
  | cons selection rest induction =>
    obtain ⟨first, tail, selected, scheduled, same⟩ := schedule_cons_ok _ _ _ _ success
    rw [same]
    exact .next (.dispatch selected) (induction first.1 tail scheduled)

theorem schedule_wellFormed (state : State) (selections : List Selection) (result : State × List Observation)
    (valid : WellFormed state) (success : schedule state selections = .ok result) : WellFormed result.1 :=
  (schedule_history _ _ _ success).wellFormed valid

theorem dispatch_remaining (state : State) (identifier query : Nat) (af : Bool) (worker : Worker)
    (result : State × Option Atomics64.Event) (valid : WellFormed state)
    (live : state.workers query = some worker) (success : dispatch state identifier af = .ok result) :
    ∃ current, result.1.workers query = some current ∧
      current.phase.remaining + (if identifier = query then 1 else 0) = worker.phase.remaining := by
  by_cases selected : identifier = query
  · subst identifier
    obtain ⟨actual, found, effect⟩ := dispatch_effect _ _ _ _ valid success
    have same := Option.some.inj (found.symm.trans live)
    subst actual
    cases effect with
    | @applying context shared phase _ =>
      exact ⟨{ worker with phase := .returning shared.2 (applied worker.entry shared.2.logical.event.after af) },
        by simp [replace], by simp [Phase.remaining, phase]⟩
    | @returning event context phase =>
      exact ⟨{ worker with phase := .completed event (returned context worker.returnAddress) },
        by simp [replace], by simp [Phase.remaining, phase]⟩
  · have kept := (dispatch_frame _ _ _ _ valid success).2 query (Ne.symm selected)
    exact ⟨worker, kept.trans live, by simp [selected]⟩

theorem schedule_remaining (state : State) (selections : List Selection) (query : Nat) (worker : Worker)
    (result : State × List Observation) (valid : WellFormed state)
    (live : state.workers query = some worker) (success : schedule state selections = .ok result) :
    ∃ current, result.1.workers query = some current ∧
      current.phase.remaining + selectedCount selections query = worker.phase.remaining := by
  induction selections generalizing state worker result with
  | nil =>
    simp [schedule] at success
    cases success
    exact ⟨worker, live, by simp [selectedCount]⟩
  | cons selection rest induction =>
    obtain ⟨first, tail, selected, scheduled, same⟩ := schedule_cons_ok _ _ _ _ success
    obtain ⟨middle, middleAt, progress⟩ := dispatch_remaining _ _ _ _ _ _ valid live selected
    obtain ⟨current, currentAt, remaining⟩ := induction first.1 middle tail
      (dispatch_wellFormed _ _ _ _ valid selected) middleAt scheduled
    rw [same]
    refine ⟨current, currentAt, ?_⟩
    by_cases own : selection.1 = query
    · simp [selectedCount, own] at progress ⊢
      unfold selectedCount at remaining
      omega
    · simp [selectedCount, own, eq_comm] at progress ⊢
      unfold selectedCount at remaining
      omega

/-- Two successful selections complete an initially applying worker, while
its handle, cell and both loans remain live until a separate join. -/
theorem schedule_two_completes (state : State) (selections : List Selection) (query : Nat) (worker : Worker)
    (result : State × List Observation) (valid : WellFormed state)
    (live : state.workers query = some worker) (applying : ∃ context, worker.phase = .applying context)
    (success : schedule state selections = .ok result) (selected : selectedCount selections query = 2) :
    ∃ current event context, result.1.workers query = some current ∧
      current.phase = .completed event context ∧ WorkerValid result.1.shared query current := by
  obtain ⟨current, atCurrent, remaining⟩ := schedule_remaining _ _ _ _ _ valid live success
  obtain ⟨initialContext, initialPhase⟩ := applying
  simp only [initialPhase, Phase.remaining, selected] at remaining
  cases phase : current.phase with
  | applying context | returning event context => simp [phase] at remaining
  | completed event context =>
    exact ⟨current, event, context, atCurrent, phase,
      ((schedule_wellFormed _ _ _ valid success).2 _ _ atCurrent).2⟩

/-- A third successful selection is impossible. This is a count of actual
instructions, independent of elapsed time or fairness. -/
theorem schedule_selection_bound (state : State) (selections : List Selection) (query : Nat) (worker : Worker)
    (result : State × List Observation) (valid : WellFormed state)
    (live : state.workers query = some worker) (success : schedule state selections = .ok result) :
    selectedCount selections query ≤ worker.phase.remaining := by
  obtain ⟨_, _, remaining⟩ := schedule_remaining _ _ _ _ _ valid live success
  omega

/-- A finite interleaving is legal when its initial live workers have enough
remaining instructions for their selected counts. No predicted future success
or execution-admission oracle occurs in this current-state condition. -/
def Admissible (state : State) (selections : List Selection) : Prop :=
  ∀ identifier, 0 < selectedCount selections identifier → ∃ worker,
    state.workers identifier = some worker ∧ selectedCount selections identifier ≤ worker.phase.remaining

/-- Any finite legal interleaving executes, for every supplied AF sequence. -/
theorem schedule_enabled (state : State) (selections : List Selection)
    (valid : WellFormed state) (legal : Admissible state selections) :
    ∃ result, schedule state selections = .ok result := by
  induction selections generalizing state with
  | nil => exact ⟨(state, []), rfl⟩
  | cons selection rest induction =>
    have positive : 0 < selectedCount (selection :: rest) selection.1 := by simp [selectedCount]
    obtain ⟨worker, live, bound⟩ := legal selection.1 positive
    have unfinished : ∀ event context, worker.phase ≠ .completed event context := by
      intro event context phase
      simp [phase, Phase.remaining] at bound
      omega
    obtain ⟨first, selected⟩ := dispatch_enabled state selection.1 worker selection.2 valid live unfinished
    have restLegal : Admissible first.1 rest := by
      intro query nonzero
      have initialPositive : 0 < selectedCount (selection :: rest) query := by
        simp only [selectedCount, List.map_cons, List.count_cons]
        unfold selectedCount at nonzero
        omega
      obtain ⟨previous, previousAt, initialBound⟩ := legal query initialPositive
      obtain ⟨current, currentAt, remaining⟩ := dispatch_remaining _ _ _ _ _ _ valid previousAt selected
      refine ⟨current, currentAt, ?_⟩
      by_cases same : selection.1 = query
      · simp [selectedCount, same] at initialBound
        simp [same] at remaining
        unfold selectedCount
        omega
      · simp [selectedCount, same] at initialBound
        simp [same] at remaining
        unfold selectedCount
        omega
    obtain ⟨tail, scheduled⟩ := induction first.1 (dispatch_wellFormed _ _ _ _ valid selected) restLegal
    exact ⟨(tail.1, (selection, first.2) :: tail.2), by simp [schedule, selected, scheduled]⟩

/-- Two own selections and a checked join exist from present authority, with
no assumption of future collection success. AF is arbitrary on each step. -/
theorem two_dispatches_join (state : State) (identifier : Nat) (worker : Worker) (af retAF : Bool)
    (valid : WellFormed state) (live : state.workers identifier = some worker)
    (applying : ∃ context, worker.phase = .applying context) :
    ∃ final observations joined,
      schedule state [(identifier, af), (identifier, retAF)] = .ok (final, observations) ∧
      join final 0 identifier = .ok joined ∧ WellFormed joined.1 := by
  have rank : worker.phase.remaining = 2 := by
    obtain ⟨context, phase⟩ := applying
    simp [phase, Phase.remaining]
  have legal : Admissible state [(identifier, af), (identifier, retAF)] := by
    intro query nonzero
    by_cases same : identifier = query
    · subst query
      exact ⟨worker, live, by simp [selectedCount, rank]⟩
    · simp [selectedCount, same] at nonzero
  obtain ⟨result, scheduled⟩ := schedule_enabled _ _ valid legal
  obtain ⟨current, event, context, currentAt, completed, _⟩ := schedule_two_completes _ _ _ _ _
    valid live applying scheduled (by simp [selectedCount])
  have afterValid := schedule_wellFormed _ _ _ valid scheduled
  obtain ⟨joined, collected⟩ := join_enabled result.1 identifier current event context afterValid currentAt completed
  exact ⟨result.1, result.2, joined, scheduled, collected, join_wellFormed _ _ _ _ afterValid collected⟩

/-- A worker has exactly one pending RMW before its first selection. -/
def Phase.pendingRmw : Phase → Nat
  | .applying _ => 1
  | .returning _ _ | .completed _ _ => 0

def rmwCount (identifier : Nat) : List Observation → Nat
  | [] => 0
  | (selection, event) :: rest =>
      (if selection.1 = identifier ∧ event.isSome then 1 else 0) + rmwCount identifier rest

theorem dispatch_pendingRmw (state : State) (identifier query : Nat) (af : Bool) (worker : Worker)
    (result : State × Option Atomics64.Event) (valid : WellFormed state)
    (live : state.workers query = some worker) (success : dispatch state identifier af = .ok result) :
    ∃ current, result.1.workers query = some current ∧
      current.phase.pendingRmw + (if identifier = query ∧ result.2.isSome then 1 else 0) =
        worker.phase.pendingRmw := by
  by_cases selected : identifier = query
  · subst identifier
    obtain ⟨actual, found, effect⟩ := dispatch_effect _ _ _ _ valid success
    have same := Option.some.inj (found.symm.trans live)
    subst actual
    cases effect with
    | @applying context shared phase _ =>
      exact ⟨{ worker with phase := .returning shared.2 (applied worker.entry shared.2.logical.event.after af) },
        by simp [replace], by simp [Phase.pendingRmw, phase]⟩
    | @returning event context phase =>
      exact ⟨{ worker with phase := .completed event (returned context worker.returnAddress) },
        by simp [replace], by simp [Phase.pendingRmw, phase]⟩
  · exact ⟨worker, (dispatch_frame _ _ _ _ valid success).2 query (Ne.symm selected) |>.trans live,
      by simp [selected]⟩

/-- Each actual emitted event consumes the selected worker's sole RMW. -/
theorem schedule_rmw_count (state : State) (selections : List Selection) (query : Nat) (worker : Worker)
    (result : State × List Observation) (valid : WellFormed state)
    (live : state.workers query = some worker) (success : schedule state selections = .ok result) :
    ∃ current, result.1.workers query = some current ∧
      current.phase.pendingRmw + rmwCount query result.2 = worker.phase.pendingRmw := by
  induction selections generalizing state worker result with
  | nil =>
    simp [schedule] at success
    cases success
    exact ⟨worker, live, by simp [rmwCount]⟩
  | cons selection rest induction =>
    obtain ⟨first, tail, selected, scheduled, same⟩ := schedule_cons_ok _ _ _ _ success
    obtain ⟨middle, middleAt, progress⟩ := dispatch_pendingRmw _ _ _ _ _ _ valid live selected
    obtain ⟨current, currentAt, remaining⟩ := induction first.1 middle tail
      (dispatch_wellFormed _ _ _ _ valid selected) middleAt scheduled
    rw [same]
    refine ⟨current, currentAt, ?_⟩
    simp only [rmwCount]
    omega

/-- A completed initially applying worker has emitted exactly one actual RMW,
including when its mask is zero or already present. -/
theorem schedule_completed_one_rmw (state : State) (selections : List Selection)
    (query : Nat) (worker current : Worker) (event : Atomics64.Event) (context : Context)
    (result : State × List Observation) (valid : WellFormed state)
    (live : state.workers query = some worker) (applying : ∃ entry, worker.phase = .applying entry)
    (success : schedule state selections = .ok result) (currentAt : result.1.workers query = some current)
    (completed : current.phase = .completed event context) : rmwCount query result.2 = 1 := by
  obtain ⟨actual, found, count⟩ := schedule_rmw_count _ _ _ _ _ valid live success
  have same := Option.some.inj (found.symm.trans currentAt)
  subst actual
  obtain ⟨entry, phase⟩ := applying
  simpa only [completed, phase, Phase.pendingRmw, Nat.zero_add] using count

end EDSL.OS.AtomicThreads64
