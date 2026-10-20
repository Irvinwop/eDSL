/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.AtomicSetThreads64.Lifecycle
import EDSL.OS.AtomicSetThreads64.Dispatch

namespace EDSL.OS.AtomicSetThreads64

/-- Every instruction selection carries its own undefined-AF choice. -/
abbrev Selection := Nat × Bool

/-- Every selected position is retained. The actual RET emits `none`. -/
abbrev Observation := Selection × Option Atomics64.Event

/-- Execute exactly one checked instruction at each supplied position. A failed
instruction or suffix exposes no partial schedule result. -/
def schedule (state : State) : List Selection → Except Fault (State × List Observation)
  | [] => .ok (state, [])
  | selection :: rest => do
    let first ← dispatch state selection.1 selection.2
    let tail ← schedule first.1 rest
    return (tail.1, (selection, first.2) :: tail.2)

/-- Ordered actual RMWs; only the no-event instruction positions are removed. -/
def events (observations : List Observation) : List Atomics64.Event :=
  observations.filterMap Prod.snd

def selectedCount (selections : List Selection) (identifier : Nat) : Nat :=
  (selections.map Prod.fst).count identifier

@[simp] theorem selectedCount_nil (identifier : Nat) : selectedCount [] identifier = 0 := rfl

@[simp] theorem selectedCount_cons (selection : Selection) (rest : List Selection) (identifier : Nat) :
    selectedCount (selection :: rest) identifier =
      (if selection.1 = identifier then 1 else 0) + selectedCount rest identifier := by
  by_cases same : selection.1 = identifier
  · simp [selectedCount, same, Nat.add_comm]
  · simp [selectedCount, same]

@[simp] theorem selectedCount_append (first rest : List Selection) (identifier : Nat) :
    selectedCount (first ++ rest) identifier =
      selectedCount first identifier + selectedCount rest identifier := by
  simp only [selectedCount, List.map_append, List.count_append]

@[simp] theorem events_nil : events [] = [] := rfl

@[simp] theorem events_none (selection : Selection) (rest : List Observation) :
    events ((selection, none) :: rest) = events rest := rfl

@[simp] theorem events_some (selection : Selection) (event : Atomics64.Event) (rest : List Observation) :
    events ((selection, some event) :: rest) = event :: events rest := rfl

@[simp] theorem events_append (first rest : List Observation) :
    events (first ++ rest) = events first ++ events rest := by
  exact List.filterMap_append

/-- A dispatch-only history retains both the selected identity/AF and the
actual optional label, including the administrative RET position. -/
inductive DispatchHistory : State → List Observation → State → Prop where
  | refl {state} : DispatchHistory state [] state
  | next {state middle final selection label rest}
      (step : dispatch state selection.1 selection.2 = .ok (middle, label))
      (tail : DispatchHistory middle rest final) :
      DispatchHistory state ((selection, label) :: rest) final

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

theorem schedule_length (state : State) (selections : List Selection) (result : State × List Observation)
    (success : schedule state selections = .ok result) : result.2.length = selections.length := by
  simpa using congrArg List.length (schedule_selections _ _ _ success)

theorem schedule_selectedCount (state : State) (selections : List Selection)
    (result : State × List Observation) (identifier : Nat)
    (success : schedule state selections = .ok result) :
    selectedCount (result.2.map Prod.fst) identifier = selectedCount selections identifier := by
  rw [schedule_selections _ _ _ success]

theorem schedule_history (state : State) (selections : List Selection) (result : State × List Observation)
    (success : schedule state selections = .ok result) : DispatchHistory state result.2 result.1 := by
  induction selections generalizing state result with
  | nil => simp [schedule] at success; cases success; exact .refl
  | cons selection rest induction =>
    obtain ⟨first, tail, selected, scheduled, same⟩ := schedule_cons_ok _ _ _ _ success
    rw [same]
    exact .next selected (induction first.1 tail scheduled)

theorem DispatchHistory.schedule {state final : State} {observations : List Observation}
    (history : DispatchHistory state observations final) :
    schedule state (observations.map Prod.fst) = .ok (final, observations) := by
  induction history with
  | refl => rfl
  | next step tail induction => simp [AtomicSetThreads64.schedule, step, induction]

theorem DispatchHistory.append {state middle final : State} {first rest : List Observation}
    (prior : DispatchHistory state first middle) (suffix : DispatchHistory middle rest final) :
    DispatchHistory state (first ++ rest) final := by
  induction prior with
  | refl => exact suffix
  | next step tail induction => exact .next step (induction suffix)

theorem schedule_append_ok (state : State) (first rest : List Selection) (result : State × List Observation)
    (success : schedule state (first ++ rest) = .ok result) :
    ∃ middle tail, schedule state first = .ok middle ∧ schedule middle.1 rest = .ok tail ∧
      result = (tail.1, middle.2 ++ tail.2) := by
  induction first generalizing state result with
  | nil => exact ⟨(state, []), result, rfl, success, rfl⟩
  | cons selection first induction =>
    obtain ⟨head, remaining, selected, scheduled, same⟩ := schedule_cons_ok _ _ _ _ success
    obtain ⟨middle, tail, prior, suffix, restSame⟩ := induction head.1 remaining scheduled
    refine ⟨(middle.1, (selection, head.2) :: middle.2), tail, ?_, suffix, ?_⟩
    · simp [schedule, selected, prior]
    · simp only [same, restSame, List.cons_append]

theorem schedule_append (state middle final : State) (first rest : List Selection)
    (prior suffix : List Observation)
    (initial : schedule state first = .ok (middle, prior))
    (remaining : schedule middle rest = .ok (final, suffix)) :
    schedule state (first ++ rest) = .ok (final, prior ++ suffix) := by
  have selections := schedule_selections _ _ _ initial
  have restSelections := schedule_selections _ _ _ remaining
  have history := (schedule_history _ _ _ initial).append (schedule_history _ _ _ remaining)
  simpa only [List.map_append, selections, restSelections] using history.schedule

/-- Each observation is bound to the supplied selection at that same position,
and to an actual checked dispatch between the successful prior and suffix. -/
theorem schedule_observation_at (state : State) (selections : List Selection)
    (result : State × List Observation) (index : Nat) (selection : Selection)
    (label : Option Atomics64.Event) (success : schedule state selections = .ok result)
    (observed : result.2[index]? = some (selection, label)) :
    selections[index]? = some selection ∧ ∃ before after,
      schedule state (selections.take index) = .ok (before, result.2.take index) ∧
      dispatch before selection.1 selection.2 = .ok (after, label) ∧
      schedule after (selections.drop (index + 1)) = .ok (result.1, result.2.drop (index + 1)) := by
  induction selections generalizing state result index with
  | nil =>
    simp [schedule] at success
    cases success
    simp at observed
  | cons head rest induction =>
    obtain ⟨first, tail, selected, scheduled, same⟩ := schedule_cons_ok _ _ _ _ success
    cases index with
    | zero =>
      simp only [same, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at observed
      obtain ⟨rfl, rfl⟩ := observed
      exact ⟨rfl, state, first.1, rfl, selected, by simpa [same] using scheduled⟩
    | succ index =>
      have tailObserved : tail.2[index]? = some (selection, label) := by
        simpa only [same, List.getElem?_cons_succ] using observed
      obtain ⟨binding, before, after, prior, step, suffix⟩ :=
        induction first.1 tail index scheduled tailObserved
      refine ⟨binding, before, after, ?_, step, ?_⟩
      · simp [same, schedule, selected, prior]
      · simpa only [same, Nat.succ_add, List.drop_succ_cons] using suffix

/-- A finite dispatch list is legal using only present worker membership and
remaining instruction counts. No future transition or result is a premise. -/
def Legal (state : State) (selections : List Selection) : Prop :=
  ∀ identifier, 0 < selectedCount selections identifier → ∃ worker,
    state.workers identifier = some worker ∧ selectedCount selections identifier ≤ worker.rank

abbrev Admissible := Legal

theorem legal_nil (state : State) : Legal state [] := by
  intro identifier positive
  simp at positive

/-- Select one worker with exactly the supplied AF list, in its original order. -/
def ownSelections (identifier : Nat) (afs : List Bool) : List Selection :=
  afs.map (fun af => (identifier, af))

@[simp] theorem ownSelections_nil (identifier : Nat) : ownSelections identifier [] = [] := rfl

@[simp] theorem ownSelections_cons (identifier : Nat) (af : Bool) (afs : List Bool) :
    ownSelections identifier (af :: afs) = (identifier, af) :: ownSelections identifier afs := rfl

@[simp] theorem ownSelections_length (identifier : Nat) (afs : List Bool) :
    (ownSelections identifier afs).length = afs.length := by
  simp [ownSelections]

theorem ownSelections_afs (identifier : Nat) (afs : List Bool) :
    (ownSelections identifier afs).map Prod.snd = afs := by
  simp only [ownSelections, List.map_map, Function.comp_def]
  exact List.map_id' afs

theorem selectedCount_ownSelections (identifier query : Nat) (afs : List Bool) :
    selectedCount (ownSelections identifier afs) query =
      if identifier = query then afs.length else 0 := by
  induction afs with
  | nil => simp
  | cons af afs induction =>
    simp only [ownSelections_cons, selectedCount_cons, induction, List.length_cons]
    split <;> omega

theorem legal_ownSelections (state : State) (identifier : Nat) (worker : Worker) (afs : List Bool)
    (live : state.workers identifier = some worker) (bound : afs.length ≤ worker.rank) :
    Legal state (ownSelections identifier afs) := by
  intro query positive
  by_cases same : identifier = query
  · subst query
    exact ⟨worker, live, by simpa only [selectedCount_ownSelections, ↓reduceIte] using bound⟩
  · simp only [selectedCount_ownSelections, same, ↓reduceIte, Nat.lt_irrefl] at positive

theorem Worker.rank_zero_iff_completed (worker : Worker) :
    worker.rank = 0 ↔ worker.phase = .completed := by
  cases phase : worker.phase <;> simp [Worker.rank, phase]

theorem DispatchHistory.wellFormed {state final : State} {observations : List Observation}
    (history : DispatchHistory state observations final) (valid : WellFormed state) :
    WellFormed final := by
  induction history with
  | refl => exact valid
  | next step tail induction => exact induction (dispatch_wellFormed _ _ _ _ valid step)

theorem schedule_wellFormed (state : State) (selections : List Selection) (result : State × List Observation)
    (valid : WellFormed state) (success : schedule state selections = .ok result) : WellFormed result.1 :=
  (schedule_history _ _ _ success).wellFormed valid

theorem dispatch_remaining (state : State) (identifier query : Nat) (af : Bool) (worker : Worker)
    (result : State × Option Atomics64.Event) (valid : WellFormed state)
    (live : state.workers query = some worker) (success : dispatch state identifier af = .ok result) :
    ∃ current, result.1.workers query = some current ∧
      current.rank + (if identifier = query then 1 else 0) = worker.rank :=
  dispatch_rank _ _ _ _ _ _ valid live success

/-- Successful selections consume exactly the initial remaining instruction
rank. Interleaved peers preserve the worker's private state. -/
theorem schedule_remaining (state : State) (selections : List Selection) (query : Nat) (worker : Worker)
    (result : State × List Observation) (valid : WellFormed state)
    (live : state.workers query = some worker) (success : schedule state selections = .ok result) :
    ∃ current, result.1.workers query = some current ∧
      current.rank + selectedCount selections query = worker.rank := by
  induction selections generalizing state worker result with
  | nil =>
    simp [schedule] at success
    cases success
    exact ⟨worker, live, by simp⟩
  | cons selection rest induction =>
    obtain ⟨first, tail, selected, scheduled, same⟩ := schedule_cons_ok _ _ _ _ success
    obtain ⟨middle, middleAt, progress⟩ := dispatch_remaining _ _ _ _ _ _ valid live selected
    obtain ⟨current, currentAt, remaining⟩ := induction first.1 middle tail
      (dispatch_wellFormed _ _ _ _ valid selected) middleAt scheduled
    rw [same]
    refine ⟨current, currentAt, ?_⟩
    rw [selectedCount_cons]
    omega

theorem schedule_selection_bound (state : State) (selections : List Selection) (query : Nat) (worker : Worker)
    (result : State × List Observation) (valid : WellFormed state)
    (live : state.workers query = some worker) (success : schedule state selections = .ok result) :
    selectedCount selections query ≤ worker.rank := by
  obtain ⟨_, _, remaining⟩ := schedule_remaining _ _ _ _ _ valid live success
  omega

/-- Every finite resource-legal list runs with its supplied AF choices. -/
theorem schedule_enabled (state : State) (selections : List Selection)
    (valid : WellFormed state) (legal : Admissible state selections) :
    ∃ result, schedule state selections = .ok result := by
  induction selections generalizing state with
  | nil => exact ⟨(state, []), rfl⟩
  | cons selection rest induction =>
    have positive : 0 < selectedCount (selection :: rest) selection.1 := by
      simp only [selectedCount_cons, ↓reduceIte]
      omega
    obtain ⟨worker, live, bound⟩ := legal selection.1 positive
    have running : worker.phase = .running := by
      cases phase : worker.phase with
      | running => rfl
      | completed => simp [Worker.rank, phase] at bound
    obtain ⟨first, selected⟩ := dispatch_enabled state selection.1 worker selection.2 valid live running
    have restLegal : Admissible first.1 rest := by
      intro query nonzero
      have initialPositive : 0 < selectedCount (selection :: rest) query := by
        rw [selectedCount_cons]
        omega
      obtain ⟨previous, previousAt, initialBound⟩ := legal query initialPositive
      obtain ⟨current, currentAt, remaining⟩ := dispatch_remaining _ _ _ _ _ _ valid previousAt selected
      refine ⟨current, currentAt, ?_⟩
      rw [selectedCount_cons] at initialBound
      omega
    obtain ⟨tail, scheduled⟩ := induction first.1 (dispatch_wellFormed _ _ _ _ valid selected) restLegal
    exact ⟨(tail.1, (selection, first.2) :: tail.2), by simp [schedule, selected, scheduled]⟩

/-- Exhausting one initial rank completes that worker while its resources
remain pinned; a legal shorter prefix need not complete it. -/
theorem schedule_completes (state : State) (selections : List Selection) (query : Nat) (worker : Worker)
    (result : State × List Observation) (valid : WellFormed state)
    (live : state.workers query = some worker) (success : schedule state selections = .ok result)
    (selected : selectedCount selections query = worker.rank) :
    ∃ current, result.1.workers query = some current ∧ current.phase = .completed ∧
      WorkerValid result.1.shared query current := by
  obtain ⟨current, currentAt, remaining⟩ := schedule_remaining _ _ _ _ _ valid live success
  have zero : current.rank = 0 := by omega
  exact ⟨current, currentAt, (current.rank_zero_iff_completed).mp zero,
    ((schedule_wellFormed _ _ _ valid success).2 _ _ currentAt).2⟩

/-- Exactly the remaining own selections finish a worker, for every list of
AF choices of that length, including a RET-only worker or a completed worker. -/
theorem ownSelections_completes (state : State) (identifier : Nat) (worker : Worker) (afs : List Bool)
    (valid : WellFormed state) (live : state.workers identifier = some worker)
    (length : afs.length = worker.rank) :
    ∃ result current, schedule state (ownSelections identifier afs) = .ok result ∧
      result.1.workers identifier = some current ∧ current.phase = .completed ∧
      WorkerValid result.1.shared identifier current := by
  obtain ⟨result, success⟩ := schedule_enabled _ _ valid
    (legal_ownSelections _ _ _ _ live (Nat.le_of_eq length))
  obtain ⟨current, currentAt, completed, workerValid⟩ := schedule_completes _ _ _ _ _ valid live success
    (by simpa only [selectedCount_ownSelections, ↓reduceIte] using length)
  exact ⟨result, current, success, currentAt, completed, workerValid⟩

/-- Completion is followed by the actual checked close and two loan finishes.
Collection preserves the entire current resource world and cell registry. -/
theorem ownSelections_join (state : State) (identifier : Nat) (worker : Worker) (afs : List Bool)
    (valid : WellFormed state) (live : state.workers identifier = some worker)
    (length : afs.length = worker.rank) :
    ∃ result current joined,
      schedule state (ownSelections identifier afs) = .ok result ∧
      result.1.workers identifier = some current ∧ current.phase = .completed ∧
      join result.1 0 identifier = .ok joined ∧ WellFormed joined.1 ∧
      joined.2 = current.context ∧ joined.1.workers identifier = none ∧
      joined.1.shared.legacy.shared.resources = result.1.shared.legacy.shared.resources ∧
      joined.1.shared.cells = result.1.shared.cells := by
  obtain ⟨result, current, success, currentAt, completed, _⟩ :=
    ownSelections_completes _ _ _ _ valid live length
  have finalValid := schedule_wellFormed _ _ _ valid success
  obtain ⟨joined, collected, joinedValid⟩ := join_enabled _ _ _ finalValid currentAt completed
  obtain ⟨actual, _, _, _, found, _, _, _, _, _, same⟩ := join_ok _ _ _ _ collected
  have equal := Option.some.inj (found.symm.trans currentAt)
  subst actual
  exact ⟨result, current, joined, success, currentAt, completed, collected, joinedValid,
    by rw [same], (join_workers _ _ _ _ collected).1, join_resources _ _ _ _ collected⟩

/-- Explicit construction with arbitrary AF at every remaining offset. -/
theorem remaining_dispatches_join (state : State) (identifier : Nat) (worker : Worker)
    (af : Nat → Bool) (valid : WellFormed state) (live : state.workers identifier = some worker) :
    ∃ result joined,
      schedule state (ownSelections identifier (List.ofFn (fun offset : Fin worker.rank => af offset))) =
        .ok result ∧ join result.1 0 identifier = .ok joined ∧ WellFormed joined.1 := by
  obtain ⟨result, _, joined, scheduled, _, _, collected, joinedValid, _⟩ :=
    ownSelections_join state identifier worker (List.ofFn (fun offset : Fin worker.rank => af offset))
      valid live (by simp)
  exact ⟨result, joined, scheduled, collected, joinedValid⟩

/-- Successful completion has exactly the initial remaining selection count;
this also excludes premature RET and repeated dispatch after completion. -/
theorem schedule_completed_iff (state : State) (selections : List Selection) (query : Nat)
    (worker current : Worker) (result : State × List Observation) (valid : WellFormed state)
    (live : state.workers query = some worker) (success : schedule state selections = .ok result)
    (currentAt : result.1.workers query = some current) :
    current.phase = .completed ↔ selectedCount selections query = worker.rank := by
  obtain ⟨actual, actualAt, conservation⟩ := schedule_remaining _ _ _ _ _ valid live success
  have equal := Option.some.inj (actualAt.symm.trans currentAt)
  subst actual
  rw [← current.rank_zero_iff_completed]
  omega

/-- A successfully selected identity was already present initially; dispatch
cannot create a worker in the middle of a schedule. -/
theorem schedule_initial_worker (state : State) (selections : List Selection) (query : Nat)
    (result : State × List Observation) (valid : WellFormed state)
    (success : schedule state selections = .ok result) (positive : 0 < selectedCount selections query) :
    ∃ worker, state.workers query = some worker := by
  induction selections generalizing state result with
  | nil => simp at positive
  | cons selection rest induction =>
    obtain ⟨first, tail, selected, scheduled, _⟩ := schedule_cons_ok _ _ _ _ success
    by_cases own : selection.1 = query
    · subst query
      obtain ⟨worker, live, _⟩ := dispatch_effect _ _ _ _ valid selected
      exact ⟨worker, live⟩
    · have restPositive : 0 < selectedCount rest query := by
        simpa only [selectedCount_cons, own, ↓reduceIte, Nat.zero_add] using positive
      obtain ⟨worker, live⟩ := induction first.1 tail (dispatch_wellFormed _ _ _ _ valid selected)
        scheduled restPositive
      exact ⟨worker, ((dispatch_frame _ _ _ _ valid selected).2 query (Ne.symm own)).symm.trans live⟩

/-- The finite resource-only admission condition is also necessary for a
successful dispatch-only schedule from a well-formed initial state. -/
theorem schedule_legal (state : State) (selections : List Selection) (result : State × List Observation)
    (valid : WellFormed state) (success : schedule state selections = .ok result) : Legal state selections := by
  intro query positive
  obtain ⟨worker, live⟩ := schedule_initial_worker _ _ _ _ valid success positive
  exact ⟨worker, live, schedule_selection_bound _ _ _ _ _ valid live success⟩

theorem schedule_enabled_iff (state : State) (selections : List Selection) (valid : WellFormed state) :
    (∃ result, schedule state selections = .ok result) ↔ Legal state selections := by
  exact ⟨fun ⟨result, success⟩ => schedule_legal _ _ result valid success, schedule_enabled _ _ valid⟩

end EDSL.OS.AtomicSetThreads64
