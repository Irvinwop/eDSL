/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.FetchAddBatch64
import EDSL.Grading.ConcurrentTask

set_option warningAsError true
set_option autoImplicit false

/-!
Whole-population safety, enabledness, finite completion and published-byte
frames for the admitted managed fetch-add family. The only executor is the
existing TSO64 scheduler. Admission remains the proof-facing `FetchAddBatch64.Pre`;
an independent admission adapter must derive it before using these lemmas.

The underlying profile has fixed manager metadata/permissions, scalar WB RAM,
the abstract TSO64 environment, and the existing long-mode/CET-off target
assumptions. These results do not assert physical or published x86-TSO refinement,
Linux or source-language semantics, scheduling fairness, or a global minimum.
-/

namespace EDSL.OS.FetchAddBatch64
open X86 Concurrency TSO64 X86.VCGen.AtomicMethods

namespace Frames

theorem stable_trans {before middle after : World}
    (first : Stable before middle) (second : Stable middle after) : Stable before after :=
  ⟨second.allocations.trans first.allocations, second.frontier.trans first.frontier,
    second.loans.trans first.loans, second.nextLoan.trans first.nextLoan,
    second.cells.trans first.cells, second.nextCell.trans first.nextCell,
    second.handles.trans first.handles, second.nextHandle.trans first.nextHandle,
    second.legacyHandles.trans first.legacyHandles,
    second.legacyNextHandle.trans first.legacyNextHandle,
    fun query => (second.permissions query).trans (first.permissions query)⟩

theorem step_length {before : TSO64.State} {action : Action}
    {result : TSO64.State × Observation} (success : TSO64.step before action = .ok result) :
    result.1.workers.length = before.workers.length := by
  cases TSO64.step_origin success with
  | ordinary live running code caller fetched effect =>
    cases effect with
    | intro supported bounds decoded reads queue executed finish =>
      cases finish <;> simp [TSO64.install]
  | blocked => rfl
  | rmw => simp [TSO64.install]
  | drained => simp [TSO64.install]

theorem schedule_length {before : TSO64.State} {actions : List Action}
    {result : TSO64.State × List Observation}
    (success : TSO64.schedule before actions = .ok result) :
    result.1.workers.length = before.workers.length := by
  induction actions generalizing before result with
  | nil =>
    have same := Except.ok.inj success
    cases same
    rfl
  | cons action rest ih =>
    obtain ⟨head, tail, first, following, same⟩ := TSO64.schedule_cons_ok success
    rw [same]
    exact (ih following).trans (step_length first)

theorem schedule_stable {before : TSO64.State} {actions : List Action}
    {result : TSO64.State × List Observation}
    (success : TSO64.schedule before actions = .ok result) :
    Stable before.world result.1.world := by
  induction actions generalizing before result with
  | nil =>
    have same := Except.ok.inj success
    cases same
    exact Stable.refl _
  | cons action rest ih =>
    obtain ⟨head, tail, first, following, same⟩ := TSO64.schedule_cons_ok success
    rw [same]
    exact stable_trans (TSO64.step_stable first) (ih (result := tail) following)

/-- Concatenate the actual scheduler runs and their observations. -/
theorem schedule_append {before : TSO64.State} {first second : List Action}
    {middle after : TSO64.State × List Observation}
    (head : TSO64.schedule before first = .ok middle)
    (tail : TSO64.schedule middle.1 second = .ok after) :
    TSO64.schedule before (first ++ second) = .ok (after.1, middle.2 ++ after.2) := by
  induction first generalizing before middle with
  | nil =>
    have same := Except.ok.inj head
    cases same
    exact tail
  | cons action rest ih =>
    obtain ⟨next, suffix, stepped, following, same⟩ := TSO64.schedule_cons_ok head
    subst middle
    have combined := ih following tail
    simp only [List.cons_append, TSO64.schedule, stepped, ok_bind, combined, pure_ok,
      List.cons_append]

/-- Any observed RMW names a real member of the original context population.
No value-based event filtering is used, including for zero updates. -/
theorem rmw_bound {before : TSO64.State} {actions : List Action}
    {result : TSO64.State × List Observation}
    (success : TSO64.schedule before actions = .ok result)
    {tid : Nat} {event : Atomics64.FetchAddEvent}
    (observed : Observation.rmw tid event ∈ result.2) : tid < before.workers.length := by
  induction actions generalizing before result with
  | nil =>
    have same := Except.ok.inj success
    cases same
    cases observed
  | cons action rest ih =>
    obtain ⟨head, tail, first, following, same⟩ := TSO64.schedule_cons_ok success
    rw [same] at observed
    rcases List.mem_cons.mp observed with atHead | later
    · obtain ⟨af, worker, instruction, identifier, machine, _, live, _⟩ :=
        TSO64History.step_event_origin (first.trans (congrArg Except.ok (by
          exact Prod.ext rfl atHead.symm)))
      exact (List.getElem_of_getElem? live).1
    · have bound := ih following later
      rwa [step_length first] at bound

end Frames

variable {image : FetchAddABI64.Image} {target : Atomics64.CellId64}
  {cell : Atomics64.Cell} {members : List (Member image target cell)}

/-- Current invariants for every actual context, also after some have returned.
There is no requirement that the contexts remain at their initial entry point. -/
structure Population (members : List (Member image target cell)) (state : TSO64.State) : Prop where
  valid : TSO64.WellFormed state
  length : state.workers.length = members.length
  current : ∀ i : Fin members.length, Current members[i].method state
  located : ∀ i : Fin members.length, ∃ point worker,
    state.workers[i.val]? = some worker ∧ At members[i].method point worker

theorem Pre.population {before : FetchAddCalls64.CheckedState target cell}
    (pre : Pre members before) : Population members before.state :=
  ⟨before.valid, pre.length, pre.current, fun i => by
    obtain ⟨worker, live, located⟩ := pre.entry i
    exact ⟨_, worker, live, located⟩⟩

/-- All successful prefixes retain every member's Current/At assertion by the
released per-method schedule theorem, including peers and returned contexts. -/
theorem Population.schedule {before : TSO64.State} (population : Population members before)
    {actions : List Action} {actual : TSO64.State × List Observation}
    (success : TSO64.schedule before actions = .ok actual) : Population members actual.1 := by
  refine ⟨TSO64.schedule_wellFormed population.valid success,
    (Frames.schedule_length success).trans population.length, ?_, ?_⟩
  · intro i
    obtain ⟨point, worker, live, located⟩ := population.located i
    exact (schedule_preserves (population.current i) live located success).1
  · intro i
    obtain ⟨point, worker, live, located⟩ := population.located i
    obtain ⟨_, next, final, finalLive, finalAt, _⟩ :=
      schedule_preserves (population.current i) live located success
    exact ⟨next, final, finalLive, finalAt⟩

theorem Population.step {before : TSO64.State} (population : Population members before)
    {action : Action} {actual : TSO64.State × Observation}
    (success : TSO64.step before action = .ok actual) : Population members actual.1 := by
  apply population.schedule (actions := [action]) (actual := (actual.1, [actual.2]))
  simp only [TSO64.schedule, success, ok_bind, pure_ok]

/-- Full coverage converts an actual worker lookup to its family cutpoint. -/
theorem Population.worker {state : TSO64.State} (population : Population members state)
    {tid : Nat} {worker : Worker} (live : state.workers[tid]? = some worker) :
    ∃ (i : Fin members.length) (point : Point), i.val = tid ∧ At members[i].method point worker := by
  have bound : tid < members.length := by
    rw [← population.length]
    exact (List.getElem_of_getElem? live).1
  let i : Fin members.length := ⟨tid, bound⟩
  obtain ⟨point, tracked, found, located⟩ := population.located i
  have same : tracked = worker := Option.some.inj (found.symm.trans live)
  subst tracked
  exact ⟨i, point, rfl, located⟩

theorem Population.quiescent {state : TSO64.State} (population : Population members state) :
    TSO64.Quiescent state := by
  intro worker member
  obtain ⟨tid, live⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨i, point, _, located⟩ := population.worker live
  exact located.2.1

/-- The independent fixed prefix contract, with original resource descriptors
and authority in the actual current world. -/
theorem Pre.safePrefix {before : FetchAddCalls64.CheckedState target cell}
    (pre : Pre members before) {actions : List Action}
    {actual : TSO64.State × List Observation}
    (success : TSO64.schedule before.state actions = .ok actual) :
    Grading.ConcurrentTask.FetchAdd64.SafePrefix before.state actual.1 := by
  have population := pre.population.schedule success
  refine ⟨population.valid, Frames.schedule_stable success, Frames.schedule_length success, ?_⟩
  intro tid initial initialLive
  have bound : tid < members.length := by
    rw [← pre.length]
    exact (List.getElem_of_getElem? initialLive).1
  let i : Fin members.length := ⟨tid, bound⟩
  obtain ⟨admitted, admittedLive, initialAt⟩ := pre.entry i
  have same : admitted = initial := Option.some.inj (admittedLive.symm.trans initialLive)
  subst admitted
  obtain ⟨point, final, finalLive, finalAt⟩ := population.located i
  exact ⟨final, finalLive, finalAt.1.trans initialAt.1.symm,
    (population.valid.2 final (List.mem_of_getElem? finalLive)).1⟩

/-- Present running contexts have a retiring own issue for every AF choice.
The unfinished cutpoint follows from actual phase, rather than a future step. -/
theorem Population.enabled {state : TSO64.State} (population : Population members state)
    {tid : Nat} {worker : Worker} (live : state.workers[tid]? = some worker)
    (running : worker.phase = .running) (af : Bool) :
    ∃ result, TSO64.step state (.issue tid af) = .ok result ∧ result.2.retired = 1 := by
  obtain ⟨i, point, tidEq, located⟩ := population.worker live
  have unfinished : point.remaining ≠ 0 := by
    intro zero
    have returned := located.zero_returned zero
    rw [running] at returned
    cases returned
  subst tid
  exact X86.VCGen.AtomicMethods.enabled (population.current i) live located unfinished af

theorem Pre.enabled {before : FetchAddCalls64.CheckedState target cell}
    (pre : Pre members before) {actions : List Action}
    {actual : TSO64.State × List Observation}
    (success : TSO64.schedule before.state actions = .ok actual)
    {tid : Nat} {worker : Worker} (live : actual.1.workers[tid]? = some worker)
    (running : worker.phase = .running) (af : Bool) :
    ∃ result, TSO64.step actual.1 (.issue tid af) = .ok result ∧ result.2.retired = 1 :=
  (pre.population.schedule success).enabled live running af

/-- Complete any finite selection, preserving prior completed members under
the remaining actual peer schedules. Choices supply arbitrary AF values. -/
theorem Population.complete_members (indices : List (Fin members.length))
    (choices : Nat → Nat → Bool) {state : TSO64.State}
    (population : Population members state) :
    ∃ actions actual, TSO64.schedule state actions = .ok actual ∧
      ∀ i ∈ indices, ∃ worker, actual.1.workers[i.val]? = some worker ∧
        worker.phase = .returned ∧ worker.pending = [] := by
  induction indices generalizing state with
  | nil => exact ⟨[], (state, []), rfl, by simp⟩
  | cons i indices ih =>
    obtain ⟨point, worker, live, located⟩ := population.located i
    obtain ⟨own, middle, returned, event, _, _, head, found, done⟩ :=
      X86.VCGen.AtomicMethods.complete (population.current i) live located (choices i.val)
    have middlePopulation := population.schedule head
    obtain ⟨rest, actual, following, finished⟩ := ih middlePopulation
    refine ⟨own ++ rest, (actual.1, middle.2 ++ actual.2),
      Frames.schedule_append head following, ?_⟩
    intro j member
    rcases List.mem_cons.mp member with same | later
    · subst j
      obtain ⟨_, next, final, finalLive, finalAt, remaining, _⟩ :=
        schedule_preserves (middlePopulation.current i) found done following
      have zero : next.remaining = 0 := (Nat.eq_zero_of_add_eq_zero remaining).1
      exact ⟨final, finalLive, finalAt.zero_returned zero, finalAt.2.1⟩
    · exact finished j later

/-- A real finite schedule completes every actual worker from any reachable
family cutpoints. Even an empty population is covered, with the empty schedule. -/
theorem Population.completion {state : TSO64.State} (population : Population members state)
    (choices : Nat → Nat → Bool) :
    ∃ actions actual, TSO64.schedule state actions = .ok actual ∧ TSO64.Finished actual.1 := by
  obtain ⟨actions, actual, success, finished⟩ :=
    population.complete_members (List.finRange members.length) choices
  have finalPopulation := population.schedule success
  refine ⟨actions, actual, success, ?_, finalPopulation.quiescent⟩
  intro worker member
  obtain ⟨tid, live⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨i, point, tidEq, located⟩ := finalPopulation.worker live
  obtain ⟨final, finalLive, returned, _⟩ := finished i (List.mem_finRange i)
  rw [tidEq, live] at finalLive
  have same : worker = final := Option.some.inj finalLive
  subst final
  exact returned

theorem Pre.completion {before : FetchAddCalls64.CheckedState target cell}
    (pre : Pre members before) (choices : Nat → Nat → Bool) :
    ∃ actions actual, TSO64.schedule before.state actions = .ok actual ∧
      TSO64.Finished actual.1 :=
  pre.population.completion choices

namespace Frames

/-- Every recorded method event satisfies the original typed event contract. -/
theorem event_correct {method : Method} {point : Point} {worker : Worker}
    (located : At method point worker) {event : Atomics64.FetchAddEvent}
    (member : event ∈ point.events) : EventCorrect method event := by
  cases point with
  | preamble _ _ | rmw _ => cases member
  | ret offset actual =>
    have same : event = actual := List.mem_singleton.mp member
    subst event
    exact located.2.2.2.2.2.2
  | done actual =>
    have same : event = actual := List.mem_singleton.mp member
    subst event
    exact located.2.2.2.2.2

end Frames

/-- Each actual RMW occurrence, without any nonzero-value condition, is at
this population's selected cell and its complete eight-byte address. -/
theorem Population.rmw {state after : TSO64.State} (population : Population members state)
    {action : Action} {tid : Nat} {event : Atomics64.FetchAddEvent}
    (success : TSO64.step state action = .ok (after, .rmw tid event)) :
    event.cell = target ∧ event.arithmetic.event.address = cell.address := by
  obtain ⟨af, worker, instruction, identifier, machine, actionEq, live, _⟩ :=
    TSO64History.step_event_origin success
  obtain ⟨i, point, tidEq, located⟩ := population.worker live
  subst tid
  obtain ⟨next, final, finalLive, finalAt, _, events, _⟩ :=
    step_preserves (population.current i) live located success
  have observed : event ∈ next.events := by
    rw [← events]
    simp [ownEvent]
  have correct := Frames.event_correct finalAt observed
  exact ⟨correct.cell.trans members[i].target,
    correct.address.trans (congrArg Atomics64.Cell.address members[i].object)⟩

/-- Empty FIFOs of all actual workers exclude successful publication steps. -/
theorem Population.no_drain {state : TSO64.State} (population : Population members state)
    (tid : Nat) (result : TSO64.State × Observation) :
    TSO64.step state (.drain tid) ≠ .ok result := by
  intro success
  obtain ⟨worker, head, tail, output, live, fifo, _⟩ := TSO64.drain_effect success
  have empty := population.quiescent worker (List.mem_of_getElem? live)
  rw [empty] at fifo
  cases fifo

/-- Every successful action of the closed family is an issue. Ordinary
publication cannot be hidden between its RMW occurrences. -/
theorem Population.issues_only {state : TSO64.State} (population : Population members state)
    {actions : List Action} {actual : TSO64.State × List Observation}
    (success : TSO64.schedule state actions = .ok actual) :
    ∀ action ∈ actions, ∃ tid af, action = .issue tid af := by
  induction actions generalizing state actual with
  | nil => simp
  | cons action rest ih =>
    obtain ⟨head, tail, first, following, _⟩ := TSO64.schedule_cons_ok success
    intro selected member
    rcases List.mem_cons.mp member with same | later
    · subst selected
      cases action with
      | issue tid af => exact ⟨tid, af, rfl⟩
      | drain tid => exact False.elim (population.no_drain tid head first)
    · exact ih (population.step first) following selected later

/-- A real published-byte frame. Ordinary issue retains the world, RMW uses
the existing checked atomic footprint, and draining contradicts actual empty
FIFOs. Metadata/permission stability alone is never used as byte equality. -/
theorem Population.step_memory {state : TSO64.State} (population : Population members state)
    {action : Action} {actual : TSO64.State × Observation}
    (success : TSO64.step state action = .ok actual)
    (address : Word) (outside : ¬ (AddressSpace.qwordRegion cell.address).Contains address) :
    (published actual.1.world).read address = (published state.world).read address := by
  cases TSO64.step_origin success with
  | ordinary live running code caller fetched effect =>
    cases effect with
    | intro supported bounds decoded reads queue executed finish =>
      cases finish <;> rfl
  | blocked => rfl
  | rmw live running code caller fetched bounds empty grant effect =>
    have selected := population.rmw success
    have frame := Atomics64.fetchAdd_frame _ _ _ _ _ effect.checked address
      (by simpa only [selected.2] using outside)
    change (AddressSpace.toMemory _).read address = (AddressSpace.toMemory _).read address
    simp only [TSO64.install, AddressSpace.toMemory, frame]
  | drained live fifo gate changed effect =>
    have empty := population.quiescent _ (List.mem_of_getElem? live)
    rw [empty] at fifo
    cases fifo

/-- The byte frame holds for every successful prefix, whether or not it has
returned yet. All members remain current and quiescent at every induction step. -/
theorem Population.memory {state : TSO64.State} (population : Population members state)
    {actions : List Action} {actual : TSO64.State × List Observation}
    (success : TSO64.schedule state actions = .ok actual)
    (address : Word) (outside : ¬ (AddressSpace.qwordRegion cell.address).Contains address) :
    (published actual.1.world).read address = (published state.world).read address := by
  induction actions generalizing state actual with
  | nil =>
    have same := Except.ok.inj success
    cases same
    rfl
  | cons action rest ih =>
    obtain ⟨head, tail, first, following, same⟩ := TSO64.schedule_cons_ok success
    rw [same]
    exact (ih (population.step first) following).trans (population.step_memory first address outside)

theorem Pre.memory {before : FetchAddCalls64.CheckedState target cell}
    (pre : Pre members before) {actions : List Action}
    {actual : TSO64.State × List Observation}
    (success : TSO64.schedule before.state actions = .ok actual)
    (address : Word) (outside : ¬ (AddressSpace.qwordRegion cell.address).Contains address) :
    (published actual.1.world).read address = (published before.state.world).read address :=
  pre.population.memory success address outside

/-- Completed batches have exactly one own event per actual member. Universal
member uniqueness and actual tid coverage exclude every foreign RMW, including
zero-delta events and events whose before/after words happen to be equal. -/
theorem Pre.rmw_completed {before : FetchAddCalls64.CheckedState target cell}
    (pre : Pre members before) {actions : List Action}
    {actual : TSO64.State × List Observation}
    (success : TSO64.schedule before.state actions = .ok actual)
    (done : TSO64.Returned actual.1) {tid : Nat} {event : Atomics64.FetchAddEvent}
    (observed : Observation.rmw tid event ∈ actual.2) :
    event.cell = target ∧ event.arithmetic.event.address = cell.address := by
  have bound : tid < members.length := by
    rw [← pre.length]
    exact Frames.rmw_bound success observed
  let i : Fin members.length := ⟨tid, bound⟩
  obtain ⟨point, worker, live, located⟩ := (pre.population.schedule success).located i
  obtain ⟨own, post, response, input, selected, unique, origin, count⟩ :=
    pre.member_completed i success live (done worker (List.mem_of_getElem? live))
  have member : event ∈ actual.2.filterMap (ownEvent i.val) :=
    List.mem_filterMap.mpr ⟨.rmw tid event, observed, by simp [ownEvent, i]⟩
  rw [unique] at member
  have same : event = own := List.mem_singleton.mp member
  subst event
  exact ⟨selected, post.correct.address.trans (congrArg Atomics64.Cell.address members[i].object)⟩

theorem Pre.noForeignRMW {before : FetchAddCalls64.CheckedState target cell}
    (pre : Pre members before) {actions : List Action}
    {actual : TSO64.State × List Observation}
    (success : TSO64.schedule before.state actions = .ok actual)
    (done : TSO64.Returned actual.1) (tid : Nat) (event : Atomics64.FetchAddEvent)
    (observed : Observation.rmw tid event ∈ actual.2) : event.cell = target :=
  (pre.rmw_completed success done observed).1

/-- The admitted initial RSI values in actual context order. -/
def inputs (members : List (Member image target cell)) : List Word :=
  members.map fun member => member.method.entry .rsi

theorem cohort_inputs (members : List (Member image target cell)) (state : TSO64.State) :
    cohort members state = Grading.ConcurrentTask.FetchAdd64.cohort (inputs members) state := by
  simp only [cohort, Grading.ConcurrentTask.FetchAdd64.cohort, inputs, List.length_map,
    List.getElem?_map]
  rfl

theorem selectedCall_task (target : Atomics64.CellId64) :
    selectedCall target = Grading.ConcurrentTask.FetchAdd64.selectedCall target := by
  funext observation
  cases observation with
  | rmw tid event =>
    by_cases selected : event.cell = target
    · simp only [selectedCall, FetchAddCalls64.targetEvent,
        Grading.ConcurrentTask.FetchAdd64.selectedCall, selected, ↓reduceIte,
        Option.map_some, FetchAddCalls64.call]
    · simp only [selectedCall, FetchAddCalls64.targetEvent,
        Grading.ConcurrentTask.FetchAdd64.selectedCall, selected, ↓reduceIte, Option.map_none]
  | _ => rfl

/-- A whole independent return frame, for each original actual context. -/
theorem Pre.returnFrame {before : FetchAddCalls64.CheckedState target cell}
    (pre : Pre members before) {actions : List Action}
    {actual : TSO64.State × List Observation}
    (success : TSO64.schedule before.state actions = .ok actual)
    (done : TSO64.Returned actual.1) {tid : Nat} {initial : Worker}
    (initialLive : before.state.workers[tid]? = some initial) :
    ∃ final, Grading.ConcurrentTask.FetchAdd64.ReturnFrame before.state actual.1 tid initial final := by
  have bound : tid < members.length := by
    rw [← pre.length]
    exact (List.getElem_of_getElem? initialLive).1
  let i : Fin members.length := ⟨tid, bound⟩
  obtain ⟨admitted, admittedLive, initialAt⟩ := pre.entry i
  have same : admitted = initial := Option.some.inj (admittedLive.symm.trans initialLive)
  subst admitted
  obtain ⟨point, final, finalLive, finalAt⟩ := (pre.population.schedule success).located i
  obtain ⟨event, post, current, direction, collected⟩ :=
    pre.member_returned i success finalLive (done final (List.mem_of_getElem? finalLive))
  obtain ⟨gated, gatedLive, facts⟩ := FetchAddABI64.gate_sound (pre.abi i)
  have gatedEq : gated = initial := Option.some.inj (gatedLive.symm.trans initialLive)
  subst gated
  obtain ⟨_, _, _, _, _, stack, _, _, _, _, stackCanonical⟩ := facts.present
  have registers : initial.context.registers = members[i].method.entry := initialAt.2.2.2.2.1
  have finalStack : final.context.registers .rsp = initial.resources.callerAddress + 8 := by
    rw [post.rsp, ← registers, stack]
  refine ⟨final, finalLive, post.phase, post.empty, post.resources.trans initialAt.1.symm,
    (current.valid.2 final (List.mem_of_getElem? finalLive)).1, ?_, ?_, ?_, direction, ?_, ?_⟩
  · intro register member
    have distinct : register ≠ .rax ∧ register ≠ .rsp := by
      cases register <;> simp_all [PureCall.calleeSaved]
    rw [registers]
    apply post.registers register
    · rw [members[i].source]
      exact distinct.1
    · exact distinct.2
  · simpa only [registers] using post.rsp
  · rw [finalStack]
    exact stackCanonical
  · refine ⟨members[i].method.returnAddress, ?_, post.rip⟩
    rw [initialAt.1]
    exact (pre.current i).caller
  · change TSO64.collect actual.1 i.val = .ok (final.context.registers .rax)
    simp [TSO64.collect, finalLive, post.phase, post.empty]

/-- Fixed independent completed-execution fields for the actual input list.
No registry Claim or independent-admission-to-family adapter is assumed or
created here; those remain separate candidate obligations. -/
theorem Pre.post {before : FetchAddCalls64.CheckedState target cell}
    (pre : Pre members before) {actions : List Action}
    {actual : TSO64.State × List Observation}
    (success : TSO64.schedule before.state actions = .ok actual)
    (done : TSO64.Returned actual.1) {prior : Word}
    (initial : FetchAddCalls64.read before.state cell = .ok prior) :
    Nonempty (Grading.ConcurrentTask.FetchAdd64.Post image before (inputs members) prior actions actual) := by
  obtain ⟨entries, result, final, actionsEq, stateEq, observationsEq, history, points, calls⟩ :=
    pre.complete success done initial
  refine ⟨{
    entries := entries
    result := result
    final := final
    actions_eq := actionsEq
    state_eq := stateEq
    observations_eq := observationsEq
    history := history
    points := ?_
    calls := ?_
    noForeignRMW := pre.noForeignRMW success done
    returns := fun _ _ live => pre.returnFrame success done live
    stable := Frames.schedule_stable success
    memory := pre.memory success
  }⟩
  · rw [← selectedCall_task]
    exact points
  · rw [← cohort_inputs]
    exact calls

namespace Frames

/-- A code-extent bound, distinct from any execution-time or hardware minimum. -/
theorem shape_bound {bytes : List Byte} {input : Register} {locked : LockedAdd64.Instruction}
    {offset : Nat} {padding : List Padding} (shape : Shape bytes input locked offset padding) :
    offset + padding.length + 9 ≤ bytes.length := by
  induction shape with
  | body copy rmw ret extent => simp only [List.length_nil, Nat.add_zero]; omega
  | @pad offset padding rest node tail ih =>
    have positive := Sequential.Instruction.length_pos padding.instruction
    simp only [List.length_cons]
    omega

/-- Identify the existing own-progress counter with the independent task's
filter-based count of attempted issues. -/
theorem ownIssues_eq (tid : Nat) (actions : List Action) :
    ownIssues tid actions = Grading.ConcurrentTask.FetchAdd64.issues tid actions := by
  unfold Grading.ConcurrentTask.FetchAdd64.issues
  induction actions with
  | nil => rfl
  | cons action rest ih =>
    cases action with
    | issue thread af =>
      by_cases same : thread = tid <;> simp [ownIssues, ownIssue, same, ih] <;> omega
    | drain thread => simp [ownIssues, ownIssue, ih]

end Frames

/-- One uniform proved output bound for this at-most-64-byte family. This
conservative own-issue bound implies no fairness or instruction-count minimum. -/
theorem Pre.bounded {before : FetchAddCalls64.CheckedState target cell}
    (pre : Pre members before) {actions : List Action}
    {actual : TSO64.State × List Observation}
    (success : TSO64.schedule before.state actions = .ok actual) {tid : Nat}
    (enough : 67 ≤ Grading.ConcurrentTask.FetchAdd64.issues tid actions)
    {worker : Worker} (live : actual.1.workers[tid]? = some worker) :
    worker.phase = .returned ∧ worker.pending = [] := by
  obtain ⟨i, point, tidEq, located⟩ := (pre.population.schedule success).worker live
  subst tid
  obtain ⟨initial, initialLive, initialAt⟩ := pre.entry i
  have extent := Frames.shape_bound initialAt.2.2.2.2.2
  have size := members[i].method.size
  have budget : members[i].padding.length + 3 ≤ ownIssues i.val actions := by
    rw [Frames.ownIssues_eq]
    omega
  obtain ⟨final, finalLive, returned, empty⟩ := pre.member_progress i success budget
  have same : final = worker := Option.some.inj (finalLive.symm.trans live)
  subst final
  exact ⟨returned, empty⟩

/-- Assemble the existing independent Claim once a candidate proves that its
present independent admission yields this checked family and its actual input
list. This premise concerns only the initial state; all schedule, history,
frame and progress obligations are conclusions of the reusable lemmas above.
No candidate admission adapter or registered Claim instance is supplied here. -/
theorem claim_of_admission (image : FetchAddABI64.Image)
    (admission : ∀ {target cell} (before : FetchAddCalls64.CheckedState target cell) deltas,
      Grading.ConcurrentTask.FetchAdd64.Pre image before deltas →
      ∃ members : List (Member image target cell), Pre members before ∧ inputs members = deltas) :
    Grading.ConcurrentTask.FetchAdd64.Claim image := by
  refine { completed := ?_, prefixes := ?_, enabled := ?_, completion := ?_, bounded := ?_ }
  · intro target cell before deltas admitted actions actual success done prior initial
    obtain ⟨members, pre, inputEq⟩ := admission before deltas admitted
    rw [← inputEq]
    exact pre.post success done initial
  · intro target cell before deltas admitted actions actual success
    obtain ⟨members, pre, _⟩ := admission before deltas admitted
    exact pre.safePrefix success
  · intro target cell before deltas admitted actions actual success tid worker live running af
    obtain ⟨members, pre, _⟩ := admission before deltas admitted
    exact pre.enabled success live running af
  · intro target cell before deltas admitted
    obtain ⟨members, pre, _⟩ := admission before deltas admitted
    obtain ⟨actions, actual, success, returned, _⟩ := pre.completion (fun _ _ => false)
    exact ⟨actions, actual, success, returned⟩
  · refine ⟨67, by decide, ?_⟩
    intro target cell before deltas admitted actions actual success tid enough worker live
    obtain ⟨members, pre, _⟩ := admission before deltas admitted
    exact pre.bounded success enough live

end EDSL.OS.FetchAddBatch64

#audit_edsl
