/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.CounterLoadedInputs
import EDSL.OS.TSO64.EffectSimulation.Mixed.RankedPrefix

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Construct overlapping finite executions of the actual loaded counter workers.
The stopping condition reads actual RMW observations, with all intervening
positions and exact collective ghosts retained. The checked ranked engine
supplies every issue and its strict finite potential decrease. Current Post
transport excludes a premature done response while the own count is short.

The target, logical authority, protected loans, stable translation/no-alias,
long-mode/CET-off and coherent scalar WB RAM assumptions of the imported model
remain. This module makes no fairness, all-schedule, minimum-cost, native,
hardware, source/compiler refinement or corpus admission claim.
-/

namespace EDSL.Corpus.V1.CounterOverlap
open X86 OS OS.TSO64 OS.TSO64.EffectSimulation CounterCommon

/-- Extract issuers from actual RMW labels, retaining their original order. -/
def issuers : List O → List Nat
  | [] => []
  | .rmw tid _ :: rest => tid :: issuers rest
  | _ :: rest => issuers rest

theorem issuers_append (left right : List O) :
    issuers (left ++ right) = issuers left ++ issuers right := by
  induction left with
  | nil => rfl
  | cons head tail ih => cases head <;> simp_all [issuers]

/-- Connect the independent full-history count API to the issuer projection. -/
theorem count_issuers (tid : Nat) (observations : List O) :
    Mixed.Counts.countRMW tid observations =
      ((issuers observations).filter fun thread => decide (thread = tid)).length := by
  induction observations with
  | nil => rfl
  | cons head tail ih =>
    cases head with
    | rmw thread event =>
      by_cases same : thread = tid <;>
        simp [issuers, Mixed.Counts.countRMW, Mixed.Counts.ownRMW, same, ih, Nat.add_comm]
    | ordinary => simpa only [issuers, Mixed.Counts.countRMW, Mixed.Counts.ownRMW, Nat.zero_add] using ih
    | returned => simpa only [issuers, Mixed.Counts.countRMW, Mixed.Counts.ownRMW, Nat.zero_add] using ih
    | blocked => simpa only [issuers, Mixed.Counts.countRMW, Mixed.Counts.ownRMW, Nat.zero_add] using ih
    | drained => simpa only [issuers, Mixed.Counts.countRMW, Mixed.Counts.ownRMW, Nat.zero_add] using ih

/-- The exact ghosts' current completion invariant; stablePost transports a
historical response along its real idle extension, without equating histories. -/
def Completed {n : Nat} {initial : S} (subjects : Fin n → CohortSubject initial)
    (slots : ∀ i, (subjects i).site.tid = i.val)
    (ghosts : (counterRankedCohort subjects slots).Ghosts initial) : Prop :=
  ∀ i, Mixed.CompletionInvariant (ghosts i)

theorem completed_step {n : Nat} {initial : S} {subjects : Fin n → CohortSubject initial}
    {slots : ∀ i, (subjects i).site.tid = i.val}
    {before after : (counterRankedCohort subjects slots).Ghosts initial}
    {action : Action} {seen : O}
    (advanced : (counterRankedCohort subjects slots).Step before action seen after)
    (completed : Completed subjects slots before) : Completed subjects slots after := by
  intro i
  exact (advanced i).2.1.completionInvariant
    (stablePost (subjects i).site (subjects i).call) (completed i)

theorem running_of_short_count {n : Nat} {initial : S}
    {subjects : Fin n → CohortSubject initial} {slots : ∀ i, (subjects i).site.tid = i.val}
    {ghosts : (counterRankedCohort subjects slots).Ghosts initial}
    (completed : Completed subjects slots ghosts) (i : Fin n)
    (short : Mixed.Counts.logRMW i.val (ghosts i).history < (subjects i).call.iterations.toNat) :
    ∃ node fuel, (ghosts i).control = .running node fuel := by
  cases control : (ghosts i).control with
  | running node fuel => exact ⟨node, fuel, rfl⟩
  | done response =>
    have post := completed i
    simp only [Mixed.CompletionInvariant, control] at post
    change Post (subjects i).site (subjects i).call (ghosts i).current (ghosts i).history at post
    have exactCount := post.count
    rw [slots i] at exactCount
    omega

/-- Full observations extend each particular subject's own count; this never
identifies different subjects' histories or separately chosen ghosts. -/
theorem trace_counts {n : Nat} {profile : Profile} {family : RMWFamily}
    (cohort : Mixed.RankedCohort n profile family) {initial : S}
    {before after : cohort.Ghosts initial} {actions : List Action} {observations : List O}
    (trace : LiftTrace cohort.Step before actions observations after) (i : Fin n) (tid : Nat) :
    Mixed.Counts.logRMW tid (after i).history = Mixed.Counts.logRMW tid (before i).history +
      Mixed.Counts.countRMW tid observations := by
  have logs := Mixed.liftTrace_logs ((cohort.rules i).localTrace_forget (cohort.localTrace trace i))
  simp only [Mixed.Counts.logRMW, logs.2, Mixed.Counts.countRMW_append]

theorem own_labels {n : Nat} {profile : Profile} {family : RMWFamily}
    (cohort : Mixed.RankedCohort n profile family) (i : Fin n) {af : Bool} {seen : O}
    (retiring : cohort.toCohort.Retires (.issue i.val af) seen) :
    seen = .ordinary i.val ∨ seen = .returned i.val ∨
      ∃ event, seen = .rmw i.val event := by
  obtain ⟨j, choice, action, labels⟩ := retiring
  have same : i.val = (cohort.descriptor j).tid := (Action.issue.inj action).1
  change seen = .ordinary (cohort.descriptor j).tid ∨
    seen = .returned (cohort.descriptor j).tid ∨
    (∃ event, seen = .rmw (cohort.descriptor j).tid event) at labels
  simpa only [← same] using labels

/-- A selected thread's finite segment ends at its first actual RMW. Other
threads advance through those same positions. All exact ghosts, logs, choices
and present-state gates are available for another segment or completion. -/
structure Segment {n : Nat} {initial before : S}
    (subjects : Fin n → CohortSubject initial) (slots : ∀ i, (subjects i).site.tid = i.val)
    (ghosts : (counterRankedCohort subjects slots).Ghosts initial)
    (choices : Nat → Nat → Bool) (offset : Nat → Nat) (selected : Fin n) where
  actions : List Action
  observations : List O
  final : S
  finalGhosts : (counterRankedCohort subjects slots).Ghosts initial
  actual : TSO64.schedule before actions .ownedOnly .arithmetic = .ok (final, observations)
  valid : WellFormed final .ownedOnly
  workers : final.workers.length = n
  empty : Quiescent final
  current : (counterRankedCohort subjects slots).Current final finalGhosts
  completed : Completed subjects slots finalGhosts
  lifted : LiftTrace (counterRankedCohort subjects slots).Step ghosts actions observations finalGhosts
  retiring : (counterRankedCohort subjects slots).toCohort.RetirementTrace actions observations
  chosen : Mixed.ChoiceTrace.ChosenFrom choices offset actions
  onlySelected : ∀ action ∈ actions, ∃ af, action = .issue selected.val af
  lastRMW : ∃ quiet event, observations = quiet ++ [.rmw selected.val event] ∧ issuers quiet = []
  bound : actions.length ≤ (counterRankedCohort subjects slots).potential ghosts

theorem Segment.issuers {n : Nat} {initial before : S}
    {subjects : Fin n → CohortSubject initial} {slots : ∀ i, (subjects i).site.tid = i.val}
    {ghosts : (counterRankedCohort subjects slots).Ghosts initial}
    {choices : Nat → Nat → Bool} {offset : Nat → Nat} {selected : Fin n}
    (segment : Segment (before := before) subjects slots ghosts choices offset selected) :
    issuers segment.observations = [selected.val] := by
  obtain ⟨quiet, event, same, noEarlier⟩ := segment.lastRMW
  rw [same, issuers_append, noEarlier]
  rfl

private theorem run_at_potential {n : Nat} {initial : S}
    (subjects : Fin n → CohortSubject initial) (slots : ∀ i, (subjects i).site.tid = i.val)
    (choices : Nat → Nat → Bool) (i : Fin n) :
    ∀ amount : Nat, ∀ {before : S}
      (ghosts : (counterRankedCohort subjects slots).Ghosts initial) (offset : Nat → Nat),
      (counterRankedCohort subjects slots).potential ghosts = amount →
      WellFormed before .ownedOnly → before.workers.length = n →
      (counterRankedCohort subjects slots).Current before ghosts → Quiescent before →
      Completed subjects slots ghosts →
      Mixed.Counts.logRMW i.val (ghosts i).history < (subjects i).call.iterations.toNat →
      Nonempty (Segment (before := before) subjects slots ghosts choices offset i) := by
  classical
  intro amount
  induction amount using Nat.strongRecOn with
  | ind amount ih =>
    intro before ghosts offset potential valid count current empty completed short
    let cohort := counterRankedCohort subjects slots
    obtain ⟨node, fuel, running⟩ := running_of_short_count completed i short
    obtain ⟨after, seen, next, actual, afterValid, afterCount, afterEmpty,
        _afterCovered, nextCurrent, advanced, retiring, smaller⟩ :=
      cohort.enabled_step valid count current empty i running (choices i.val (offset i.val))
    have nextCompleted := completed_step advanced completed
    have single : TSO64.schedule before [.issue i.val (choices i.val (offset i.val))]
        .ownedOnly .arithmetic = .ok (after, [seen]) := by
      simp only [TSO64.schedule, actual, ok_bind, pure_ok]
    by_cases hit : ∃ event, seen = .rmw i.val event
    · obtain ⟨event, rfl⟩ := hit
      exact ⟨{
        actions := [.issue i.val (choices i.val (offset i.val))]
        observations := [.rmw i.val event]
        final := after
        finalGhosts := next
        actual := single
        valid := afterValid
        workers := afterCount
        empty := afterEmpty
        current := nextCurrent
        completed := nextCompleted
        lifted := .cons advanced .nil
        retiring := .cons retiring .nil
        chosen := Mixed.ChoiceTrace.chosen_cons (Mixed.ChoiceTrace.chosen_nil choices _)
        onlySelected := by intro action member; exact ⟨_, (List.mem_singleton.mp member)⟩
        lastRMW := ⟨[], event, rfl, rfl⟩
        bound := by change 1 ≤ cohort.potential ghosts; omega }⟩
    · have quiet : seen = .ordinary i.val ∨ seen = .returned i.val := by
        rcases own_labels cohort i retiring with ordinary | returned | atomic
        · exact Or.inl ordinary
        · exact Or.inr returned
        · exact False.elim (hit atomic)
      have zero : Mixed.Counts.ownRMW i.val seen = 0 := by
        rcases quiet with rfl | rfl <;> rfl
      have noIssuer : issuers [seen] = [] := by
        rcases quiet with rfl | rfl <;> rfl
      have unchanged : Mixed.Counts.logRMW i.val (next i).history =
          Mixed.Counts.logRMW i.val (ghosts i).history := by
        rw [(advanced i).2.1.tick, Mixed.Counts.logRMW_snoc, zero, Nat.add_zero]
      have below : cohort.potential next < amount :=
        Nat.lt_of_lt_of_le smaller (Nat.le_of_eq potential)
      obtain ⟨rest⟩ := ih (cohort.potential next) below next
        (Mixed.ChoiceTrace.bump offset i.val) rfl afterValid afterCount nextCurrent afterEmpty
        nextCompleted (by rw [unchanged]; exact short)
      refine ⟨{
        actions := .issue i.val (choices i.val (offset i.val)) :: rest.actions
        observations := seen :: rest.observations
        final := rest.final
        finalGhosts := rest.finalGhosts
        actual := ?_
        valid := rest.valid
        workers := rest.workers
        empty := rest.empty
        current := rest.current
        completed := rest.completed
        lifted := .cons advanced rest.lifted
        retiring := .cons retiring rest.retiring
        chosen := Mixed.ChoiceTrace.chosen_cons rest.chosen
        onlySelected := ?_
        lastRMW := ?_
        bound := Nat.le_trans (Nat.succ_le_succ rest.bound) smaller }⟩
      · simp only [TSO64.schedule, actual, ok_bind, rest.actual, pure_ok]
      · intro action member
        rcases List.mem_cons.mp member with rfl | later
        · exact ⟨_, rfl⟩
        · exact rest.onlySelected action later
      · obtain ⟨quietPrefix, event, same, noEarlier⟩ := rest.lastRMW
        refine ⟨seen :: quietPrefix, event, ?_, ?_⟩
        · simp only [same, List.cons_append]
        · change issuers ([seen] ++ quietPrefix) = []
          rw [issuers_append, noIssuer, noEarlier]
          rfl

/-- Present checked invariants and a short own history construct the segment;
no future success, intermediate value, PC oracle or desired label is assumed. -/
theorem run_to_own_RMW {n : Nat} {initial before : S}
    (subjects : Fin n → CohortSubject initial) (slots : ∀ i, (subjects i).site.tid = i.val)
    (ghosts : (counterRankedCohort subjects slots).Ghosts initial)
    (valid : WellFormed before .ownedOnly) (count : before.workers.length = n)
    (current : (counterRankedCohort subjects slots).Current before ghosts) (empty : Quiescent before)
    (completed : Completed subjects slots ghosts) (choices : Nat → Nat → Bool)
    (offset : Nat → Nat) (i : Fin n)
    (short : Mixed.Counts.logRMW i.val (ghosts i).history < (subjects i).call.iterations.toNat) :
    Nonempty (Segment (before := before) subjects slots ghosts choices offset i) :=
  run_at_potential subjects slots choices i _ ghosts offset rfl valid count current empty completed short

theorem Segment.counts {n : Nat} {initial before : S}
    {subjects : Fin n → CohortSubject initial} {slots : ∀ i, (subjects i).site.tid = i.val}
    {ghosts : (counterRankedCohort subjects slots).Ghosts initial}
    {choices : Nat → Nat → Bool} {offset : Nat → Nat} {selected : Fin n}
    (segment : Segment (before := before) subjects slots ghosts choices offset selected) (i : Fin n) :
    Mixed.Counts.logRMW i.val (segment.finalGhosts i).history =
      Mixed.Counts.logRMW i.val (ghosts i).history + if selected.val = i.val then 1 else 0 := by
  rw [trace_counts _ segment.lifted i i.val, count_issuers, segment.issuers]
  by_cases same : selected.val = i.val <;> simp [same]

/-- A running exact residual authenticates an actual live running worker. -/
theorem running_live {n : Nat} {profile : Profile} {family : RMWFamily}
    (cohort : Mixed.RankedCohort n profile family) {initial state : S}
    {ghosts : cohort.Ghosts initial} (current : cohort.Current state ghosts)
    (i : Fin n) {node : (cohort.descriptor i).graph.Index} {fuel : Nat}
    (running : (ghosts i).control = .running node fuel) :
    ∃ worker, state.workers[i.val]? = some worker ∧ worker.phase = .running := by
  have retained := (current i).1.2
  simp only [running] at retained
  cases fuel with
  | zero => exact False.elim retained.generated
  | succ fuel =>
    obtain ⟨worker, binding, _generated⟩ := (Mixed.rwp.here retained.generated).2
    refine ⟨worker, ?_, binding.running⟩
    rw [(current i).1.1, ← cohort.tid_eq i]
    exact binding.live

/-- Compose actual schedules at their common actual state. The ranked prefix
library's corresponding helper is private, so this small derived law is local. -/
theorem schedule_append {before middle final : S} {left right : List Action}
    {leftSeen rightSeen : List O} {profile : Profile} {family : RMWFamily}
    (first : TSO64.schedule before left profile family = .ok (middle, leftSeen))
    (second : TSO64.schedule middle right profile family = .ok (final, rightSeen)) :
    TSO64.schedule before (left ++ right) profile family = .ok (final, leftSeen ++ rightSeen) := by
  induction left generalizing before leftSeen with
  | nil =>
    have same : (before, []) = (middle, leftSeen) := Except.ok.inj first
    cases same
    exact second
  | cons action rest ih =>
    obtain ⟨head, tail, stepped, following, same⟩ := schedule_cons_ok first
    cases same
    have appended := ih following
    simp only [List.cons_append, TSO64.schedule, stepped, ok_bind, appended, pure_ok]

/-- The requests deliberately leave both workers unfinished at the overlap cut. -/
def requests (i : Fin 2) : BitVec 32 := if i.val = 0 then 3 else 9

theorem requests_nat (i : Fin 2) :
    (requests i).toNat = if i.val = 0 then 3 else 9 := by
  unfold requests
  split <;> rfl

/-- Both subjects use the same actual loaded ELF and production attachments.
Upper RSI halves, all modeled initial flag bits and the old word stay arbitrary. -/
def loadedSubjects (compiler : Compiler) (old : Word) (upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) :
    Fin 2 → CohortSubject (CounterResources.initial compiler old requests upper flags) :=
  fun i => {
    compiler := compiler
    site := CounterResources.site compiler old requests upper flags i
    call := CounterResources.call compiler old requests i
    pre := CounterResources.pre compiler old requests upper flags i
    ownedOnly := rfl }

theorem loadedSlots (compiler : Compiler) (old : Word) (upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) (i : Fin 2) :
    (loadedSubjects compiler old upper flags i).site.tid = i.val := rfl

abbrev loadedCohort (compiler : Compiler) (old : Word) (upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) :=
  counterRankedCohort (loadedSubjects compiler old upper flags) (loadedSlots compiler old upper flags)

abbrev loadedGhosts (compiler : Compiler) (old : Word) (upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) :=
  counterInitialGhosts (loadedSubjects compiler old upper flags) (loadedSlots compiler old upper flags)

/-- A genuinely interleaved actual prefix, with both actual workers still
running. Counts refer to the same exact ghosts and the real observation list. -/
structure Prefix {initial before : S} (cohort : Mixed.RankedCohort 2 .ownedOnly .arithmetic)
    (ghosts : cohort.Ghosts initial) (choices : Nat → Nat → Bool) where
  actions : List Action
  observations : List O
  final : S
  finalGhosts : cohort.Ghosts initial
  actual : TSO64.schedule before actions .ownedOnly .arithmetic = .ok (final, observations)
  valid : WellFormed final .ownedOnly
  workers : final.workers.length = 2
  empty : Quiescent final
  current : cohort.Current final finalGhosts
  completed : ∀ i, Mixed.CompletionInvariant (finalGhosts i)
  lifted : LiftTrace cohort.Step ghosts actions observations finalGhosts
  retiring : cohort.toCohort.RetirementTrace actions observations
  chosen : Mixed.ChoiceTrace.ChosenIssues choices actions
  pattern : issuers observations = [0, 1, 0]
  counts : ∀ i : Fin 2, Mixed.Counts.countRMW i.val observations = if i.val = 0 then 2 else 1
  ghostCounts : ∀ i : Fin 2,
    Mixed.Counts.logRMW i.val (finalGhosts i).history = if i.val = 0 then 2 else 1
  running : ∀ i : Fin 2, ∃ worker, final.workers[i.val]? = some worker ∧ worker.phase = .running

abbrev LoadedPrefix (compiler : Compiler) (old : Word) (upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) (choices : Nat → Nat → Bool) :=
  Prefix (before := CounterResources.initial compiler old requests upper flags)
    (loadedCohort compiler old upper flags) (loadedGhosts compiler old upper flags) choices

/-- Construct three first-own-RMW segments in order 0,1,0. Every recursive
choice offset counts that thread's issues across the entire actual prefix. -/
theorem construct_prefix (compiler : Compiler) (old : Word) (upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) (choices : Nat → Nat → Bool) :
    Nonempty (LoadedPrefix compiler old upper flags choices) := by
  let subjects := loadedSubjects compiler old upper flags
  let slots := loadedSlots compiler old upper flags
  let cohort := loadedCohort compiler old upper flags
  let ghosts := loadedGhosts compiler old upper flags
  have startCurrent := counterInitialGhosts_current subjects slots
  have startCompleted : Completed subjects slots ghosts := by intro i; trivial
  have historyEmpty : ∀ i, (ghosts i).history = [] := fun _ => rfl
  have requested : ∀ i, (subjects i).call.iterations.toNat = if i.val = 0 then 3 else 9 :=
    fun i => requests_nat i
  obtain ⟨first⟩ := run_to_own_RMW subjects slots ghosts
    (CounterResources.wellFormed compiler old requests upper flags)
    (CounterResources.workerUniverse2 compiler old requests upper flags)
    startCurrent (CounterResources.quiescent compiler old requests upper flags)
    startCompleted choices (fun _ => 0) 0 (by change 0 < 3; decide)
  have firstRight : Mixed.Counts.logRMW 1 (first.finalGhosts 1).history = 0 := by
    simpa [historyEmpty] using first.counts 1
  obtain ⟨second⟩ := run_to_own_RMW subjects slots first.finalGhosts first.valid first.workers
    first.current first.empty first.completed choices
    (fun tid => 0 + Mixed.ChoiceTrace.issues tid first.actions) 1 (by
      change Mixed.Counts.logRMW 1 (first.finalGhosts 1).history < 9
      rw [firstRight]; decide)
  have firstLeft : Mixed.Counts.logRMW 0 (first.finalGhosts 0).history = 1 := by
    simpa [historyEmpty] using first.counts 0
  have secondLeft : Mixed.Counts.logRMW 0 (second.finalGhosts 0).history = 1 := by
    simpa [firstLeft] using second.counts 0
  have actual01 := schedule_append first.actual second.actual
  have lifted01 := first.lifted.append second.lifted
  have chosen01 := Mixed.ChoiceTrace.chosen_append first.chosen second.chosen
  obtain ⟨third⟩ := run_to_own_RMW subjects slots second.finalGhosts second.valid second.workers
    second.current second.empty second.completed choices
    (fun tid => 0 + Mixed.ChoiceTrace.issues tid (first.actions ++ second.actions)) 0 (by
      change Mixed.Counts.logRMW 0 (second.finalGhosts 0).history < 3
      rw [secondLeft]; decide)
  have actual := schedule_append actual01 third.actual
  have lifted := lifted01.append third.lifted
  have chosen := Mixed.ChoiceTrace.chosen_append chosen01 third.chosen
  have pattern : issuers ((first.observations ++ second.observations) ++ third.observations) =
      [0, 1, 0] := by
    rw [issuers_append, issuers_append, first.issuers, second.issuers, third.issuers]
    rfl
  have counts : ∀ i : Fin 2,
      Mixed.Counts.countRMW i.val ((first.observations ++ second.observations) ++ third.observations) =
        if i.val = 0 then 2 else 1 := by
    intro i
    rw [count_issuers, pattern]
    by_cases left : i.val = 0
    · simp [left]
    · have right : i.val = 1 := by have bound := i.isLt; omega
      simp [right]
  have ghostCounts : ∀ i : Fin 2,
      Mixed.Counts.logRMW i.val (third.finalGhosts i).history = if i.val = 0 then 2 else 1 := by
    intro i
    rw [trace_counts cohort lifted i i.val, historyEmpty, Mixed.Counts.logRMW_nil, Nat.zero_add]
    exact counts i
  refine ⟨{
    actions := (first.actions ++ second.actions) ++ third.actions
    observations := (first.observations ++ second.observations) ++ third.observations
    final := third.final
    finalGhosts := third.finalGhosts
    actual := actual
    valid := third.valid
    workers := third.workers
    empty := third.empty
    current := third.current
    completed := third.completed
    lifted := lifted
    retiring := ?_
    chosen := chosen
    pattern := pattern
    counts := counts
    ghostCounts := ghostCounts
    running := ?_ }⟩
  · exact (cohort.toCohort.schedule_from_current
      (cohort.covers (CounterResources.workerUniverse2 compiler old requests upper flags))
      (cohort.current_toCohort startCurrent)
      (CounterResources.quiescent compiler old requests upper flags) actual).2.2.2
  · intro i
    have short : Mixed.Counts.logRMW i.val (third.finalGhosts i).history <
        (subjects i).call.iterations.toNat := by
      rw [ghostCounts i, requested i]
      split <;> decide
    obtain ⟨node, fuel, control⟩ := running_of_short_count third.completed i short
    exact running_live cohort third.current i control

/-- Production logical cleanup of the same returned endpoint, with the sum
read from that cleanup world's current RAM. Full loaded-cell preservation is
outside this record; the independent outside-byte frame is retained. -/
structure Cleanup (before final : S) (target : Atomics64.CellId64)
    (cell : Atomics64.Cell) (old : Word) where
  result : S × List Context
  value : Word
  retired : Lifecycle.retireAll final = .ok result
  valid : WellFormed result.1 .ownedOnly
  workers : result.1.workers = []
  contexts : result.2 = final.workers.reverse.map Worker.context
  resources : result.1.world.legacy.shared.resources = final.world.legacy.shared.resources
  cells : result.1.world.cells = final.world.cells
  ram : published result.1.world = published final.world
  history : ∃ labels, Atomics64.History final.world labels result.1.world
  revoked : ∀ worker ∈ final.workers, Lifecycle.WorkerRevoked result.1.world worker
  targetLive : result.1.world.cells target = some cell
  counter : loadQWord (published result.1.world) cell.address = .ok value
  total : value.toNat = (old.toNat + 12) % 2^64
  frame : ∀ query : Word, 8 ≤ (query - cell.address).toNat →
    (published result.1.world).read query = (published before.world).read query

/-- This helper is conditional only on an actual run and its actual returned
workers. The construction below supplies that very run after the overlap cut. -/
theorem cleanup_of_returned (compiler : Compiler) (old : Word) (upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) {final : S} {actions : List Action} {observations : List O}
    (actual : TSO64.schedule (CounterResources.initial compiler old requests upper flags)
      actions .ownedOnly .arithmetic = .ok (final, observations))
    (returned : ∀ worker ∈ final.workers, worker.phase = .returned) :
    Nonempty (Cleanup (CounterResources.initial compiler old requests upper flags) final
      (CounterResources.Image.resources compiler old).target
      (CounterResources.Image.resources compiler old).cell old) := by
  have finalLength : final.workers.length = 2 :=
    (ScheduleTrace.workers_length actual).trans
      (CounterResources.workerUniverse2 compiler old requests upper flags)
  have leftBound : 0 < final.workers.length := by rw [finalLength]; decide
  have rightBound : 1 < final.workers.length := by rw [finalLength]; decide
  have leftLive : final.workers[0]? = some (final.workers[0]'leftBound) :=
    List.getElem?_eq_getElem leftBound
  have rightLive : final.workers[1]? = some (final.workers[1]'rightBound) :=
    List.getElem?_eq_getElem rightBound
  obtain ⟨_value, _read, _total, frame⟩ := two_completed_total_frame
    (CounterResources.pre compiler old requests upper flags 0)
    (CounterResources.pre compiler old requests upper flags 1)
    (CounterResources.site_profile compiler old requests upper flags 0)
    (CounterResources.site_profile compiler old requests upper flags 1)
    (CounterResources.site_slot compiler old requests upper flags 0)
    (CounterResources.site_slot compiler old requests upper flags 1)
    (CounterResources.workerUniverse2 compiler old requests upper flags)
    (CounterResources.quiescent compiler old requests upper flags)
    actual leftLive rightLive
    (returned _ (List.mem_of_getElem? leftLive)) (returned _ (List.mem_of_getElem? rightLive))
    (CounterResources.Image.resources compiler old).target (CounterResources.Image.resources compiler old).cell
    (CounterResources.registered compiler old requests upper flags) rfl rfl old
    (CounterResources.initial_read compiler old requests upper flags)
  obtain ⟨result, value, retired, valid, workers, contexts, resources, cells, ram,
      history, revoked, counter, total⟩ := two_completed_retired_total
    (CounterResources.pre compiler old requests upper flags 0)
    (CounterResources.pre compiler old requests upper flags 1)
    (CounterResources.site_profile compiler old requests upper flags 0)
    (CounterResources.site_profile compiler old requests upper flags 1)
    (CounterResources.site_slot compiler old requests upper flags 0)
    (CounterResources.site_slot compiler old requests upper flags 1)
    (CounterResources.workerUniverse2 compiler old requests upper flags)
    (CounterResources.quiescent compiler old requests upper flags)
    (CounterResources.cleanupShape compiler old requests upper flags 0)
    (CounterResources.cleanupShape compiler old requests upper flags 1)
    (CounterResources.separate compiler old requests upper flags)
    actual leftLive rightLive
    (returned _ (List.mem_of_getElem? leftLive)) (returned _ (List.mem_of_getElem? rightLive))
    (CounterResources.Image.resources compiler old).target (CounterResources.Image.resources compiler old).cell
    (CounterResources.registered compiler old requests upper flags) rfl rfl old
    (CounterResources.initial_read compiler old requests upper flags)
  have stable := TSO64.schedule_stable actual
  refine ⟨{
    result := result
    value := value
    retired := retired
    valid := valid
    workers := workers
    contexts := contexts
    resources := resources
    cells := cells
    ram := ram
    history := history
    revoked := revoked
    targetLive := ?_
    counter := counter
    total := ?_
    frame := ?_ }⟩
  · rw [cells, stable.cells]
    exact CounterResources.registered compiler old requests upper flags
  · change value.toNat = (old.toNat + 3 + 9) % 2^64 at total
    simpa only [Nat.add_assoc] using total
  · intro query outside
    rw [ram]
    exact frame query outside

/-- The suffix starts from precisely lead.finalGhosts; the actual whole run,
collective trace, AF offsets and cleanup all refer to that same execution. -/
structure Output {initial : S} (cohort : Mixed.RankedCohort 2 .ownedOnly .arithmetic)
    (ghosts : cohort.Ghosts initial) (choices : Nat → Nat → Bool)
    (target : Atomics64.CellId64) (cell : Atomics64.Cell) (old : Word) where
  lead : Prefix (before := initial) cohort ghosts choices
  suffix : cohort.Suffix (before := lead.final) lead.finalGhosts choices
    (fun tid => 0 + Mixed.ChoiceTrace.issues tid lead.actions)
  actual : TSO64.schedule initial (lead.actions ++ suffix.actions) .ownedOnly .arithmetic =
    .ok (suffix.final, lead.observations ++ suffix.observations)
  lifted : LiftTrace cohort.Step ghosts (lead.actions ++ suffix.actions)
    (lead.observations ++ suffix.observations) suffix.finalGhosts
  chosen : Mixed.ChoiceTrace.ChosenIssues choices (lead.actions ++ suffix.actions)
  cleanup : Cleanup initial suffix.final target cell old

abbrev LoadedOutput (compiler : Compiler) (old : Word) (upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) (choices : Nat → Nat → Bool) :=
  Output (loadedCohort compiler old upper flags) (loadedGhosts compiler old upper flags)
    choices (CounterResources.Image.resources compiler old).target
    (CounterResources.Image.resources compiler old).cell old

/-- For either homogeneous frozen ELF, arbitrary old64, upper RSI halves,
modeled initial flags and per-thread AF choices, construct the actual 0,1,0
overlap, its returning suffix and production logical cleanup. No successful
future prefix/run, desired intermediate memory, return or result is a premise.
The cleaned current word is independently proved to be old + (3+9) modulo 2^64. -/
theorem complete (compiler : Compiler) (old : Word) (upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) (choices : Nat → Nat → Bool) :
    Nonempty (LoadedOutput compiler old upper flags choices) := by
  obtain ⟨lead⟩ := construct_prefix compiler old upper flags choices
  let cohort := loadedCohort compiler old upper flags
  obtain ⟨suffix⟩ := cohort.complete_from_current lead.valid lead.workers lead.current lead.empty
    choices (fun tid => 0 + Mixed.ChoiceTrace.issues tid lead.actions)
  have actual := schedule_append lead.actual suffix.actual
  obtain ⟨cleanup⟩ := cleanup_of_returned compiler old upper flags actual suffix.returned
  exact ⟨{
    lead := lead
    suffix := suffix
    actual := actual
    lifted := lead.lifted.append suffix.lifted
    chosen := Mixed.ChoiceTrace.chosen_append lead.chosen suffix.chosen
    cleanup := cleanup }⟩

#print axioms issuers
#print axioms issuers_append
#print axioms count_issuers
#print axioms Completed
#print axioms completed_step
#print axioms running_of_short_count
#print axioms trace_counts
#print axioms own_labels
#print axioms Segment
#print axioms Segment.issuers
#print axioms run_at_potential
#print axioms run_to_own_RMW
#print axioms Segment.counts
#print axioms running_live
#print axioms schedule_append
#print axioms requests
#print axioms requests_nat
#print axioms loadedSubjects
#print axioms loadedSlots
#print axioms loadedCohort
#print axioms loadedGhosts
#print axioms Prefix
#print axioms LoadedPrefix
#print axioms construct_prefix
#print axioms Cleanup
#print axioms cleanup_of_returned
#print axioms Output
#print axioms LoadedOutput
#print axioms complete

end EDSL.Corpus.V1.CounterOverlap

#audit_edsl
