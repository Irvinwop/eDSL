/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.C23Projection.AtomicTrace.Graph
import EDSL.OS.TSO64.PublishedOrder
import EDSL.OS.TSO64.StoreHistory.Order

/-!
Publication ranks for actual writer identities in a finite successful schedule.
Rank zero names an initial boundary. Every other rank retains a full actual
publication witness and its cell, and is the original action position plus one.
Buffered keys are original thread/occurrence pairs; RMW keys are original
action positions. Equal words never identify writers or publications.

The prefix bridge starts its publication map at `PublishedHistory.empty` and
permits nonempty initial queues and arbitrary stream offsets. It authenticates
published metadata against the complete schedule, without assigning earlier
instruction issues to incoming queued entries. Boundary ranks alone assert no
initial value, cell registration or access authority. These results establish
neither source-language legality nor synchronization or native refinement.
-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.PublishedHistory

/-- A publication witnessed inside an action prefix is the same full stamp in
the successful complete schedule. Its own actual prefix and step suffice; no
success or final-state claim about the rest of the shorter result is needed. -/
theorem WriteAt.lift_prefix {state : State} {actions : List Action}
    {prefixResult result : State × List Observation} {profile : Profile}
    {offset stop : Nat} {stamp : Stamp}
    (witness : WriteAt state (actions.take stop) prefixResult profile offset stamp)
    (success : schedule state actions profile = .ok result) :
    Nonempty (WriteAt state actions result profile offset stamp) := by
  have inside : witness.index < stop :=
    Nat.lt_of_lt_of_le (List.getElem_of_getElem? witness.actionAt).1
      (List.length_take_le _ _)
  have actionAt : actions[witness.index]? = some witness.action := by
    simpa only [List.getElem?_take_of_lt inside] using witness.actionAt
  have prefixRun : schedule state (actions.take witness.index) profile =
      .ok (witness.before, prefixResult.2.take witness.index) := by
    simpa only [List.take_take, Nat.min_eq_left (Nat.le_of_lt inside)] using witness.prefixRun
  have bound : witness.index < result.2.length := by
    rw [ScheduleTrace.length success]
    exact (List.getElem_of_getElem? actionAt).1
  let observation := result.2[witness.index]'bound
  have observed : result.2[witness.index]? = some observation := List.getElem?_eq_getElem bound
  obtain ⟨before, action, next, actualPrefix, actualAction, stepped⟩ :=
    ScheduleTrace.observation_at success observed
  have prefixes : (witness.before, prefixResult.2.take witness.index) =
      (before, result.2.take witness.index) :=
    Except.ok.inj (prefixRun.symm.trans actualPrefix)
  have beforeEq : witness.before = before := congrArg Prod.fst prefixes
  have actionEq : witness.action = action := Option.some.inj (actionAt.symm.trans actualAction)
  have originalStep : step before action profile = .ok (witness.next, witness.observation) := by
    simpa only [beforeEq, actionEq] using witness.stepped
  have sameStep : (witness.next, witness.observation) = (next, observation) :=
    Except.ok.inj (originalStep.symm.trans stepped)
  have observationEq : witness.observation = observation := congrArg Prod.snd sameStep
  refine ⟨⟨witness.index, observation, before, action, next, witness.position, observed,
    actualPrefix, actualAction, stepped, ?_⟩⟩
  simpa only [observationEq] using witness.written

end EDSL.OS.TSO64.PublishedHistory

namespace EDSL.OS.TSO64.C23Projection.AtomicTrace
open PublishedHistory

/-- An execution-derived writer rank. The initial constructor is a boundary
identity only. A publication retains its complete actual cause and cell, with
the existing graph key and original action position rather than a value key. -/
inductive WriterRank (initial : State) (actions : List Action)
    (result : State × List Observation) (profile : Profile) (offset : Nat)
    (target : Atomics64.CellId64) : WriterId → Nat → Prop where
  | initial : WriterRank initial actions result profile offset target (.initial target) 0
  | publication {stamp : PublishedHistory.Stamp}
      (actual : PublishedHistory.WriteAt initial actions result profile offset stamp)
      (cell : stamp.cause.cell = target) :
      WriterRank initial actions result profile offset target
        (Graph.publicationKey stamp) (stamp.position + 1)

/-- Equal graph keys of actual publications identify the entire stamp.
Buffered uniqueness uses the actual thread/occurrence identity and recovers
the reference and word from the run. RMW identity fixes the action position;
the observation at that position fixes its complete cause. -/
theorem publicationKey_writeAt_unique {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {offset : Nat}
    {firstStamp secondStamp : PublishedHistory.Stamp}
    (success : schedule initial actions profile = .ok result)
    (sequenced : Sequenced initial)
    (first : PublishedHistory.WriteAt initial actions result profile offset firstStamp)
    (second : PublishedHistory.WriteAt initial actions result profile offset secondStamp)
    (same : Graph.publicationKey firstStamp = Graph.publicationKey secondStamp) :
    firstStamp = secondStamp := by
  have atSameIndex (indices : first.index = second.index) : firstStamp = secondStamp := by
    have observed : result.2[first.index]? = some second.observation := by
      simpa only [indices] using second.observed
    have observationEq : first.observation = second.observation :=
      Option.some.inj (first.observed.symm.trans observed)
    have written : writeOf first.observation = some secondStamp.cause := by
      simpa only [observationEq] using second.written
    have causeEq : firstStamp.cause = secondStamp.cause :=
      Option.some.inj (first.written.symm.trans written)
    have positionEq : firstStamp.position = secondStamp.position := by
      rw [first.position, second.position, indices]
    cases firstStamp with
    | mk firstPosition firstCause =>
      cases secondStamp with
      | mk secondPosition secondCause =>
        change firstPosition = secondPosition at positionEq
        change firstCause = secondCause at causeEq
        cases positionEq
        cases causeEq
        rfl
  apply atSameIndex
  cases firstStamp with
  | mk firstPosition firstCause =>
    cases secondStamp with
    | mk secondPosition secondCause =>
      cases firstCause with
      | buffered firstTid firstReference firstValue firstOccurrence =>
        cases secondCause with
        | buffered secondTid secondReference secondValue secondOccurrence =>
          change WriterId.store firstTid firstOccurrence = .store secondTid secondOccurrence at same
          obtain ⟨threadEq, occurrenceEq⟩ := WriterId.store.inj same
          subst secondTid
          subst secondOccurrence
          exact (StoreHistory.managed_drain_identity_unique success sequenced
            first.buffered_observed second.buffered_observed).1
        | rmw secondTid secondEvent => cases same
      | rmw firstTid firstEvent =>
        cases secondCause with
        | buffered secondTid secondReference secondValue secondOccurrence => cases same
        | rmw secondTid secondEvent =>
          have positions : firstPosition = secondPosition := WriterId.rmw.inj same
          have firstAt : firstPosition = offset + first.index := first.position
          have secondAt : secondPosition = offset + second.index := second.position
          omega

/-- A writer identity has one rank in the actual successful sequenced run.
No value equality, empty initial queues or desired numerical rank is assumed. -/
theorem WriterRank.unique {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {offset : Nat}
    {target : Atomics64.CellId64} {writer : WriterId} {firstRank secondRank : Nat}
    (success : schedule initial actions profile = .ok result)
    (sequenced : Sequenced initial)
    (first : WriterRank initial actions result profile offset target writer firstRank)
    (second : WriterRank initial actions result profile offset target writer secondRank) :
    firstRank = secondRank := by
  have rankEq {leftWriter rightWriter : WriterId} {leftRank rightRank : Nat}
      (left : WriterRank initial actions result profile offset target leftWriter leftRank)
      (right : WriterRank initial actions result profile offset target rightWriter rightRank)
      (identity : leftWriter = rightWriter) : leftRank = rightRank := by
    cases left with
    | initial =>
      cases right with
      | initial => rfl
      | @publication stamp _actual _cell =>
        cases stamp with
        | mk position cause => cases cause <;> cases identity
    | @publication firstStamp firstActual _firstCell =>
      cases right with
      | initial =>
        cases firstStamp with
        | mk position cause => cases cause <;> cases identity
      | @publication secondStamp secondActual _secondCell =>
        have stamps := publicationKey_writeAt_unique success sequenced firstActual secondActual identity
        exact congrArg (fun stamp : PublishedHistory.Stamp => stamp.position + 1) stamps
  exact rankEq first second rfl

/-- Resolve the actual published source and its numerical published view at
any actual prefix of a complete successful run. The map starts empty at the
supplied offset; the scheduler's initial queues may be nonempty. No access,
initial-quiescence, sequencing or caller-supplied rank premise is needed. -/
theorem publishedSource_prefix_rank {initial before : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {cut offset : Nat}
    (success : schedule initial actions profile = .ok result)
    (prefixRun : schedule initial (actions.take cut) profile =
      .ok (before, result.2.take cut))
    (target : Atomics64.CellId64) :
    WriterRank initial actions result profile offset target
      (publishedSource (PublishedHistory.after offset (result.2.take cut) PublishedHistory.empty) target)
      (PublishedOrder.view (PublishedHistory.after offset (result.2.take cut) PublishedHistory.empty)
        target) := by
  cases found : PublishedHistory.after offset (result.2.take cut) PublishedHistory.empty target with
  | none =>
    simpa only [publishedSource, PublishedOrder.view, found] using
      (WriterRank.initial (initial := initial) (actions := actions) (result := result)
        (profile := profile) (offset := offset) (target := target))
  | some stamp =>
    obtain ⟨actual, cell, _noLater⟩ := PublishedHistory.newest_write_at prefixRun found
    obtain ⟨full⟩ := actual.lift_prefix success
    have sourceEq :
        publishedSource (PublishedHistory.after offset (result.2.take cut) PublishedHistory.empty)
          target = Graph.publicationKey stamp := by
      simp only [publishedSource, found, Graph.publicationKey]
      cases stamp.cause <;> rfl
    have rankEq :
        PublishedOrder.view (PublishedHistory.after offset (result.2.take cut) PublishedHistory.empty)
          target = stamp.position + 1 := by
      simp only [PublishedOrder.view, found]
    rw [sourceEq, rankEq]
    exact WriterRank.publication full cell

end EDSL.OS.TSO64.C23Projection.AtomicTrace

#audit_edsl
