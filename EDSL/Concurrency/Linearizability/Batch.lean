/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Concurrency.Linearizability

namespace EDSL.Concurrency.Linearizability.Batch

variable {Id Thread Input Output : Type}

/-- The independent public/internal labels of one completed occurrence. -/
def events (call : Call Id Thread Input Output) : @History Id Thread Input Output :=
  [.invoke call.id call.thread call.input, .point call,
    .respond call.id call.thread call.output]

/-- Retain one occurrence's labels without imposing positions in the global
history. A machine adapter can establish this equation from its own trace. -/
def projection [DecidableEq Id] (history : @History Id Thread Input Output) (id : Id) :
    @History Id Thread Input Output :=
  history.filter fun event => decide (event.id = id)

private theorem three_positions {α : Type} {predicate : α → Bool}
    {history : List α} {first middle last : α}
    (triple : history.filter predicate = [first, middle, last]) :
    ∃ i j k : Nat, i < j ∧ j < k ∧ history[i]? = some first ∧
      history[j]? = some middle ∧ history[k]? = some last := by
  obtain ⟨before, tail, split, _, _, rest⟩ := List.filter_eq_cons_iff.mp triple
  obtain ⟨between, tail', split', _, _, rest'⟩ := List.filter_eq_cons_iff.mp rest
  obtain ⟨after, tail'', split'', _, _, _⟩ := List.filter_eq_cons_iff.mp rest'
  subst history
  subst tail
  subst tail'
  refine ⟨before.length, before.length + 1 + between.length,
    before.length + 1 + between.length + 1 + after.length, by omega, by omega, ?_, ?_, ?_⟩
  · simp
  · rw [List.getElem?_append_right (by omega)]
    have offset : before.length + 1 + between.length - before.length = between.length + 1 := by omega
    rw [offset]
    simp
  · rw [List.getElem?_append_right (by omega)]
    have offset : before.length + 1 + between.length + 1 + after.length - before.length =
        (between.length + 1 + after.length) + 1 := by omega
    rw [offset]
    simp only [List.getElem?_cons_succ]
    rw [List.getElem?_append_right (by omega)]
    have offset' : between.length + 1 + after.length - between.length = after.length + 1 := by omega
    rw [offset']
    simp

private theorem nodup_field_injective {α β : Type} {cohort : List α} {field : α → β}
    (distinct : (cohort.map field).Nodup) {left right : α}
    (leftMem : left ∈ cohort) (rightMem : right ∈ cohort)
    (same : field left = field right) : left = right := by
  obtain ⟨i, leftAt⟩ := List.mem_iff_getElem?.mp leftMem
  obtain ⟨j, rightAt⟩ := List.mem_iff_getElem?.mp rightMem
  have indexSame : i = j := distinct.eq_of_getElem?_eq
    (by simpa using (List.getElem?_eq_some_iff.mp leftAt).1)
    (by simp only [List.getElem?_map, leftAt, rightAt, Option.map_some, same])
  exact Option.some.inj (leftAt.symm.trans (indexSame ▸ rightAt))

private theorem key_positions_unique [DecidableEq Id]
    {history : @History Id Thread Input Output}
    (distinct : (history.map Event.key).Nodup) {i j : Nat}
    {left right : Event Id Thread Input Output}
    (leftAt : history[i]? = some left) (rightAt : history[j]? = some right)
    (same : left.key = right.key) : i = j := by
  apply distinct.eq_of_getElem?_eq
  · simpa using (List.getElem?_eq_some_iff.mp leftAt).1
  · simp only [List.getElem?_map, leftAt, rightAt, Option.map_some, same]

private theorem key_findIdx [DecidableEq Id]
    {history : @History Id Thread Input Output}
    (distinct : (history.map Event.key).Nodup) {index : Nat}
    {event : Event Id Thread Input Output} (atIndex : history[index]? = some event) :
    history.findIdx (fun entry => decide (entry.key = event.key)) = index := by
  have present : ∃ entry ∈ history, decide (entry.key = event.key) = true :=
    ⟨event, List.mem_of_getElem? atIndex, by simp⟩
  have bounded := List.findIdx_lt_length_of_exists present
  have found := List.findIdx_getElem (p := fun entry : Event Id Thread Input Output => decide (entry.key = event.key))
    (w := bounded)
  apply key_positions_unique distinct (List.getElem?_eq_getElem bounded) atIndex
  exact of_decide_eq_true found

private theorem point_of_interval [DecidableEq Id]
    {history : @History Id Thread Input Output} {interval : Interval Id Thread Input Output}
    (member : interval ∈ intervals history) :
    history[interval.point]? = some (.point interval.call) ∧
      interval.invocation = history.findIdx (fun event => decide (event.key = (interval.call.id, 0))) ∧
      interval.response = history.findIdx (fun event => decide (event.key = (interval.call.id, 2))) := by
  obtain ⟨⟨event, index⟩, present, located⟩ := List.mem_filterMap.mp member
  cases event <;> simp only [locate, Option.some.injEq, reduceCtorEq] at located
  case point call =>
    subst interval
    exact ⟨List.mk_mem_zipIdx_iff_getElem?.mp present, rfl, rfl⟩

private theorem point_call_mem [DecidableEq Id]
    {cohort : List (Call Id Thread Input Output)} {history : @History Id Thread Input Output}
    (closed : ∀ event ∈ history, ∃ call ∈ cohort, call.id = event.id)
    (triples : ∀ call ∈ cohort, projection history call.id = events call)
    {call : Call Id Thread Input Output} (pointMem : Event.point call ∈ history) :
    call ∈ cohort := by
  obtain ⟨entry, member, identity⟩ := closed (.point call) pointMem
  have selected : Event.point call ∈ projection history entry.id :=
    List.mem_filter.mpr ⟨pointMem, by simp only [Event.id]; exact decide_eq_true identity.symm⟩
  rw [triples entry member] at selected
  have same : call = entry := by simpa [events] using selected
  exact same ▸ member

/-- A closed finite cohort has one complete occurrence per distinct thread.
Per-occurrence projection equations supply the order, payload matching and
absence of duplicate labels. The existing global `Protocol`, including its
computed `findIdx` boundaries, is a conclusion rather than an admission.

This is a label theorem only. A machine adapter must independently justify its
cohort, emitted labels, occurrence identities and projection equations. -/
theorem protocol [DecidableEq Id]
    {cohort : List (Call Id Thread Input Output)} {history : @History Id Thread Input Output}
    (_ids : (cohort.map Call.id).Nodup)
    (threads : (cohort.map Call.thread).Nodup)
    (closed : ∀ event ∈ history, ∃ call ∈ cohort, call.id = event.id)
    (triples : ∀ call ∈ cohort, projection history call.id = events call) :
    Protocol history := by
  have distinct : (history.map Event.key).Nodup := by
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map, List.pairwise_iff_getElem]
    intro i j hi hj ordered same
    obtain ⟨call, member, identity⟩ := closed history[i] (List.getElem_mem hi)
    have fiber : (projection history call.id).Pairwise (fun left right => left.key ≠ right.key) := by
      rw [triples call member]
      simp [events, Event.key, Event.id, Event.kind]
    have pair := List.pairwise_iff_getElem.mp (List.pairwise_filter.mp fiber) i j hi hj ordered
    have leftIdentity : history[i].id = call.id := identity.symm
    have rightIdentity : history[j].id = call.id := by
      exact (congrArg Prod.fst same).symm.trans leftIdentity
    exact pair (by simpa [projection] using leftIdentity) (by simpa [projection] using rightIdentity) same
  have bounds : ∀ interval ∈ intervals history,
      interval.invocation < interval.point ∧ interval.point < interval.response ∧
      history[interval.invocation]? = some (.invoke interval.call.id interval.call.thread interval.call.input) ∧
      history[interval.point]? = some (.point interval.call) ∧
      history[interval.response]? = some (.respond interval.call.id interval.call.thread interval.call.output) := by
    intro interval member
    obtain ⟨pointAt, invocation, response⟩ := point_of_interval member
    have inCohort := point_call_mem closed triples (List.mem_of_getElem? pointAt)
    obtain ⟨i, j, k, ordered, ordered', atInvoke, atPoint, atResponse⟩ :=
      three_positions (triples interval.call inCohort)
    have pointIndex : j = interval.point := key_positions_unique distinct atPoint pointAt rfl
    have invocationIndex : interval.invocation = i := by
      rw [invocation]
      exact key_findIdx distinct atInvoke
    have responseIndex : interval.response = k := by
      rw [response]
      exact key_findIdx distinct atResponse
    simpa only [← invocationIndex, ← responseIndex, pointIndex] using
      And.intro ordered (And.intro ordered' (And.intro atInvoke (And.intro atPoint atResponse)))
  refine ⟨distinct, ?_, bounds, ?_⟩
  · intro event member
    obtain ⟨call, callMem, identity⟩ := closed event member
    have selected : Event.point call ∈ projection history call.id := by
      rw [triples call callMem]
      simp [events]
    have pointMem : Event.point call ∈ history := (List.mem_filter.mp selected).1
    obtain ⟨index, atPoint⟩ := List.mem_iff_getElem?.mp pointMem
    refine ⟨⟨call,
      history.findIdx (fun event => decide (event.key = (call.id, 0))), index,
      history.findIdx (fun event => decide (event.key = (call.id, 2)))⟩, ?_, identity⟩
    exact List.mem_filterMap.mpr ⟨(.point call, index),
      List.mk_mem_zipIdx_iff_getElem?.mpr atPoint, rfl⟩
  · apply (intervals_chronological history).imp_of_mem
    intro left right leftMem rightMem ordered
    apply Or.inl
    intro sameThread
    have leftAt := (point_of_interval leftMem).1
    have rightAt := (point_of_interval rightMem).1
    have sameCall := nodup_field_injective threads
      (point_call_mem closed triples (List.mem_of_getElem? leftAt))
      (point_call_mem closed triples (List.mem_of_getElem? rightAt)) sameThread
    have sameIndex := key_positions_unique distinct leftAt rightAt (by rw [sameCall])
    omega

/-- The computed chronological point order contains every cohort call once.
This does not prescribe a sequential object specification. -/
theorem calls_perm [DecidableEq Id]
    {cohort : List (Call Id Thread Input Output)} {history : @History Id Thread Input Output}
    (ids : (cohort.map Call.id).Nodup)
    (threads : (cohort.map Call.thread).Nodup)
    (closed : ∀ event ∈ history, ∃ call ∈ cohort, call.id = event.id)
    (triples : ∀ call ∈ cohort, projection history call.id = events call) :
    (calls history).Perm cohort := by
  have valid := protocol ids threads closed triples
  have leftNodup : (calls history).Nodup :=
    List.Pairwise.of_map Call.id (fun _ _ different same => different (congrArg Call.id same))
      valid.unique_calls
  have rightNodup : cohort.Nodup :=
    List.Pairwise.of_map Call.id (fun _ _ different same => different (congrArg Call.id same)) ids
  apply (List.perm_ext_iff_of_nodup leftNodup rightNodup).mpr
  intro call
  rw [calls_eq_points, List.mem_filterMap]
  constructor
  · rintro ⟨event, member, point⟩
    cases event <;> simp only [Event.call?, Option.some.injEq, reduceCtorEq] at point
    case point entry =>
      subst call
      exact point_call_mem closed triples member
  · intro member
    have selected : Event.point call ∈ projection history call.id := by
      rw [triples call member]
      simp [events]
    exact ⟨.point call, (List.mem_filter.mp selected).1, rfl⟩

/-- Independent sequential correctness can be composed through the existing
linearization theorem once actual occurrence projections have been justified. -/
theorem linearization [DecidableEq Id]
    {cohort : List (Call Id Thread Input Output)} {history : @History Id Thread Input Output}
    {specification : List (Call Id Thread Input Output) → Prop}
    (ids : (cohort.map Call.id).Nodup)
    (threads : (cohort.map Call.thread).Nodup)
    (closed : ∀ event ∈ history, ∃ call ∈ cohort, call.id = event.id)
    (triples : ∀ call ∈ cohort, projection history call.id = events call)
    (sequential : specification (calls history)) :
    Linearization history specification :=
  linearize (protocol ids threads closed triples) sequential

end EDSL.Concurrency.Linearizability.Batch

#audit_edsl
