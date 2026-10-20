/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Audit

namespace EDSL.Concurrency.Linearizability

/-- Identity is global to the finite history; thread identity is separate.
Input and output are abstract, so this infrastructure fixes no machine width. -/
structure Call (Id Thread Input Output : Type) where
  id : Id
  thread : Thread
  input : Input
  output : Output
  deriving DecidableEq, Repr

/-- `point` is an internal witness, not an external response. A concrete
adapter must justify it by execution. Erasing points gives the public history. -/
inductive Event (Id Thread Input Output : Type) where
  | invoke (id : Id) (thread : Thread) (input : Input)
  | point (call : Call Id Thread Input Output)
  | respond (id : Id) (thread : Thread) (output : Output)
  deriving DecidableEq, Repr

variable {Id Thread Input Output : Type}

abbrev Operation := Call Id Thread Input Output
abbrev History := List (Event Id Thread Input Output)

def Event.id : Event Id Thread Input Output → Id
  | .invoke id _ _ | .respond id _ _ => id
  | .point call => call.id

def Event.kind : Event Id Thread Input Output → Nat
  | .invoke .. => 0
  | .point .. => 1
  | .respond .. => 2

def Event.call? : Event Id Thread Input Output → Option (Call Id Thread Input Output)
  | .point call => some call
  | _ => none

def Event.key (event : Event Id Thread Input Output) : Id × Nat := (event.id, event.kind)

def publicHistory (history : @History Id Thread Input Output) : @History Id Thread Input Output :=
  history.filter fun event => event.kind != 1

structure Interval (Id Thread Input Output : Type) where
  call : Call Id Thread Input Output
  invocation : Nat
  point : Nat
  response : Nat
  deriving DecidableEq, Repr

/-- Missing labels yield the list length, and are rejected by `Protocol`.
No future response or origin is manufactured by this lookup. -/
def locate [DecidableEq Id] (history : @History Id Thread Input Output)
    (entry : Event Id Thread Input Output × Nat) : Option (Interval Id Thread Input Output) :=
  match entry.1 with
  | .point call => some ⟨call,
      history.findIdx (fun event => decide (event.key = (call.id, 0))), entry.2,
      history.findIdx (fun event => decide (event.key = (call.id, 2)))⟩
  | _ => none

/-- The proposed serial order is computed from chronological internal points,
never supplied as an arbitrary permutation of completed calls. -/
def intervals [DecidableEq Id] (history : @History Id Thread Input Output) : List (Interval Id Thread Input Output) :=
  history.zipIdx.filterMap (locate history)

def calls [DecidableEq Id] (history : @History Id Thread Input Output) : List (Call Id Thread Input Output) :=
  (intervals history).map Interval.call

theorem calls_eq_points [DecidableEq Id] (history : @History Id Thread Input Output) :
    calls history = history.filterMap Event.call? := by
  unfold calls intervals
  rw [List.map_filterMap]
  have same : (fun entry => (locate history entry).map Interval.call) =
      (fun entry : Event Id Thread Input Output × Nat => Event.call? entry.1) := by
    funext entry
    rcases entry with ⟨event, index⟩
    cases event <;> rfl
  rw [same]
  change history.zipIdx.filterMap (Event.call? ∘ Prod.fst) = _
  rw [← List.filterMap_map, List.zipIdx_map_fst]

/-- Exactly one invocation, internal point and response per identity; matching
thread, input and output; strict containment of the point in the call interval;
and at most one outstanding call per thread. This checks only a finite label
protocol. It does not assume a sequential specification or real-time order. -/
def Protocol [DecidableEq Id] (history : @History Id Thread Input Output) : Prop :=
  (history.map Event.key).Nodup ∧
  (∀ event ∈ history, ∃ interval ∈ intervals history, interval.call.id = event.id) ∧
  (∀ interval ∈ intervals history,
    interval.invocation < interval.point ∧ interval.point < interval.response ∧
    history[interval.invocation]? = some (.invoke interval.call.id interval.call.thread interval.call.input) ∧
    history[interval.point]? = some (.point interval.call) ∧
    history[interval.response]? = some (.respond interval.call.id interval.call.thread interval.call.output)) ∧
  (intervals history).Pairwise (fun left right => left.call.thread ≠ right.call.thread ∨
    left.response < right.invocation ∨ right.response < left.invocation)

instance protocolDecidable [DecidableEq Id] [DecidableEq Thread] [DecidableEq Input] [DecidableEq Output]
    (history : @History Id Thread Input Output) : Decidable (Protocol history) := by
  unfold Protocol
  infer_instance

def check [DecidableEq Id] [DecidableEq Thread] [DecidableEq Input] [DecidableEq Output] (history : @History Id Thread Input Output) : Bool := decide (Protocol history)

theorem check_sound [DecidableEq Id] [DecidableEq Thread] [DecidableEq Input] [DecidableEq Output]
    {history : @History Id Thread Input Output} (checked : check history = true) :
    Protocol history := of_decide_eq_true checked

theorem Protocol.unique_calls [DecidableEq Id] {history : @History Id Thread Input Output}
    (valid : Protocol history) : ((calls history).map Call.id).Nodup := by
  rw [calls_eq_points, List.nodup_iff_pairwise_ne, List.pairwise_map]
  have distinct : history.Pairwise (fun left right => left.key ≠ right.key) := by
    simpa only [List.nodup_iff_pairwise_ne, List.pairwise_map] using valid.1
  apply List.Pairwise.filterMap Event.call? ?_ distinct
  intro left right different a ha b hb same
  cases left <;> simp only [Event.call?, Option.some.injEq, reduceCtorEq] at ha
  case point left =>
    subst a
    cases right <;> simp only [Event.call?, Option.some.injEq, reduceCtorEq] at hb
    case point right =>
      subst b
      exact different (Prod.ext same rfl)

/-- Pending means an invocation with no response of the same identity. The
complete-history theorem below deliberately rejects such prefixes; it does not
claim a standard pending-history extension without a real response witness. -/
def Pending (history : @History Id Thread Input Output) (id : Id) : Prop :=
  (id, 0) ∈ history.map Event.key ∧ (id, 2) ∉ history.map Event.key

theorem Protocol.no_pending [DecidableEq Id] {history : @History Id Thread Input Output}
    (valid : Protocol history) (id : Id) : ¬ Pending history id := by
  rintro ⟨invoked, missing⟩
  obtain ⟨event, member, key⟩ := List.mem_map.mp invoked
  obtain ⟨interval, present, identity⟩ := valid.2.1 event member
  have response := (valid.2.2.1 interval present).2.2.2.2
  have inHistory := List.mem_of_getElem? response
  apply missing
  have same : interval.call.id = id := identity.trans (congrArg Prod.fst key)
  exact List.mem_map.mpr ⟨_, inHistory, by simp [Event.key, Event.id, Event.kind, same]⟩

private theorem zipIdx_order (history : @History Id Thread Input Output) :
    history.zipIdx.Pairwise (fun left right => left.2 < right.2) := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj less
  simpa using less

theorem intervals_chronological [DecidableEq Id] (history : @History Id Thread Input Output) :
    (intervals history).Pairwise (fun left right => left.point < right.point) := by
  apply (zipIdx_order history).filterMap (locate history)
  intro left right ordered a ha b hb
  cases left with | mk event index =>
    cases event <;> simp only [locate, Option.some.injEq, reduceCtorEq] at ha
    case point call =>
      subst a
      cases right with | mk event index =>
        cases event <;> simp only [locate, Option.some.injEq, reduceCtorEq] at hb
        case point call => subst b; exact ordered

/-- A strict serial order of all and only complete calls, extending external
response-before-invocation order. For any independent object specification,
`specification (calls history)` supplies the remaining sequential obligation. -/
structure Linearization [DecidableEq Id] (history : @History Id Thread Input Output)
    (specification : List (Call Id Thread Input Output) → Prop) : Prop where
  protocol : Protocol history
  sequential : specification (calls history)
  uniqueCalls : ((calls history).map Call.id).Nodup
  chronological : (intervals history).Pairwise (fun left right => left.point < right.point)
  realTime : ∀ left ∈ intervals history, ∀ right ∈ intervals history,
    left.response < right.invocation → left.point < right.point
  /-- No earlier element in the serial list is required to follow a later one
  by external real time. Together with exact coverage this is a total-order
  extension of real time, rather than merely a chronological RMW sequence. -/
  extendsRealTime : (intervals history).Pairwise
    (fun earlier later => ¬ later.response < earlier.invocation)

theorem linearize [DecidableEq Id] {history : @History Id Thread Input Output}
    {specification : List (Call Id Thread Input Output) → Prop}
    (valid : Protocol history) (sequential : specification (calls history)) :
    Linearization history specification := by
  have chronological := intervals_chronological history
  refine ⟨valid, sequential, valid.unique_calls, chronological, ?_, ?_⟩
  · intro left leftMem right rightMem nonoverlap
    have l := valid.2.2.1 left leftMem
    have r := valid.2.2.1 right rightMem
    omega
  · apply chronological.imp_of_mem
    intro earlier later earlierMem laterMem ordered reversed
    have e := valid.2.2.1 earlier earlierMem
    have l := valid.2.2.1 later laterMem
    omega

end EDSL.Concurrency.Linearizability

#audit_edsl
