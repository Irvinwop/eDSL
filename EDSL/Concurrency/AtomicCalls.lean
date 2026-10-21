/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Concurrency.C23Atomic.Coherence

/-!
An independent atomic primitive interface and completed-call history contract.
Requests fix acquire loads, release stores, or an explicitly ordered RMW with
an intended value transformation. A reply is typed by the request: a store has
a unit reply, while a load/RMW returns its observed value.

The event associated with a call is its source access, not a claim that a
buffered store publishes inside its invocation/return interval. Modification
ranks remain graph metadata and can be determined by later publication.
Machine adapters must derive these histories from actual invocation, access,
and return origins. This module provides neither that adapter nor a source
frontend, compiler preservation, native correspondence, or corpus certificate.
-/

set_option autoImplicit false

namespace EDSL.Concurrency.AtomicCalls
variable {Location Value : Type}

inductive Request (Location Value : Type) where
  | loadAcquire (object : Location)
  | storeRelease (object : Location) (value : Value)
  | rmw (object : Location) (order : C23Atomic.RMWOrder) (update : Value → Value)

def Request.object : Request Location Value → Location
  | .loadAcquire object | .storeRelease object _ | .rmw object _ _ => object

def Request.Reply : Request Location Value → Type
  | .loadAcquire _ | .rmw .. => Value
  | .storeRelease .. => PUnit

/-- The request determines the source order and the intended update. An RMW's
transformation is not reconstructed from its observed machine postvalue. -/
def Request.access (request : Request Location Value) (reply : request.Reply) :
    C23Atomic.Access Value :=
  match request with
  | .loadAcquire _ => .load .acquire reply
  | .storeRelease _ value => .store .release value
  | .rmw _ order update => .rmw order reply (update reply)

/-- One logical call occurrence. Positions name original action boundaries;
the access must occur after invocation and strictly before the actual return.
These data are a postcondition witness, never an admission oracle. -/
structure Call (Location Value : Type) where
  thread : Nat
  occurrence : Nat
  request : Request Location Value
  reply : request.Reply
  invoked : Nat
  performed : Nat
  returned : Nat

def Call.key (call : Call Location Value) : Nat × Nat :=
  (call.thread, call.occurrence)

def Call.event (call : Call Location Value) : C23Atomic.Event Location Value :=
  ⟨some call.thread, call.request.object, call.request.access call.reply⟩

/-- Complete structural call/event correspondence. All relevant atomic calls
are represented in access order, with one event per distinct occurrence. Calls
on one logical thread do not overlap. Initializers are a separate already-
initialized boundary. No memory-order legality or machine origin is assumed. -/
structure Realizes (initials : List (C23Atomic.Event Location Value))
    (calls : List (Call Location Value)) (candidate : C23Atomic.Candidate Location Value) : Prop where
  events : candidate.events = initials ++ calls.map Call.event
  initial : ∀ event ∈ initials, event.thread = none ∧
    ∃ value, event.access = .initialize value
  keys : (calls.map Call.key).Nodup
  ordered : calls.Pairwise (fun first second => first.performed < second.performed)
  intervals : ∀ call ∈ calls, call.invoked ≤ call.performed ∧ call.performed < call.returned
  threadOrder : ∀ first ∈ calls, ∀ second ∈ calls,
    first.thread = second.thread → first.performed < second.performed →
      first.returned ≤ second.invoked

/-- The independent behavioral target combines call correspondence with every
field of the existing atomic-fragment legality predicate. A machine candidate
must construct this witness from its execution; clients do not supply it as a
precondition. Publication need not occur before a store's return. -/
structure History (initials : List (C23Atomic.Event Location Value))
    (calls : List (Call Location Value)) (candidate : C23Atomic.Candidate Location Value) : Prop where
  realizes : Realizes initials calls candidate
  legal : C23Atomic.Legal candidate

theorem Realizes.call_at {initials : List (C23Atomic.Event Location Value)}
    {calls : List (Call Location Value)} {candidate : C23Atomic.Candidate Location Value}
    (history : Realizes initials calls candidate) (index : Fin calls.length) :
    candidate.events[initials.length + index.val]? = some calls[index.val].event := by
  rw [history.events, List.getElem?_append_right (by omega)]
  have aligned : initials.length + index.val - initials.length = index.val := by omega
  rw [aligned]
  simp only [List.getElem?_map, List.getElem?_eq_getElem index.isLt, Option.map_some]

/-- Same-thread source access order comes from the actual call/event ordering,
not from a total order imposed on modification ranks. -/
theorem Realizes.sequenced {initials : List (C23Atomic.Event Location Value)}
    {calls : List (Call Location Value)} {candidate : C23Atomic.Candidate Location Value}
    (history : Realizes initials calls candidate) (first second : Fin calls.length)
    (earlier : first.val < second.val)
    (thread : calls[first.val].thread = calls[second.val].thread) :
    C23Atomic.SeqBefore candidate (initials.length + first.val) (initials.length + second.val) := by
  refine ⟨by omega, calls[first.val].event, calls[second.val].event,
    calls[first.val].thread, history.call_at first, history.call_at second, rfl, ?_⟩
  change some calls[second.val].thread = some calls[first.val].thread
  exact congrArg some thread.symm

/-- Every observed call value is tied to its selected actual graph writer.
Equal values cannot change the supplied read-from identity. Initialization and
qualifying release synchronization remain distinct alternatives. -/
theorem History.read_source {initials : List (C23Atomic.Event Location Value)}
    {calls : List (Call Location Value)} {candidate : C23Atomic.Candidate Location Value}
    (history : History initials calls candidate) (index : Fin calls.length) {value : Value}
    (observed : calls[index.val].event.access.readValue = some value) :
    ∃ writer, C23Atomic.ReadsFrom candidate (initials.length + index.val) writer ∧
      C23Atomic.Writes candidate writer calls[index.val].request.object value := by
  have read : C23Atomic.Reads candidate (initials.length + index.val)
      calls[index.val].request.object value :=
    ⟨calls[index.val].event, history.realizes.call_at index, rfl, observed⟩
  obtain ⟨writer, source⟩ := history.legal.wellFormed.readsSource _ _ _ read
  exact ⟨writer, source, source.source read⟩

/-- A direct qualifying release/acquire read establishes synchronization only
through the selected writer. Earlier completion or equal payloads are not used
as substitutes for a read-from witness. Release-sequence cases use the existing
`ReleaseMember` relation instead of this direct-head specialization. -/
theorem Realizes.direct_synchronizes {initials : List (C23Atomic.Event Location Value)}
    {calls : List (Call Location Value)} {candidate : C23Atomic.Candidate Location Value}
    (history : Realizes initials calls candidate) (head reader : Fin calls.length)
    (release : calls[head.val].event.access.releases = true)
    (acquire : calls[reader.val].event.access.acquires = true)
    (source : C23Atomic.ReadsFrom candidate (initials.length + reader.val)
      (initials.length + head.val)) :
    C23Atomic.SynchronizesWith candidate (initials.length + head.val)
      (initials.length + reader.val) := by
  have releasing : C23Atomic.Releases candidate (initials.length + head.val) :=
    ⟨calls[head.val].event, history.call_at head, release⟩
  obtain ⟨object, value, _read, written⟩ := source.2
  exact ⟨⟨calls[reader.val].event, history.call_at reader, acquire⟩,
    initials.length + head.val, source, C23Atomic.releaseMember_self releasing written⟩

end EDSL.Concurrency.AtomicCalls
