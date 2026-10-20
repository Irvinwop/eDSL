/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.C23Projection.StoreTrace
import EDSL.Concurrency.C23Atomic.Check

set_option autoImplicit false

namespace EDSL.OS.TSO64.C23Projection.AtomicTrace
open X86

/-- Writer identities precede table indices. Values validate a chosen source;
they never identify it. Store occurrences belong to scheduler thread slots. -/
inductive WriterId where
  | initial (cell : Atomics64.CellId64)
  | store (tid occurrence : Nat)
  | rmw (position : Nat)
  deriving DecidableEq, Repr

/-- Unordered machine access data. Source memory orders are supplied separately
by a declared primitive/interface annotation, not inferred from MOV bytes. -/
inductive Access where
  | load (reference : Queue.ManagedRef) (value : Word) (source : WriterId)
  | store (reference : Queue.ManagedRef) (value : Word) (occurrence : Nat)
  | rmw (event : Atomics64.FetchAddEvent) (source : WriterId)
  deriving DecidableEq, Repr

structure Event where
  position : Nat
  tid : Nat
  access : Access
  deriving DecidableEq, Repr

def Event.object (event : Event) : Atomics64.CellId64 :=
  match event.access with
  | .load reference .. | .store reference .. => reference.handle.cell
  | .rmw changed _ => changed.cell

def Event.source (event : Event) : Option WriterId :=
  match event.access with
  | .load _ _ source | .rmw _ source => some source
  | .store .. => none

def Event.writer (event : Event) : Option WriterId :=
  match event.access with
  | .load .. => none
  | .store _ _ occurrence => some (.store event.tid occurrence)
  | .rmw .. => some (.rmw event.position)

/-- Interface orders are explicit inputs, indexed by scheduler thread and
original action position. This supplies no source syntax/control semantics. -/
structure Orders where
  read : Nat → Nat → Concurrency.C23Atomic.ReadOrder
  write : Nat → Nat → Concurrency.C23Atomic.WriteOrder
  rmw : Nat → Nat → Concurrency.C23Atomic.RMWOrder

def Event.toSource (event : Event) (orders : Orders) :
    Concurrency.C23Atomic.Event Atomics64.CellId64 Word :=
  ⟨some event.tid, event.object, match event.access with
    | .load _ value _ => .load (orders.read event.tid event.position) value
    | .store _ value _ => .store (orders.write event.tid event.position) value
    | .rmw changed _ => .rmw (orders.rmw event.tid event.position)
        changed.arithmetic.event.before changed.arithmetic.event.after⟩

/-- A machine trace result plus computed atomic events. Event provenance is
established by scanner theorems, not by constructing this data record. -/
structure Result where
  state : State
  observations : List Observation
  events : List Event

def Result.execution (result : Result) : State × List Observation :=
  (result.state, result.observations)

/-- Convert a current published-writer stamp to its instruction writer key.
A buffered stamp retains its original issue identity rather than its drain. -/
def publishedSource (writers : PublishedHistory.Writers) (cell : Atomics64.CellId64) : WriterId :=
  match writers cell with
  | none => .initial cell
  | some stamp => match stamp.cause with
    | .buffered tid _ _ occurrence => .store tid occurrence
    | .rmw .. => .rmw stamp.position

end EDSL.OS.TSO64.C23Projection.AtomicTrace
