/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Concurrency.C23Atomic.Coherence
import EDSL.Audit

/-!
The four atomic coherence constraints along a specified event relation.
This separates reusable numerical constraints from the obligation to derive
which event pairs are related. In particular, sequencing alone is weaker than
the happens-before closure of sequencing and release/acquire synchronization.
-/

set_option autoImplicit false

namespace EDSL.Concurrency.C23Atomic

/-- Coherence constraints for exactly the supplied event pairs. No edge or
legality is inferred from a numerical ordering of modification ranks. -/
structure CoherentAlong {Location Value : Type} (c : Candidate Location Value)
    (order : Nat → Nat → Prop) : Prop where
  writeWrite : ∀ {first second : Nat} {location : Location} {a b : Value},
    Writes c first location a → Writes c second location b →
    order first second → c.rank first < c.rank second
  readRead : ∀ {first second left right : Nat} {location : Location} {a b : Value},
    Reads c first location a → Reads c second location b →
    ReadsFrom c first left → ReadsFrom c second right →
    order first second → c.rank left ≤ c.rank right
  readWrite : ∀ {reader observed writer : Nat} {location : Location} {a b : Value},
    Reads c reader location a → ReadsFrom c reader observed → Writes c writer location b →
    order reader writer → c.rank observed < c.rank writer
  writeRead : ∀ {writer reader observed : Nat} {location : Location} {a b : Value},
    Writes c writer location a → Reads c reader location b → ReadsFrom c reader observed →
    order writer reader → c.rank writer ≤ c.rank observed

variable {Location Value : Type} {c : Candidate Location Value}
  {order restricted : Nat → Nat → Prop}

/-- Restricting a relation preserves all four constraints. This does not
assert that coherence is closed under arbitrary edge composition. -/
theorem CoherentAlong.restrict (coherent : CoherentAlong c order)
    (included : ∀ {first second}, restricted first second → order first second) :
    CoherentAlong c restricted :=
  ⟨fun first second related => coherent.writeWrite first second (included related),
    fun first second left right related => coherent.readRead first second left right (included related),
    fun reader source writer related => coherent.readWrite reader source writer (included related),
    fun writer reader source related => coherent.writeRead writer reader source (included related)⟩

/-- The existing atomic-fragment coherence contract is recovered only when
all happens-before pairs have been discharged. -/
theorem CoherentAlong.happensBefore (coherent : CoherentAlong c (HappensBefore c)) :
    Coherent c :=
  ⟨coherent.writeWrite, coherent.readRead, coherent.readWrite, coherent.writeRead⟩

theorem Coherent.along (coherent : Coherent c) : CoherentAlong c (HappensBefore c) :=
  ⟨coherent.writeWrite, coherent.readRead, coherent.readWrite, coherent.writeRead⟩

/-- Program-order coherence includes RMWs in both read and write roles. It
says nothing about synchronization edges or their transitive HB consequences. -/
abbrev SequencedCoherent (c : Candidate Location Value) := CoherentAlong c (SeqBefore c)

/-- Full sequencing is transitive because every event has one thread label. -/
theorem SeqBefore.trans {first middle last : Nat}
    (left : SeqBefore c first middle) (right : SeqBefore c middle last) :
    SeqBefore c first last := by
  obtain ⟨firstNode, middleNode, thread, firstLive, middleLive, firstThread, middleThread⟩ := left.2
  obtain ⟨otherMiddle, lastNode, otherThread, otherLive, lastLive, otherMiddleThread, lastThread⟩ := right.2
  have sameNode := Option.some.inj (middleLive.symm.trans otherLive)
  subst otherMiddle
  have sameThread := Option.some.inj (middleThread.symm.trans otherMiddleThread)
  subst otherThread
  exact ⟨Nat.lt_trans left.1 right.1,
    firstNode, lastNode, thread, firstLive, lastLive, firstThread, lastThread⟩

/-- Without synchronization, every nonempty HB path is already a sequencing
edge. This is a relation theorem, not an inference from observed timestamps. -/
theorem HappensBefore.sequenced_of_no_synchronization
    (absent : ∀ first second, ¬ SynchronizesWith c first second)
    {first second : Nat} (path : HappensBefore c first second) : SeqBefore c first second := by
  induction path with
  | sequenced before => exact before
  | synchronizes edge => exact False.elim (absent _ _ edge)
  | trans _first _second earlier later => exact earlier.trans later

/-- The finite fragment's full legality contract follows from sequencing
constraints when the graph has no synchronization edges. RMW predecessor and
structural well-formedness remain explicit, separately discharged obligations. -/
theorem legal_of_no_synchronization (wellFormed : WellFormed c)
    (coherent : SequencedCoherent c)
    (absent : ∀ first second, ¬ SynchronizesWith c first second)
    (noFuture : ∀ {reader writer}, ReadsFrom c reader writer → ¬ SeqBefore c reader writer)
    (predecessor : ∀ {index writer}, IsRMW c index → ReadsFrom c index writer →
      ModBefore c writer index ∧ ∀ middle, ModBefore c writer middle → ¬ ModBefore c middle index) :
    Legal c := by
  have allHB : CoherentAlong c (HappensBefore c) :=
    coherent.restrict (fun path => path.sequenced_of_no_synchronization absent)
  refine ⟨wellFormed, allHB.happensBefore, ?_, ?_, predecessor⟩
  · intro index cycle
    exact Nat.lt_irrefl index (cycle.sequenced_of_no_synchronization absent).1
  · intro reader writer source future
    exact noFuture source (future.sequenced_of_no_synchronization absent)

end EDSL.Concurrency.C23Atomic

#audit_edsl
