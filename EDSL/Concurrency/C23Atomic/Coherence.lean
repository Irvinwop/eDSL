/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Concurrency.C23Atomic.Model

/-!
Consistency obligations for the finite atomic-only relaxed/acquire/release
fragment. The four coherence conditions follow N3096 §5.1.2.4 paragraphs 25–32.
Read-from identifies an actual modification, rather than merely an equal value.
RMWs additionally read the immediately preceding modification (§7.17.3).

This module neither maps a machine trace to a source execution nor supplies
non-atomic, consume, fence, sequential-consistency or full C semantics. A legal
candidate is a witness for this fragment, not a compiler-correctness theorem.
Program consistency and value/control-dependency obligations require a separate
source semantics or mapping.
-/

set_option autoImplicit false

namespace EDSL.Concurrency.C23Atomic
variable {Location Value : Type} {c : Candidate Location Value}

/-- The source's four atomic coherence requirements. RMWs participate in both
the read and write predicates, so they receive the same coherence obligations. -/
structure Coherent (c : Candidate Location Value) : Prop where
  writeWrite : ∀ {first second : Nat} {location : Location} {a b : Value},
    Writes c first location a → Writes c second location b →
    HappensBefore c first second → c.rank first < c.rank second
  readRead : ∀ {first second left right : Nat} {location : Location} {a b : Value},
    Reads c first location a → Reads c second location b →
    ReadsFrom c first left → ReadsFrom c second right →
    HappensBefore c first second → c.rank left ≤ c.rank right
  readWrite : ∀ {reader observed writer : Nat} {location : Location} {a b : Value},
    Reads c reader location a → ReadsFrom c reader observed → Writes c writer location b →
    HappensBefore c reader writer → c.rank observed < c.rank writer
  writeRead : ∀ {writer reader observed : Nat} {location : Location} {a b : Value},
    Writes c writer location a → Reads c reader location b → ReadsFrom c reader observed →
    HappensBefore c writer reader → c.rank writer ≤ c.rank observed

/-- Legal finite candidates must discharge every condition. In particular,
matching values and an acyclic happens-before relation alone do not suffice. -/
structure Legal (c : Candidate Location Value) : Prop where
  wellFormed : WellFormed c
  coherent : Coherent c
  acyclic : ∀ index, ¬ HappensBefore c index index
  noFutureRead : ∀ {reader writer}, ReadsFrom c reader writer →
    ¬ HappensBefore c reader writer
  rmwPredecessor : ∀ {index writer}, IsRMW c index → ReadsFrom c index writer →
    ModBefore c writer index ∧
      ∀ middle, ModBefore c writer middle → ¬ ModBefore c middle index

/-- A given read event has one object and one observed value, independently
of how a client names the read or its selected source modification. -/
theorem Reads.unique {index : Nat} {first second : Location} {a b : Value}
    (left : Reads c index first a) (right : Reads c index second b) :
    first = second ∧ a = b := by
  exact reads_unique left right

/-- A source modification has one written value; equal values do not imply
that two distinct modifications have the same identity. -/
theorem Writes.unique {index : Nat} {first second : Location} {a b : Value}
    (left : Writes c index first a) (right : Writes c index second b) :
    first = second ∧ a = b := by
  exact writes_unique left right

/-- Read-from retains the selected writer and the actual read object's value. -/
theorem ReadsFrom.source {reader writer : Nat} {location : Location} {value : Value}
    (source : ReadsFrom c reader writer) (read : Reads c reader location value) :
    Writes c writer location value := by
  obtain ⟨_, object, observed, actualRead, actualWrite⟩ := source
  obtain ⟨sameObject, sameValue⟩ := Reads.unique actualRead read
  cases sameObject
  cases sameValue
  exact actualWrite

/-- A checked timestamp certificate for the two generating edges orders every
happens-before path. The clock is an untrusted witness: both edge obligations
remain proofs, and no clock ordering is promoted to an extra HB edge. -/
theorem HappensBefore.clock_lt {clock : Nat → Nat}
    (sequenced : ∀ {i j}, SeqBefore c i j → clock i < clock j)
    (synchronized : ∀ {i j}, SynchronizesWith c i j → clock i < clock j)
    {i j : Nat} (path : HappensBefore c i j) : clock i < clock j := by
  induction path with
  | sequenced edge => exact sequenced edge
  | synchronizes edge => exact synchronized edge
  | trans first second ihFirst ihSecond => exact Nat.lt_trans ihFirst ihSecond

/-- No happens-before cycle can pass a strictly increasing clock certificate. -/
theorem acyclic_of_clock {clock : Nat → Nat}
    (sequenced : ∀ {i j}, SeqBefore c i j → clock i < clock j)
    (synchronized : ∀ {i j}, SynchronizesWith c i j → clock i < clock j) :
    ∀ index, ¬ HappensBefore c index index := by
  intro index cycle
  exact Nat.lt_irrefl (clock index) (cycle.clock_lt sequenced synchronized)

/-- The synchronization edge transports every earlier source event through a
qualifying acquire to its later events. It requires the actual selected writer
in the release sequence, and works for direct reads and transitive sequences. -/
theorem publication_chain {before head reader after writer : Nat}
    (beforeRelease : SeqBefore c before head)
    (acquire : Acquires c reader) (source : ReadsFrom c reader writer)
    (member : ReleaseMember c head writer)
    (afterAcquire : SeqBefore c reader after) : HappensBefore c before after := by
  have synchronizes : SynchronizesWith c head reader := ⟨acquire, writer, source, member⟩
  exact .trans (.sequenced beforeRelease)
    (.trans (.synchronizes synchronizes) (.sequenced afterAcquire))

/-- Message passing cannot read an older payload modification after a qualifying
release/acquire chain. This theorem is independent of the machine program,
instruction sequence, payload value and chosen event identities. -/
theorem Legal.message_passing_not_older (legal : Legal c)
    {payloadWrite head flagRead payloadRead flagWriter payloadSource : Nat}
    {location : Location} {written observed : Value}
    (payload : Writes c payloadWrite location written)
    (beforeRelease : SeqBefore c payloadWrite head)
    (acquire : Acquires c flagRead) (flagSource : ReadsFrom c flagRead flagWriter)
    (member : ReleaseMember c head flagWriter)
    (afterAcquire : SeqBefore c flagRead payloadRead)
    (read : Reads c payloadRead location observed)
    (source : ReadsFrom c payloadRead payloadSource) :
    c.rank payloadWrite ≤ c.rank payloadSource :=
  legal.coherent.writeRead payload read source
    (publication_chain beforeRelease acquire flagSource member afterAcquire)

/-- With no later payload modification, the same generic publication chain
forces the payload's actual value. Maximality constrains writes to that object;
it does not assume the load's result or select a writer by equal bits. -/
theorem Legal.message_passing_value (legal : Legal c)
    {payloadWrite head flagRead payloadRead flagWriter payloadSource : Nat}
    {location : Location} {written observed : Value}
    (payload : Writes c payloadWrite location written)
    (lastWrite : ∀ index value, Writes c index location value →
      ¬ ModBefore c payloadWrite index)
    (beforeRelease : SeqBefore c payloadWrite head)
    (acquire : Acquires c flagRead) (flagSource : ReadsFrom c flagRead flagWriter)
    (member : ReleaseMember c head flagWriter)
    (afterAcquire : SeqBefore c flagRead payloadRead)
    (read : Reads c payloadRead location observed)
    (source : ReadsFrom c payloadRead payloadSource) : observed = written := by
  have current := source.source read
  have lower := legal.message_passing_not_older payload beforeRelease acquire flagSource
    member afterAcquire read source
  have noLater := lastWrite payloadSource observed current
  have upper : c.rank payloadSource ≤ c.rank payloadWrite := by
    apply Nat.le_of_not_lt
    intro later
    exact noLater ⟨location, written, observed, payload, current, later⟩
  have equalRank := Nat.le_antisymm lower upper
  have identity := legal.wellFormed.rankUnique _ _ _ _ _ payload current equalRank
  subst payloadSource
  exact (Writes.unique current payload).2

end EDSL.Concurrency.C23Atomic
