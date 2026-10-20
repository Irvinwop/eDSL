/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import Init

/-!
Finite supplied atomic event graphs, fully sequenced within each thread, for
relaxed, acquire, release and
acquire/release operations. The primary reference is C23 draft N3096:
https://www.open-std.org/jtc1/sc22/wg14/www/docs/n3096.pdf
Sections 5.1.2.4p10-11 describe release sequences and synchronization; p18
describes happens-before. The separate legality layer must impose p23-32 and
the RMW predecessor requirement of 7.17.3p12.

Each list index names one event. Per-thread list order supplies sequencing;
explicit reader-to-writer indices supply RF; numeric ranks supply per-object
modification order. Rank gaps are allowed. Release-sequence membership checks
every actual intervening write, including writes that leave the value unchanged.
Initialization is a synthetic boundary write without a thread or release flag.
Interpreted objects are already validly initialized before the modeled interval;
object lifetimes and logical thread instances remain stable. This does not
execute atomic_init or supply initialization/creation/join happens-before.

`WellFormed` supplies structural conditions only. This fragment has no fences,
consume, sequential consistency, non-atomic accesses, data-race semantics,
value-computation dependencies, control flow, OS or scheduler semantics. It is
neither a GNU C source frontend nor a source/native/compiler mapping or corpus
claim. Clients supply the finite graph; this file does not establish its origin
or full C23 legality.
-/

set_option autoImplicit false

namespace EDSL.Concurrency.C23Atomic

inductive ReadOrder where
  | relaxed
  | acquire
  deriving DecidableEq, Repr

inductive WriteOrder where
  | relaxed
  | release
  deriving DecidableEq, Repr

inductive RMWOrder where
  | relaxed
  | acquire
  | release
  | acqRel
  deriving DecidableEq, Repr

/-- An RMW has one identity and exposes both its observed and its stored value. -/
inductive Access (Value : Type) where
  | «initialize» (value : Value)
  | load (order : ReadOrder) (value : Value)
  | store (order : WriteOrder) (value : Value)
  | rmw (order : RMWOrder) (before after : Value)
  deriving DecidableEq, Repr

namespace Access

variable {Value : Type}

def readValue : Access Value → Option Value
  | .load _ value => some value
  | .rmw _ before _ => some before
  | .initialize _ => none
  | .store _ _ => none

def writeValue : Access Value → Option Value
  | .initialize value => some value
  | .store _ value => some value
  | .rmw _ _ after => some after
  | .load _ _ => none

def isInitial : Access Value → Bool
  | .initialize _ => true
  | _ => false

def isRMW : Access Value → Bool
  | .rmw _ _ _ => true
  | _ => false

def acquires : Access Value → Bool
  | .load .acquire _ => true
  | .rmw .acquire _ _ => true
  | .rmw .acqRel _ _ => true
  | _ => false

def releases : Access Value → Bool
  | .store .release _ => true
  | .rmw .release _ _ => true
  | .rmw .acqRel _ _ => true
  | _ => false

end Access

structure Event (Location Value : Type) where
  thread : Option Nat
  object : Location
  access : Access Value
  deriving DecidableEq, Repr

/-- Only the finite list's live indices denote events. RF names an event, and
ranks order writes only when they concern the same object. -/
structure Candidate (Location Value : Type) where
  events : List (Event Location Value)
  readsFrom : Nat → Option Nat
  rank : Nat → Nat

variable {Location Value : Type}

def Reads (c : Candidate Location Value) (index : Nat) (location : Location)
    (value : Value) : Prop :=
  ∃ event, c.events[index]? = some event ∧ event.object = location ∧
    event.access.readValue = some value

def Writes (c : Candidate Location Value) (index : Nat) (location : Location)
    (value : Value) : Prop :=
  ∃ event, c.events[index]? = some event ∧ event.object = location ∧
    event.access.writeValue = some value

def SameThread (c : Candidate Location Value) (i j : Nat) : Prop :=
  ∃ first second thread, c.events[i]? = some first ∧
    c.events[j]? = some second ∧ first.thread = some thread ∧
    second.thread = some thread

def IsInitial (c : Candidate Location Value) (index : Nat) : Prop :=
  ∃ event, c.events[index]? = some event ∧ event.access.isInitial = true

def IsRMW (c : Candidate Location Value) (index : Nat) : Prop :=
  ∃ event, c.events[index]? = some event ∧ event.access.isRMW = true

def Releases (c : Candidate Location Value) (index : Nat) : Prop :=
  ∃ event, c.events[index]? = some event ∧ event.access.releases = true

def Acquires (c : Candidate Location Value) (index : Nat) : Prop :=
  ∃ event, c.events[index]? = some event ∧ event.access.acquires = true

def SeqBefore (c : Candidate Location Value) (i j : Nat) : Prop :=
  i < j ∧ SameThread c i j

def ModBefore (c : Candidate Location Value) (i j : Nat) : Prop :=
  ∃ location before after, Writes c i location before ∧
    Writes c j location after ∧ c.rank i < c.rank j

/-- Value agreement validates the selected edge; it never selects a writer. -/
def ReadsFrom (c : Candidate Location Value) (reader writer : Nat) : Prop :=
  c.readsFrom reader = some writer ∧
    ∃ location value, Reads c reader location value ∧ Writes c writer location value

/-- C23 5.1.2.4p10: the head itself and the maximal contiguous prefix of
same-thread writes or arbitrary-thread RMWs. All intervening writes are checked,
including the member when it strictly follows the head. -/
def ReleaseMember (c : Candidate Location Value) (head member : Nat) : Prop :=
  Releases c head ∧
    ∃ location headValue memberValue, Writes c head location headValue ∧
      Writes c member location memberValue ∧ c.rank head ≤ c.rank member ∧
      (∀ index value, Writes c index location value →
        c.rank head < c.rank index → c.rank index ≤ c.rank member →
        SameThread c head index ∨ IsRMW c index)

/-- C23 5.1.2.4p11 within this fragment. The acquire must observe the actual
selected writer in the release sequence. No thread-inequality premise is added. -/
def SynchronizesWith (c : Candidate Location Value) (head reader : Nat) : Prop :=
  Acquires c reader ∧
    ∃ writer, ReadsFrom c reader writer ∧ ReleaseMember c head writer

/-- The transitive closure of sequencing and synchronization, with no zero-edge
constructor. Absence of cycles is a separate legality condition. -/
inductive HappensBefore (c : Candidate Location Value) : Nat → Nat → Prop where
  | sequenced {i j : Nat} (order : SeqBefore c i j) : HappensBefore c i j
  | synchronizes {i j : Nat} (edge : SynchronizesWith c i j) : HappensBefore c i j
  | trans {i j k : Nat} (first : HappensBefore c i j)
      (second : HappensBefore c j k) : HappensBefore c i k

/-- Structural obligations for the explicit graph. They do not impose
no-future-RF, happens-before acyclicity, coherence or RMW predecessor legality. -/
structure WellFormed (c : Candidate Location Value) : Prop where
  threadKind : ∀ (index : Nat) (event : Event Location Value), c.events[index]? = some event →
    (event.thread = none ↔ event.access.isInitial = true)
  initialUnique : ∀ i j location before after,
    Writes c i location before → Writes c j location after →
    IsInitial c i → IsInitial c j → i = j
  initialExists : ∀ (index : Nat) (event : Event Location Value), c.events[index]? = some event →
    ∃ initial value, Writes c initial event.object value ∧ IsInitial c initial
  initialRank : ∀ index location value, Writes c index location value →
    (IsInitial c index → c.rank index = 0) ∧
    (¬ IsInitial c index → 0 < c.rank index)
  rankUnique : ∀ i j location before after,
    Writes c i location before → Writes c j location after →
    c.rank i = c.rank j → i = j
  readsSource : ∀ reader location value, Reads c reader location value →
    ∃ writer, ReadsFrom c reader writer
  noReadSource : ∀ index, (∀ location value, ¬ Reads c index location value) →
    c.readsFrom index = none

/-- An index fixes both the read's object and its value. -/
theorem reads_unique {c : Candidate Location Value} {index : Nat}
    {leftLocation rightLocation : Location} {leftValue rightValue : Value}
    (left : Reads c index leftLocation leftValue)
    (right : Reads c index rightLocation rightValue) :
    leftLocation = rightLocation ∧ leftValue = rightValue := by
  rcases left with ⟨first, firstLive, firstObject, firstRead⟩
  rcases right with ⟨second, secondLive, secondObject, secondRead⟩
  have same : first = second := Option.some.inj (firstLive.symm.trans secondLive)
  subst second
  exact ⟨firstObject.symm.trans secondObject,
    Option.some.inj (firstRead.symm.trans secondRead)⟩

/-- Equal values do not identify distinct writes; this requires the same index. -/
theorem writes_unique {c : Candidate Location Value} {index : Nat}
    {leftLocation rightLocation : Location} {leftValue rightValue : Value}
    (left : Writes c index leftLocation leftValue)
    (right : Writes c index rightLocation rightValue) :
    leftLocation = rightLocation ∧ leftValue = rightValue := by
  rcases left with ⟨first, firstLive, firstObject, firstWrite⟩
  rcases right with ⟨second, secondLive, secondObject, secondWrite⟩
  have same : first = second := Option.some.inj (firstLive.symm.trans secondLive)
  subst second
  exact ⟨firstObject.symm.trans secondObject,
    Option.some.inj (firstWrite.symm.trans secondWrite)⟩

/-- A reader has only its explicitly selected writer, even among equal values. -/
theorem readsFrom_unique {c : Candidate Location Value} {reader left right : Nat}
    (first : ReadsFrom c reader left) (second : ReadsFrom c reader right) :
    left = right :=
  Option.some.inj (first.1.symm.trans second.1)

/-- Agreement of objects and values cannot override a different selected ID. -/
theorem not_readsFrom_of_ne {c : Candidate Location Value} {reader selected other : Nat}
    (source : ReadsFrom c reader selected) (different : selected ≠ other) :
    ¬ ReadsFrom c reader other := by
  intro alternative
  exact different (readsFrom_unique source alternative)

/-- Every actual release write heads its own sequence, without any later member. -/
theorem releaseMember_self {c : Candidate Location Value} {head : Nat}
    {location : Location} {value : Value}
    (release : Releases c head) (written : Writes c head location value) :
    ReleaseMember c head head := by
  refine ⟨release, location, value, value, written, written, Nat.le_refl _, ?_⟩
  intro index _ _ aboveHead atMostHead
  exact False.elim (Nat.lt_irrefl (c.rank head)
    (Nat.lt_of_lt_of_le aboveHead atMostHead))

/-- Prefix closure includes the head rank. The actual prefix write must be on
the head's object, at or after the head and at or before the known member. -/
theorem releaseMember_prefix {c : Candidate Location Value} {head member through : Nat}
    {location : Location} {headValue prefixValue : Value}
    (membership : ReleaseMember c head member)
    (headWrite : Writes c head location headValue)
    (prefixWrite : Writes c through location prefixValue)
    (lower : c.rank head ≤ c.rank through) (upper : c.rank through ≤ c.rank member) :
    ReleaseMember c head through := by
  rcases membership with ⟨release, sequenceObject, _, _, firstWrite, _, _, contiguous⟩
  have sameObject : sequenceObject = location := (writes_unique firstWrite headWrite).1
  subst sequenceObject
  refine ⟨release, location, headValue, prefixValue, headWrite, prefixWrite, lower, ?_⟩
  intro index value written aboveHead atMostPrefix
  exact contiguous index value written aboveHead (Nat.le_trans atMostPrefix upper)

/-- A foreign plain write anywhere after the head through the proposed member
breaks the sequence, regardless of the values written by any of these events. -/
theorem foreign_plain_breaks {c : Candidate Location Value} {head member index : Nat}
    {location : Location} {headValue value : Value}
    (headWrite : Writes c head location headValue)
    (interveningWrite : Writes c index location value)
    (afterHead : c.rank head < c.rank index) (atMostMember : c.rank index ≤ c.rank member)
    (otherThread : ¬ SameThread c head index) (plain : ¬ IsRMW c index) :
    ¬ ReleaseMember c head member := by
  intro membership
  rcases membership with ⟨_, sequenceObject, _, _, firstWrite, _, _, contiguous⟩
  have sameObject : sequenceObject = location := (writes_unique firstWrite headWrite).1
  subst sequenceObject
  rcases contiguous index value interveningWrite afterHead atMostMember with same | rmw
  · exact otherThread same
  · exact plain rmw

theorem not_synchronizesWith_of_not_acquires {c : Candidate Location Value}
    {head reader : Nat} (notAcquire : ¬ Acquires c reader) :
    ¬ SynchronizesWith c head reader := by
  intro synchronization
  exact notAcquire synchronization.1

/-- A relaxed load cannot acquire merely by selecting a release-sequence write. -/
theorem relaxed_load_not_acquires {c : Candidate Location Value} {reader : Nat}
    {event : Event Location Value} {value : Value}
    (live : c.events[reader]? = some event)
    (relaxed : event.access = .load .relaxed value) : ¬ Acquires c reader := by
  intro acquire
  rcases acquire with ⟨actual, actualLive, acquired⟩
  have same : actual = event := Option.some.inj (actualLive.symm.trans live)
  subst actual
  rw [relaxed] at acquired
  cases acquired

theorem relaxed_load_not_synchronizesWith {c : Candidate Location Value}
    {head reader : Nat} {event : Event Location Value} {value : Value}
    (live : c.events[reader]? = some event)
    (relaxed : event.access = .load .relaxed value) :
    ¬ SynchronizesWith c head reader :=
  not_synchronizesWith_of_not_acquires (relaxed_load_not_acquires live relaxed)

end EDSL.Concurrency.C23Atomic
