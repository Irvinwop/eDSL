/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Concurrency.C23Atomic.Check.Table

/-!
Executable finite predicates for the supplied atomic event-graph semantics.
The equivalences require neither table shape nor candidate well-formedness.
Only the deciders for object/value comparisons require decidable equality;
the reflection theorems themselves do not.
-/

set_option autoImplicit false

namespace EDSL.Concurrency.C23Atomic.Check

variable {Location Value : Type}

/-- Both live events have an actual thread, and those thread identities agree. -/
def sameThread (t : Table Location Value) (i j : t.Index) : Prop :=
  match (t.node i).thread, (t.node j).thread with
  | some a, some b => a = b
  | _, _ => False

instance decidableSameThread (t : Table Location Value) (i j : t.Index) :
    Decidable (sameThread t i j) := by
  unfold sameThread
  cases (t.node i).thread <;> cases (t.node j).thread <;> infer_instance

/-- List order restricted to actual events of the same thread. -/
def seq (t : Table Location Value) (i j : t.Index) : Prop :=
  i.val < j.val ∧ sameThread t i j

instance decidableSeq (t : Table Location Value) (i j : t.Index) :
    Decidable (seq t i j) := by
  unfold seq
  infer_instance

/-- The selected writer ID must also agree with the reader's object and value.
The read must exist: equal absent options never constitute an RF edge. -/
def rf (t : Table Location Value) (reader writer : t.Index) : Prop :=
  t.source reader.val = some writer.val ∧
    (t.node reader).object = (t.node writer).object ∧
    (t.node reader).access.readValue.isSome = true ∧
    (t.node reader).access.readValue = (t.node writer).access.writeValue

instance decidableRF [DecidableEq Location] [DecidableEq Value]
    (t : Table Location Value) (reader writer : t.Index) :
    Decidable (rf t reader writer) := by
  unfold rf
  infer_instance

/-- All actual same-object writes strictly after the head through the member
must belong to the head's thread or be RMWs. Numeric rank gaps are allowed. -/
def releaseMember (t : Table Location Value) (head member : t.Index) : Prop :=
  (t.node head).access.releases = true ∧
    (t.node head).access.writeValue.isSome = true ∧
    (t.node member).access.writeValue.isSome = true ∧
    (t.node head).object = (t.node member).object ∧
    t.rank head.val ≤ t.rank member.val ∧
    ∀ k : t.Index, (t.node k).access.writeValue.isSome = true →
      (t.node k).object = (t.node head).object →
      t.rank head.val < t.rank k.val → t.rank k.val ≤ t.rank member.val →
      sameThread t head k ∨ (t.node k).access.isRMW = true

instance decidableReleaseMember [DecidableEq Location]
    (t : Table Location Value) (head member : t.Index) :
    Decidable (releaseMember t head member) := by
  unfold releaseMember
  infer_instance

/-- An acquire observes its selected writer in the head's release sequence. -/
def sync (t : Table Location Value) (head reader : t.Index) : Prop :=
  (t.node reader).access.acquires = true ∧
    ∃ writer : t.Index, rf t reader writer ∧ releaseMember t head writer

instance decidableSync [DecidableEq Location] [DecidableEq Value]
    (t : Table Location Value) (head reader : t.Index) :
    Decidable (sync t head reader) := by
  unfold sync
  infer_instance

theorem sameThread_iff (t : Table Location Value) (i j : t.Index) :
    SameThread t.toCandidate i.val j.val ↔ sameThread t i j := by
  constructor
  · rintro ⟨first, second, thread, firstLive, secondLive, firstThread, secondThread⟩
    unfold sameThread
    rw [t.node_of_lookup i firstLive, t.node_of_lookup j secondLive,
      firstThread, secondThread]
  · intro same
    cases firstThread : (t.node i).thread with
    | none => simp only [sameThread, firstThread] at same
    | some a =>
      cases secondThread : (t.node j).thread with
      | none => simp only [sameThread, firstThread, secondThread] at same
      | some b =>
        have equal : a = b := by
          simpa only [sameThread, firstThread, secondThread] using same
        exact ⟨t.node i, t.node j, a, t.node_lookup i, t.node_lookup j,
          firstThread, secondThread.trans (congrArg some equal.symm)⟩

theorem seq_iff (t : Table Location Value) (i j : t.Index) :
    SeqBefore t.toCandidate i.val j.val ↔ seq t i j := by
  constructor
  · rintro ⟨order, same⟩
    exact ⟨order, (sameThread_iff t i j).mp same⟩
  · rintro ⟨order, same⟩
    exact ⟨order, (sameThread_iff t i j).mpr same⟩

theorem isInitial_iff (t : Table Location Value) (i : t.Index) :
    IsInitial t.toCandidate i.val ↔ (t.node i).access.isInitial = true := by
  constructor
  · rintro ⟨event, live, initial⟩
    rw [t.node_of_lookup i live]
    exact initial
  · intro initial
    exact ⟨t.node i, t.node_lookup i, initial⟩

theorem isRMW_iff (t : Table Location Value) (i : t.Index) :
    IsRMW t.toCandidate i.val ↔ (t.node i).access.isRMW = true := by
  constructor
  · rintro ⟨event, live, rmw⟩
    rw [t.node_of_lookup i live]
    exact rmw
  · intro rmw
    exact ⟨t.node i, t.node_lookup i, rmw⟩

theorem releases_iff (t : Table Location Value) (i : t.Index) :
    Releases t.toCandidate i.val ↔ (t.node i).access.releases = true := by
  constructor
  · rintro ⟨event, live, release⟩
    rw [t.node_of_lookup i live]
    exact release
  · intro release
    exact ⟨t.node i, t.node_lookup i, release⟩

theorem acquires_iff (t : Table Location Value) (i : t.Index) :
    Acquires t.toCandidate i.val ↔ (t.node i).access.acquires = true := by
  constructor
  · rintro ⟨event, live, acquire⟩
    rw [t.node_of_lookup i live]
    exact acquire
  · intro acquire
    exact ⟨t.node i, t.node_lookup i, acquire⟩

theorem rf_iff (t : Table Location Value) (reader writer : t.Index) :
    ReadsFrom t.toCandidate reader.val writer.val ↔ rf t reader writer := by
  constructor
  · rintro ⟨selected, location, value, read, written⟩
    obtain ⟨readObject, readValue⟩ := (t.reads_iff reader location value).mp read
    obtain ⟨writeObject, writeValue⟩ := (t.writes_iff writer location value).mp written
    exact ⟨selected, readObject.trans writeObject.symm,
      Option.isSome_of_eq_some readValue, readValue.trans writeValue.symm⟩
  · rintro ⟨selected, sameObject, hasRead, sameValue⟩
    obtain ⟨value, readValue⟩ := Option.isSome_iff_exists.mp hasRead
    refine ⟨selected, (t.node reader).object, value, ?_, ?_⟩
    · exact (t.reads_iff reader (t.node reader).object value).mpr ⟨rfl, readValue⟩
    · exact (t.writes_iff writer (t.node reader).object value).mpr
        ⟨sameObject.symm, sameValue.symm.trans readValue⟩

theorem releaseMember_iff (t : Table Location Value) (head member : t.Index) :
    ReleaseMember t.toCandidate head.val member.val ↔ releaseMember t head member := by
  constructor
  · rintro ⟨release, location, headValue, memberValue, headWrite, memberWrite,
      ordered, contiguous⟩
    obtain ⟨headObject, headWritten⟩ := (t.writes_iff head location headValue).mp headWrite
    obtain ⟨memberObject, memberWritten⟩ :=
      (t.writes_iff member location memberValue).mp memberWrite
    refine ⟨(releases_iff t head).mp release, Option.isSome_of_eq_some headWritten,
      Option.isSome_of_eq_some memberWritten, headObject.trans memberObject.symm,
      ordered, ?_⟩
    intro k hasWrite sameObject aboveHead atMostMember
    obtain ⟨value, written⟩ := Option.isSome_iff_exists.mp hasWrite
    have actualWrite : Writes t.toCandidate k.val location value :=
      (t.writes_iff k location value).mpr ⟨sameObject.trans headObject, written⟩
    rcases contiguous k.val value actualWrite aboveHead atMostMember with same | rmw
    · exact Or.inl ((sameThread_iff t head k).mp same)
    · exact Or.inr ((isRMW_iff t k).mp rmw)
  · rintro ⟨release, headHasWrite, memberHasWrite, sameObject, ordered, contiguous⟩
    obtain ⟨headValue, headWritten⟩ := Option.isSome_iff_exists.mp headHasWrite
    obtain ⟨memberValue, memberWritten⟩ := Option.isSome_iff_exists.mp memberHasWrite
    refine ⟨(releases_iff t head).mpr release, (t.node head).object,
      headValue, memberValue,
      (t.writes_iff head (t.node head).object headValue).mpr ⟨rfl, headWritten⟩,
      (t.writes_iff member (t.node head).object memberValue).mpr
        ⟨sameObject.symm, memberWritten⟩,
      ordered, ?_⟩
    intro index value written aboveHead atMostMember
    let k : t.Index := ⟨index, t.writes_bound written⟩
    obtain ⟨object, stored⟩ := (t.writes_iff k (t.node head).object value).mp written
    rcases contiguous k (Option.isSome_of_eq_some stored) object aboveHead atMostMember
        with same | rmw
    · exact Or.inl ((sameThread_iff t head k).mpr same)
    · exact Or.inr ((isRMW_iff t k).mpr rmw)

theorem sync_iff (t : Table Location Value) (head reader : t.Index) :
    SynchronizesWith t.toCandidate head.val reader.val ↔ sync t head reader := by
  constructor
  · rintro ⟨acquire, writer, source, member⟩
    obtain ⟨_, _, _, written⟩ := source.2
    let actual : t.Index := ⟨writer, t.writes_bound written⟩
    exact ⟨(acquires_iff t reader).mp acquire, actual,
      (rf_iff t reader actual).mp source, (releaseMember_iff t head actual).mp member⟩
  · rintro ⟨acquire, writer, source, member⟩
    exact ⟨(acquires_iff t reader).mpr acquire, writer.val,
      (rf_iff t reader writer).mpr source, (releaseMember_iff t head writer).mpr member⟩

/-- Sequencing endpoints must each name a live event, without structural assumptions. -/
theorem seq_bound (t : Table Location Value) {i j : Nat}
    (edge : SeqBefore t.toCandidate i j) :
    i < t.events.length ∧ j < t.events.length := by
  obtain ⟨_, _, _, firstLive, secondLive, _, _⟩ := edge.2
  exact ⟨(List.getElem_of_getElem? firstLive).1, (List.getElem_of_getElem? secondLive).1⟩

/-- The release head and acquire reader are actual synchronization endpoints. -/
theorem sync_bound (t : Table Location Value) {i j : Nat}
    (edge : SynchronizesWith t.toCandidate i j) :
    i < t.events.length ∧ j < t.events.length := by
  obtain ⟨_, _, member⟩ := edge.2
  obtain ⟨_, headLive, _⟩ := member.1
  obtain ⟨_, readerLive, _⟩ := edge.1
  exact ⟨(List.getElem_of_getElem? headLive).1, (List.getElem_of_getElem? readerLive).1⟩

/-- Positive HB paths inherit their first and last actual event bounds. -/
theorem hb_bound (t : Table Location Value) {i j : Nat}
    (path : HappensBefore t.toCandidate i j) :
    i < t.events.length ∧ j < t.events.length := by
  induction path with
  | sequenced edge => exact seq_bound t edge
  | synchronizes edge => exact sync_bound t edge
  | trans _ _ ihFirst ihSecond => exact ⟨ihFirst.1, ihSecond.2⟩

/-- An actual RMW exposes both values on its event's own object. -/
theorem rmw_values (t : Table Location Value) (i : t.Index)
    (actual : IsRMW t.toCandidate i.val) :
    ∃ before after, Reads t.toCandidate i.val (t.node i).object before ∧
      Writes t.toCandidate i.val (t.node i).object after := by
  have values : ∀ access : Access Value, access.isRMW = true →
      ∃ before after, access.readValue = some before ∧ access.writeValue = some after := by
    intro access flag
    cases access with
    | «initialize» _ => cases flag
    | load _ _ => cases flag
    | store _ _ => cases flag
    | rmw _ before after => exact ⟨before, after, rfl, rfl⟩
  obtain ⟨before, after, read, written⟩ := values (t.node i).access
    ((isRMW_iff t i).mp actual)
  exact ⟨before, after,
    (t.reads_iff i (t.node i).object before).mpr ⟨rfl, read⟩,
    (t.writes_iff i (t.node i).object after).mpr ⟨rfl, written⟩⟩

end EDSL.Concurrency.C23Atomic.Check
