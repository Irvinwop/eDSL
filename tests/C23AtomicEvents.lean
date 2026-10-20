/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Concurrency.C23Atomic.Coherence
import tests.C23MessagePassing
import EDSL.Audit

/-!
Independent finite atomic-event regressions for the N3096 fragment.

`direct_legal` supplies an actual nonempty legal candidate, including every
structural and coherence obligation. The subsequent candidates test the
synchronization relation only: equal values do not replace writer identities,
C23 permits a head-thread plain write after a foreign RMW, and a foreign plain
write breaks the sequence even when a later RMW writes the same value.

These are synthetic atomic-only graphs. They make no whole-C, native execution,
source/machine correspondence, compiler preservation or corpus claim.
-/

set_option autoImplicit false

namespace EDSL.Tests.C23AtomicEvents
open EDSL.Concurrency.C23Atomic

private theorem lookup_three {α : Type} {a b d event : α} {index : Nat}
    (live : [a, b, d][index]? = some event) :
    (index = 0 ∧ event = a) ∨ (index = 1 ∧ event = b) ∨
      (index = 2 ∧ event = d) := by
  have bound : index < 3 := by
    simpa using (List.getElem?_eq_some_iff.mp live).1
  have positions : index = 0 ∨ index = 1 ∨ index = 2 := by omega
  rcases positions with rfl | rfl | rfl
  · exact Or.inl ⟨rfl, (Option.some.inj live).symm⟩
  · exact Or.inr (Or.inl ⟨rfl, (Option.some.inj live).symm⟩)
  · exact Or.inr (Or.inr ⟨rfl, (Option.some.inj live).symm⟩)

private theorem lookup_five {α : Type} {a b d e f event : α} {index : Nat}
    (live : [a, b, d, e, f][index]? = some event) :
    (index = 0 ∧ event = a) ∨ (index = 1 ∧ event = b) ∨
      (index = 2 ∧ event = d) ∨ (index = 3 ∧ event = e) ∨
      (index = 4 ∧ event = f) := by
  have bound : index < 5 := by
    simpa using (List.getElem?_eq_some_iff.mp live).1
  have positions : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 := by
    omega
  rcases positions with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl ⟨rfl, (Option.some.inj live).symm⟩
  · exact Or.inr (Or.inl ⟨rfl, (Option.some.inj live).symm⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, (Option.some.inj live).symm⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, (Option.some.inj live).symm⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, (Option.some.inj live).symm⟩)))

private def initial0 : Event Nat Nat := ⟨none, 0, .initialize 0⟩
private def release7 : Event Nat Nat := ⟨some 11, 0, .store .release 7⟩
private def directAcquire7 : Event Nat Nat := ⟨some 12, 0, .load .acquire 7⟩

/-- One release observed by a different thread's acquire, with an explicit
initial boundary. Event indices and modification ranks are separate fields. -/
def direct : Candidate Nat Nat where
  events := [initial0, release7, directAcquire7]
  readsFrom index := if index = 2 then some 1 else none
  rank index := index

private theorem direct_lookup {index : Nat} {event : Event Nat Nat}
    (live : direct.events[index]? = some event) :
    (index = 0 ∧ event = initial0) ∨ (index = 1 ∧ event = release7) ∨
      (index = 2 ∧ event = directAcquire7) :=
  lookup_three (a := initial0) (b := release7) (d := directAcquire7) live

private theorem direct_reads {index location value : Nat} :
    Reads direct index location value ↔ index = 2 ∧ location = 0 ∧ value = 7 := by
  constructor
  · rintro ⟨event, live, object, observed⟩
    rcases direct_lookup live with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases observed
    · cases observed
    · exact ⟨rfl, object.symm, (Option.some.inj observed).symm⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨directAcquire7, rfl, rfl, rfl⟩

private theorem direct_writes {index location value : Nat} :
    Writes direct index location value ↔
      location = 0 ∧ ((index = 0 ∧ value = 0) ∨ (index = 1 ∧ value = 7)) := by
  constructor
  · rintro ⟨event, live, object, written⟩
    rcases direct_lookup live with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨object.symm, Or.inl ⟨rfl, (Option.some.inj written).symm⟩⟩
    · exact ⟨object.symm, Or.inr ⟨rfl, (Option.some.inj written).symm⟩⟩
    · cases written
  · rintro ⟨rfl, positions⟩
    rcases positions with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨initial0, rfl, rfl, rfl⟩
    · exact ⟨release7, rfl, rfl, rfl⟩

private theorem direct_initial {index : Nat} : IsInitial direct index ↔ index = 0 := by
  constructor
  · rintro ⟨event, live, initial⟩
    rcases direct_lookup live with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · cases initial
    · cases initial
  · rintro rfl
    exact ⟨initial0, rfl, rfl⟩

private theorem direct_releases {index : Nat} : Releases direct index ↔ index = 1 := by
  constructor
  · rintro ⟨event, live, release⟩
    rcases direct_lookup live with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases release
    · rfl
    · cases release
  · rintro rfl
    exact ⟨release7, rfl, rfl⟩

private theorem direct_rf {reader writer : Nat} :
    ReadsFrom direct reader writer ↔ reader = 2 ∧ writer = 1 := by
  constructor
  · intro source
    by_cases selected : reader = 2
    · subst reader
      exact ⟨rfl, (Option.some.inj source.1).symm⟩
    · have chosen : (if reader = 2 then some 1 else none) = some writer := source.1
      rw [ite_eq_right selected] at chosen
      cases chosen
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, 0, 7, ⟨directAcquire7, rfl, rfl, rfl⟩,
      ⟨release7, rfl, rfl, rfl⟩⟩

private theorem direct_no_rmw {index : Nat} : ¬ IsRMW direct index := by
  rintro ⟨event, live, rmw⟩
  rcases direct_lookup live with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · cases rmw
  · cases rmw
  · cases rmw

private theorem direct_no_sequencing {first second : Nat} :
    ¬ SeqBefore direct first second := by
  rintro ⟨earlier, left, right, thread, leftAt, rightAt, leftThread, rightThread⟩
  rcases direct_lookup leftAt with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · cases leftThread
  · rcases direct_lookup rightAt with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases rightThread
    · exact Nat.lt_irrefl 1 earlier
    · have leftId : 11 = thread := Option.some.inj leftThread
      have rightId : 12 = thread := Option.some.inj rightThread
      omega
  · rcases direct_lookup rightAt with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases rightThread
    · have leftId : 12 = thread := Option.some.inj leftThread
      have rightId : 11 = thread := Option.some.inj rightThread
      omega
    · exact Nat.lt_irrefl 2 earlier

private theorem direct_synchronizes : SynchronizesWith direct 1 2 := by
  refine ⟨⟨directAcquire7, rfl, rfl⟩, 1, direct_rf.mpr ⟨rfl, rfl⟩, ?_⟩
  exact releaseMember_self ⟨release7, rfl, rfl⟩ ⟨release7, rfl, rfl, rfl⟩

private theorem direct_sync_ends {head reader : Nat}
    (edge : SynchronizesWith direct head reader) : head = 1 ∧ reader = 2 := by
  obtain ⟨_, writer, source, member⟩ := edge
  exact ⟨direct_releases.mp member.1, (direct_rf.mp source).1⟩

/-- The complete nonreflexive HB relation, rather than just one assigned edge.
In particular the initialization is not implicitly assigned a thread. -/
theorem direct_happens_before {first second : Nat} :
    HappensBefore direct first second ↔ first = 1 ∧ second = 2 := by
  constructor
  · intro ordered
    induction ordered with
    | sequenced edge => exact False.elim (direct_no_sequencing edge)
    | synchronizes edge => exact direct_sync_ends edge
    | trans _ _ left right =>
      obtain ⟨_, leftEnd⟩ := left
      obtain ⟨rightStart, _⟩ := right
      omega
  · rintro ⟨rfl, rfl⟩
    exact .synchronizes direct_synchronizes

theorem direct_wellFormed : WellFormed direct where
  threadKind := by
    intro index event live
    rcases direct_lookup live with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    <;> decide
  initialUnique := by
    intro i j _ _ _ _ _ left right
    exact (direct_initial.mp left).trans (direct_initial.mp right).symm
  initialExists := by
    intro index event live
    rcases direct_lookup live with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    <;> exact ⟨0, 0, ⟨initial0, rfl, rfl, rfl⟩, ⟨initial0, rfl, rfl⟩⟩
  initialRank := by
    intro index location value written
    obtain ⟨_, positions⟩ := direct_writes.mp written
    rcases positions with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · constructor
      · intro _
        rfl
      · intro notInitial
        exact False.elim (notInitial ⟨initial0, rfl, rfl⟩)
    · constructor
      · intro initial
        have impossible := direct_initial.mp initial
        cases impossible
      · intro _
        exact Nat.zero_lt_succ 0
  rankUnique := by
    intro i j _ _ _ _ _ sameRank
    exact sameRank
  readsSource := by
    intro reader location value read
    exact ⟨1, direct_rf.mpr ⟨(direct_reads.mp read).1, rfl⟩⟩
  noReadSource := by
    intro index noRead
    by_cases isReader : index = 2
    · subst index
      exact False.elim (noRead 0 7 (direct_reads.mpr ⟨rfl, rfl, rfl⟩))
    · change (if index = 2 then some 1 else none) = none
      exact ite_eq_right isReader

private theorem direct_coherent : Coherent direct where
  writeWrite := by
    intro first second location a b _ written ordered
    obtain ⟨rfl, rfl⟩ := direct_happens_before.mp ordered
    have impossible := direct_writes.mp written
    simp at impossible
  readRead := by
    intro first second left right location a b read _ _ _ ordered
    have readerIndex := (direct_reads.mp read).1
    have endpoints := direct_happens_before.mp ordered
    omega
  readWrite := by
    intro reader observed writer location a b read _ _ ordered
    have readerIndex := (direct_reads.mp read).1
    have endpoints := direct_happens_before.mp ordered
    omega
  writeRead := by
    intro writer reader observed location a b _ _ source ordered
    obtain ⟨rfl, rfl⟩ := direct_happens_before.mp ordered
    obtain ⟨_, rfl⟩ := direct_rf.mp source
    exact Nat.le_refl _

/-- A constructive witness for every legality field; legality is not a premise.
The write/read coherence field has the actual release-to-acquire HB edge. -/
theorem direct_legal : Legal direct where
  wellFormed := direct_wellFormed
  coherent := direct_coherent
  acyclic := by
    intro index ordered
    have endpoints := direct_happens_before.mp ordered
    omega
  noFutureRead := by
    intro reader writer source future
    have selected := direct_rf.mp source
    have endpoints := direct_happens_before.mp future
    omega
  rmwPredecessor := by
    intro index writer rmw _
    exact False.elim (direct_no_rmw rmw)

theorem direct_nonempty :
    Legal direct ∧ HappensBefore direct 1 2 ∧ ReadsFrom direct 2 1 :=
  ⟨direct_legal, direct_happens_before.mpr ⟨rfl, rfl⟩, direct_rf.mpr ⟨rfl, rfl⟩⟩

private def foreignPlain7 : Event Nat Nat := ⟨some 12, 0, .store .relaxed 7⟩
private def foreignRmw7 : Event Nat Nat := ⟨some 12, 0, .rmw .relaxed 7 7⟩
private def sameThreadPlain7 : Event Nat Nat := ⟨some 11, 0, .store .relaxed 7⟩
private def sameThreadRmw7 : Event Nat Nat := ⟨some 11, 0, .rmw .relaxed 7 7⟩
private def observer7 : Event Nat Nat := ⟨some 13, 0, .load .acquire 7⟩

private theorem distinct_threads {c : Candidate Nat Nat} {i j : Nat}
    {left right : Event Nat Nat}
    (leftAt : c.events[i]? = some left) (rightAt : c.events[j]? = some right)
    (different : left.thread ≠ right.thread) : ¬ SameThread c i j := by
  rintro ⟨first, second, thread, firstAt, secondAt, firstThread, secondThread⟩
  have sameLeft : first = left := Option.some.inj (firstAt.symm.trans leftAt)
  have sameRight : second = right := Option.some.inj (secondAt.symm.trans rightAt)
  subst first
  subst second
  exact different (firstThread.trans secondThread.symm)

private theorem plain_at {c : Candidate Nat Nat} {index : Nat} {event : Event Nat Nat}
    (live : c.events[index]? = some event) (plain : event.access.isRMW = false) :
    ¬ IsRMW c index := by
  rintro ⟨actual, actualAt, rmw⟩
  have same : actual = event := Option.some.inj (actualAt.symm.trans live)
  subst actual
  rw [plain] at rmw
  cases rmw

/-- Both potential writers store 7. Only the explicit RF field changes between
the two relation regressions; the foreign plain store remains in MO in both. -/
def equalBits (selected : Nat) : Candidate Nat Nat where
  events := [initial0, release7, foreignPlain7, observer7]
  readsFrom index := if index = 3 then some selected else none
  rank index := index

theorem equal_bits_release_source_sync : SynchronizesWith (equalBits 1) 1 3 := by
  refine ⟨⟨observer7, rfl, rfl⟩, 1, ?_, ?_⟩
  · exact ⟨rfl, 0, 7, ⟨observer7, rfl, rfl, rfl⟩, ⟨release7, rfl, rfl, rfl⟩⟩
  · exact releaseMember_self ⟨release7, rfl, rfl⟩ ⟨release7, rfl, rfl, rfl⟩

/-- Observing the equal-valued foreign store cannot acquire from event 1.
The failed membership includes the selected store as an interval endpoint. -/
theorem equal_bits_foreign_source_no_sync : ¬ SynchronizesWith (equalBits 2) 1 3 := by
  rintro ⟨_, writer, source, member⟩
  have selected : writer = 2 := (Option.some.inj source.1).symm
  subst writer
  have broken : ¬ ReleaseMember (equalBits 2) 1 2 := by
    apply foreign_plain_breaks
      (headWrite := (show Writes (equalBits 2) 1 0 7 from ⟨release7, rfl, rfl, rfl⟩))
      (interveningWrite :=
        (show Writes (equalBits 2) 2 0 7 from ⟨foreignPlain7, rfl, rfl, rfl⟩))
      (afterHead := by decide) (atMostMember := by decide)
    · exact distinct_threads (c := equalBits 2) (i := 1) (j := 2)
        (left := release7) (right := foreignPlain7) rfl rfl (by decide)
    · exact plain_at (c := equalBits 2) (index := 2) (event := foreignPlain7) rfl rfl
  exact broken member

/-- Both equal-valued writers really can be read. Selecting event 2 precludes
RF from event 1 and its synchronization edge, despite the same observed 7. -/
theorem equal_bits_choose_identity :
    ReadsFrom (equalBits 2) 3 2 ∧ ¬ ReadsFrom (equalBits 2) 3 1 ∧
      SynchronizesWith (equalBits 1) 1 3 ∧ ¬ SynchronizesWith (equalBits 2) 1 3 := by
  have actual : ReadsFrom (equalBits 2) 3 2 :=
    ⟨rfl, 0, 7, ⟨observer7, rfl, rfl, rfl⟩, ⟨foreignPlain7, rfl, rfl, rfl⟩⟩
  exact ⟨actual, not_readsFrom_of_ne actual (by decide),
    equal_bits_release_source_sync, equal_bits_foreign_source_no_sync⟩

/-- The head-thread plain write follows an RMW by a foreign thread. The head
and its two successors all write 7, so value changes cannot stand in for
checking release-sequence membership. -/
def continued : Candidate Nat Nat where
  events := [initial0, release7, foreignRmw7, sameThreadPlain7, observer7]
  readsFrom index := if index = 2 then some 1 else if index = 4 then some 3 else none
  rank index := index

/-- The quantified interval contains a foreign RMW and then a plain write by
the head's thread. Both must be admitted by the C23 release-sequence rule. -/
theorem continued_member : ReleaseMember continued 1 3 := by
  refine ⟨⟨release7, rfl, rfl⟩, 0, 7, 7,
    ⟨release7, rfl, rfl, rfl⟩, ⟨sameThreadPlain7, rfl, rfl, rfl⟩, by decide, ?_⟩
  intro index value written aboveHead _atMostMember
  obtain ⟨event, live, _, stored⟩ := written
  rcases lookup_five (a := initial0) (b := release7) (d := foreignRmw7)
      (e := sameThreadPlain7) (f := observer7) live with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact False.elim (Nat.not_lt_zero 1 aboveHead)
  · exact False.elim (Nat.lt_irrefl 1 aboveHead)
  · exact Or.inr ⟨foreignRmw7, rfl, rfl⟩
  · exact Or.inl ⟨release7, sameThreadPlain7, 11, rfl, rfl, rfl, rfl⟩
  · cases stored

theorem continued_synchronizes : SynchronizesWith continued 1 4 := by
  refine ⟨⟨observer7, rfl, rfl⟩, 3, ?_, continued_member⟩
  exact ⟨rfl, 0, 7, ⟨observer7, rfl, rfl, rfl⟩,
    ⟨sameThreadPlain7, rfl, rfl, rfl⟩⟩

/-- A foreign plain store is inside the proposed sequence, before the selected
RMW. Even a later RMW by the original head's thread cannot rejoin the sequence. -/
def interrupted : Candidate Nat Nat where
  events := [initial0, release7, foreignRmw7, foreignPlain7, sameThreadRmw7, observer7]
  readsFrom index := if index = 2 then some 1 else if index = 4 then some 3
    else if index = 5 then some 4 else none
  rank index := index

theorem interrupted_no_rejoin : ¬ ReleaseMember interrupted 1 4 := by
  apply foreign_plain_breaks
    (headWrite := (show Writes interrupted 1 0 7 from ⟨release7, rfl, rfl, rfl⟩))
    (interveningWrite :=
      (show Writes interrupted 3 0 7 from ⟨foreignPlain7, rfl, rfl, rfl⟩))
    (afterHead := by decide) (atMostMember := by decide)
  · exact distinct_threads (c := interrupted) (i := 1) (j := 3)
      (left := release7) (right := foreignPlain7) rfl rfl (by decide)
  · exact plain_at (c := interrupted) (index := 3) (event := foreignPlain7) rfl rfl

theorem interrupted_no_sync : ¬ SynchronizesWith interrupted 1 5 := by
  rintro ⟨_, writer, source, member⟩
  have selected : writer = 4 := (Option.some.inj source.1).symm
  subst writer
  exact interrupted_no_rejoin member

/-- This acquire actually selects the later RMW; the failed synchronization
is caused by the interior foreign plain write, rather than an absent RF edge. -/
theorem interrupted_rmw_observation :
    IsRMW interrupted 4 ∧ ReadsFrom interrupted 5 4 ∧
      ¬ SynchronizesWith interrupted 1 5 := by
  exact ⟨⟨sameThreadRmw7, rfl, rfl⟩,
    ⟨rfl, 0, 7, ⟨observer7, rfl, rfl, rfl⟩, ⟨sameThreadRmw7, rfl, rfl, rfl⟩⟩,
    interrupted_no_sync⟩

end EDSL.Tests.C23AtomicEvents

#print axioms EDSL.Concurrency.C23Atomic.publication_chain
#print axioms EDSL.Concurrency.C23Atomic.Legal.message_passing_not_older
#print axioms EDSL.Concurrency.C23Atomic.Legal.message_passing_value
#print axioms EDSL.Tests.C23AtomicEvents.direct_legal
#print axioms EDSL.Tests.C23AtomicEvents.equal_bits_choose_identity
#print axioms EDSL.Tests.C23AtomicEvents.continued_synchronizes
#print axioms EDSL.Tests.C23AtomicEvents.interrupted_rmw_observation
#audit_edsl
