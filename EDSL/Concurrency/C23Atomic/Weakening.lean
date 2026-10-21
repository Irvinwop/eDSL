/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Concurrency.C23Atomic.Coherence

/-!
Memory-order weakening for the same supplied finite atomic execution. Access
constructors and values, event indices, objects, threads, selected RF sources
and modification ranks stay fixed. Only acquire and release flags may be
removed; an RMW's two flags may be removed independently.

The relation is defined from those data, without a happens-before or legality
premise. Synchronization and happens-before in the weaker candidate embed in
the stronger candidate, so legality of the stronger candidate transports to
the weaker one. Clients can use `Legal.weaken` after separately establishing
legality at maximal labels and the concrete relabeling relation.

This is a theorem about the fragment in `Model` and `Coherence`. Operational
realizability, source program consistency, native/source mappings and compiler
correctness remain separate obligations. No checker or proposal completeness
claim is made.
-/

set_option autoImplicit false

namespace EDSL.Concurrency.C23Atomic

namespace Access

variable {Value : Type}

/-- `Weakens strong weak` preserves the access constructor and all its values.
The flag implications permit removal of acquire/release, including either bit
of an RMW independently. Initialization has no order to weaken. -/
inductive Weakens : Access Value → Access Value → Prop where
  | initial (value : Value) : Weakens (.initialize value) (.initialize value)
  | load {strong weak : ReadOrder} {value : Value}
      (acquire : (Access.load weak value).acquires = true →
        (Access.load strong value).acquires = true) :
      Weakens (.load strong value) (.load weak value)
  | store {strong weak : WriteOrder} {value : Value}
      (release : (Access.store weak value).releases = true →
        (Access.store strong value).releases = true) :
      Weakens (.store strong value) (.store weak value)
  | rmw {strong weak : RMWOrder} {before after : Value}
      (acquire : (Access.rmw weak before after).acquires = true →
        (Access.rmw strong before after).acquires = true)
      (release : (Access.rmw weak before after).releases = true →
        (Access.rmw strong before after).releases = true) :
      Weakens (.rmw strong before after) (.rmw weak before after)

namespace Weakens

variable {strong weak : Access Value}

theorem refl (access : Access Value) : Weakens access access := by
  cases access with
  | «initialize» value => exact .initial value
  | load _ _ => exact .load (fun flag => flag)
  | store _ _ => exact .store (fun flag => flag)
  | rmw _ _ _ => exact .rmw (fun flag => flag) (fun flag => flag)

theorem readValue (labels : Weakens strong weak) :
    strong.readValue = weak.readValue := by
  cases labels <;> rfl

theorem writeValue (labels : Weakens strong weak) :
    strong.writeValue = weak.writeValue := by
  cases labels <;> rfl

theorem isInitial (labels : Weakens strong weak) :
    strong.isInitial = weak.isInitial := by
  cases labels <;> rfl

theorem isRMW (labels : Weakens strong weak) :
    strong.isRMW = weak.isRMW := by
  cases labels <;> rfl

theorem acquires (labels : Weakens strong weak)
    (flag : weak.acquires = true) : strong.acquires = true := by
  cases labels with
  | initial _ => cases flag
  | load acquire => exact acquire flag
  | store _ => cases flag
  | rmw acquire _ => exact acquire flag

theorem releases (labels : Weakens strong weak)
    (flag : weak.releases = true) : strong.releases = true := by
  cases labels with
  | initial _ => cases flag
  | load _ => cases flag
  | store release => exact release flag
  | rmw _ release => exact release flag

end Weakens
end Access

namespace Event

variable {Location Value : Type}

/-- An event keeps its object and logical thread, as well as its access shape
and values. The candidate relation below also keeps its list index. -/
structure Weakens (strong weak : Event Location Value) : Prop where
  thread_eq : strong.thread = weak.thread
  object_eq : strong.object = weak.object
  access : Access.Weakens strong.access weak.access

theorem Weakens.refl (event : Event Location Value) : Weakens event event :=
  ⟨rfl, rfl, Access.Weakens.refl event.access⟩

end Event

namespace Candidate

variable {Location Value : Type}

/-- Pointwise optional event correspondence fixes every live and absent index.
RF and rank functions are identical, including at indices outside the list.
No derived graph relation or legality condition is assumed. -/
structure Weakens (strong weak : Candidate Location Value) : Prop where
  events : ∀ (index : Nat), Option.Rel Event.Weakens strong.events[index]? weak.events[index]?
  readsFrom_eq : strong.readsFrom = weak.readsFrom
  rank_eq : strong.rank = weak.rank

namespace Weakens

variable {strong weak : Candidate Location Value}

theorem refl (candidate : Candidate Location Value) : Weakens candidate candidate := by
  refine ⟨?_, rfl, rfl⟩
  intro index
  cases candidate.events[index]? with
  | none => exact .none
  | some event => exact .some (Event.Weakens.refl event)

/-- Lookup in the stronger candidate yields the corresponding weaker event at
the same index, with its typed label relation. -/
theorem event_of_strong (labels : Weakens strong weak) {index : Nat}
    {event : Event Location Value} (live : strong.events[index]? = some event) :
    ∃ weakened, weak.events[index]? = some weakened ∧ Event.Weakens event weakened := by
  cases lookup : weak.events[index]? with
  | none =>
      have impossible : Option.Rel Event.Weakens (some event) none := by
        simpa only [live, lookup] using labels.events index
      cases impossible
  | some weakened =>
      have related : Option.Rel Event.Weakens (some event) (some weakened) := by
        simpa only [live, lookup] using labels.events index
      exact ⟨weakened, rfl, Option.rel_some_some.mp related⟩

/-- Lookup in the weaker candidate yields the corresponding stronger event at
the same index, without reconstructing an event from its observed value. -/
theorem event_of_weak (labels : Weakens strong weak) {index : Nat}
    {event : Event Location Value} (live : weak.events[index]? = some event) :
    ∃ original, strong.events[index]? = some original ∧ Event.Weakens original event := by
  cases lookup : strong.events[index]? with
  | none =>
      have impossible : Option.Rel Event.Weakens none (some event) := by
        simpa only [lookup, live] using labels.events index
      cases impossible
  | some original =>
      have related : Option.Rel Event.Weakens (some original) (some event) := by
        simpa only [lookup, live] using labels.events index
      exact ⟨original, rfl, Option.rel_some_some.mp related⟩

theorem reads_iff (labels : Weakens strong weak) {index : Nat}
    {location : Location} {value : Value} :
    Reads weak index location value ↔ Reads strong index location value := by
  constructor
  · rintro ⟨event, live, object, read⟩
    obtain ⟨original, originalLive, eventLabels⟩ := labels.event_of_weak live
    exact ⟨original, originalLive, eventLabels.object_eq.trans object,
      eventLabels.access.readValue.trans read⟩
  · rintro ⟨event, live, object, read⟩
    obtain ⟨weakened, weakenedLive, eventLabels⟩ := labels.event_of_strong live
    exact ⟨weakened, weakenedLive, eventLabels.object_eq.symm.trans object,
      eventLabels.access.readValue.symm.trans read⟩

theorem writes_iff (labels : Weakens strong weak) {index : Nat}
    {location : Location} {value : Value} :
    Writes weak index location value ↔ Writes strong index location value := by
  constructor
  · rintro ⟨event, live, object, write⟩
    obtain ⟨original, originalLive, eventLabels⟩ := labels.event_of_weak live
    exact ⟨original, originalLive, eventLabels.object_eq.trans object,
      eventLabels.access.writeValue.trans write⟩
  · rintro ⟨event, live, object, write⟩
    obtain ⟨weakened, weakenedLive, eventLabels⟩ := labels.event_of_strong live
    exact ⟨weakened, weakenedLive, eventLabels.object_eq.symm.trans object,
      eventLabels.access.writeValue.symm.trans write⟩

theorem sameThread_iff (labels : Weakens strong weak) {i j : Nat} :
    SameThread weak i j ↔ SameThread strong i j := by
  constructor
  · rintro ⟨first, second, thread, firstLive, secondLive, firstThread, secondThread⟩
    obtain ⟨originalFirst, originalFirstLive, firstLabels⟩ := labels.event_of_weak firstLive
    obtain ⟨originalSecond, originalSecondLive, secondLabels⟩ := labels.event_of_weak secondLive
    exact ⟨originalFirst, originalSecond, thread, originalFirstLive, originalSecondLive,
      firstLabels.thread_eq.trans firstThread, secondLabels.thread_eq.trans secondThread⟩
  · rintro ⟨first, second, thread, firstLive, secondLive, firstThread, secondThread⟩
    obtain ⟨weakenedFirst, weakenedFirstLive, firstLabels⟩ := labels.event_of_strong firstLive
    obtain ⟨weakenedSecond, weakenedSecondLive, secondLabels⟩ := labels.event_of_strong secondLive
    exact ⟨weakenedFirst, weakenedSecond, thread, weakenedFirstLive, weakenedSecondLive,
      firstLabels.thread_eq.symm.trans firstThread, secondLabels.thread_eq.symm.trans secondThread⟩

theorem isInitial_iff (labels : Weakens strong weak) {index : Nat} :
    IsInitial weak index ↔ IsInitial strong index := by
  constructor
  · rintro ⟨event, live, initial⟩
    obtain ⟨original, originalLive, eventLabels⟩ := labels.event_of_weak live
    exact ⟨original, originalLive, eventLabels.access.isInitial.trans initial⟩
  · rintro ⟨event, live, initial⟩
    obtain ⟨weakened, weakenedLive, eventLabels⟩ := labels.event_of_strong live
    exact ⟨weakened, weakenedLive, eventLabels.access.isInitial.symm.trans initial⟩

theorem isRMW_iff (labels : Weakens strong weak) {index : Nat} :
    IsRMW weak index ↔ IsRMW strong index := by
  constructor
  · rintro ⟨event, live, rmw⟩
    obtain ⟨original, originalLive, eventLabels⟩ := labels.event_of_weak live
    exact ⟨original, originalLive, eventLabels.access.isRMW.trans rmw⟩
  · rintro ⟨event, live, rmw⟩
    obtain ⟨weakened, weakenedLive, eventLabels⟩ := labels.event_of_strong live
    exact ⟨weakened, weakenedLive, eventLabels.access.isRMW.symm.trans rmw⟩

theorem seqBefore_iff (labels : Weakens strong weak) {i j : Nat} :
    SeqBefore weak i j ↔ SeqBefore strong i j := by
  exact and_congr Iff.rfl labels.sameThread_iff

theorem modBefore_iff (labels : Weakens strong weak) {i j : Nat} :
    ModBefore weak i j ↔ ModBefore strong i j := by
  constructor
  · rintro ⟨location, before, after, firstWrite, secondWrite, order⟩
    refine ⟨location, before, after, labels.writes_iff.mp firstWrite,
      labels.writes_iff.mp secondWrite, ?_⟩
    simpa only [labels.rank_eq] using order
  · rintro ⟨location, before, after, firstWrite, secondWrite, order⟩
    refine ⟨location, before, after, labels.writes_iff.mpr firstWrite,
      labels.writes_iff.mpr secondWrite, ?_⟩
    simpa only [labels.rank_eq] using order

theorem readsFrom_iff (labels : Weakens strong weak) {reader writer : Nat} :
    ReadsFrom weak reader writer ↔ ReadsFrom strong reader writer := by
  constructor
  · rintro ⟨source, location, value, read, write⟩
    refine ⟨?_, location, value, labels.reads_iff.mp read, labels.writes_iff.mp write⟩
    simpa only [labels.readsFrom_eq] using source
  · rintro ⟨source, location, value, read, write⟩
    refine ⟨?_, location, value, labels.reads_iff.mpr read, labels.writes_iff.mpr write⟩
    simpa only [labels.readsFrom_eq] using source

theorem acquires (labels : Weakens strong weak) {index : Nat}
    (acquire : Acquires weak index) : Acquires strong index := by
  rcases acquire with ⟨event, live, flag⟩
  obtain ⟨original, originalLive, eventLabels⟩ := labels.event_of_weak live
  exact ⟨original, originalLive, eventLabels.access.acquires flag⟩

theorem releases (labels : Weakens strong weak) {index : Nat}
    (release : Releases weak index) : Releases strong index := by
  rcases release with ⟨event, live, flag⟩
  obtain ⟨original, originalLive, eventLabels⟩ := labels.event_of_weak live
  exact ⟨original, originalLive, eventLabels.access.releases flag⟩

/-- All intervening writes remain present, with the same ranks, thread
identities and RMW kinds. Only the release flag on the head is monotone. -/
theorem releaseMember (labels : Weakens strong weak) {head member : Nat}
    (membership : ReleaseMember weak head member) : ReleaseMember strong head member := by
  rcases membership with
    ⟨release, location, headValue, memberValue, headWrite, memberWrite, lower, contiguous⟩
  refine ⟨labels.releases release, location, headValue, memberValue,
    labels.writes_iff.mp headWrite, labels.writes_iff.mp memberWrite, ?_, ?_⟩
  · simpa only [labels.rank_eq] using lower
  · intro index value written aboveHead atMostMember
    have weakAbove : weak.rank head < weak.rank index := by
      simpa only [labels.rank_eq] using aboveHead
    have weakUpper : weak.rank index ≤ weak.rank member := by
      simpa only [labels.rank_eq] using atMostMember
    rcases contiguous index value (labels.writes_iff.mpr written) weakAbove weakUpper with
      same | rmw
    · exact Or.inl (labels.sameThread_iff.mp same)
    · exact Or.inr (labels.isRMW_iff.mp rmw)

theorem synchronizesWith (labels : Weakens strong weak) {head reader : Nat}
    (edge : SynchronizesWith weak head reader) : SynchronizesWith strong head reader := by
  rcases edge with ⟨acquire, writer, source, member⟩
  exact ⟨labels.acquires acquire, writer, labels.readsFrom_iff.mp source,
    labels.releaseMember member⟩

/-- Induction on the actual weaker path derives inclusion; inclusion is not a
field or assumption of `Candidate.Weakens`. -/
theorem happensBefore (labels : Weakens strong weak) {i j : Nat}
    (path : HappensBefore weak i j) : HappensBefore strong i j := by
  induction path with
  | sequenced edge => exact .sequenced (labels.seqBefore_iff.mp edge)
  | synchronizes edge => exact .synchronizes (labels.synchronizesWith edge)
  | trans first second ihFirst ihSecond => exact .trans ihFirst ihSecond

end Weakens
end Candidate

variable {Location Value : Type} {strong weak : Candidate Location Value}

/-- Structural obligations transport using exact event and metadata identity;
no well-formedness premise for the weaker candidate is required. -/
theorem WellFormed.weaken (wellFormed : WellFormed strong)
    (labels : Candidate.Weakens strong weak) : WellFormed weak := by
  refine {
    threadKind := ?_
    initialUnique := ?_
    initialExists := ?_
    initialRank := ?_
    rankUnique := ?_
    readsSource := ?_
    noReadSource := ?_
  }
  · intro index event live
    obtain ⟨original, originalLive, eventLabels⟩ := labels.event_of_weak live
    rw [← eventLabels.thread_eq, ← eventLabels.access.isInitial]
    exact wellFormed.threadKind index original originalLive
  · intro i j location before after firstWrite secondWrite firstInitial secondInitial
    exact wellFormed.initialUnique i j location before after
      (labels.writes_iff.mp firstWrite) (labels.writes_iff.mp secondWrite)
      (labels.isInitial_iff.mp firstInitial) (labels.isInitial_iff.mp secondInitial)
  · intro index event live
    obtain ⟨original, originalLive, eventLabels⟩ := labels.event_of_weak live
    obtain ⟨initial, value, written, initialFlag⟩ :=
      wellFormed.initialExists index original originalLive
    refine ⟨initial, value, ?_, labels.isInitial_iff.mpr initialFlag⟩
    simpa only [eventLabels.object_eq] using (labels.writes_iff.mpr written)
  · intro index location value written
    have bounds := wellFormed.initialRank index location value (labels.writes_iff.mp written)
    constructor
    · intro initial
      simpa only [labels.rank_eq] using bounds.1 (labels.isInitial_iff.mp initial)
    · intro noninitial
      have originalNoninitial : ¬ IsInitial strong index := by
        intro initial
        exact noninitial (labels.isInitial_iff.mpr initial)
      simpa only [labels.rank_eq] using bounds.2 originalNoninitial
  · intro i j location before after firstWrite secondWrite equalRank
    apply wellFormed.rankUnique i j location before after
      (labels.writes_iff.mp firstWrite) (labels.writes_iff.mp secondWrite)
    simpa only [labels.rank_eq] using equalRank
  · intro reader location value read
    obtain ⟨writer, source⟩ :=
      wellFormed.readsSource reader location value (labels.reads_iff.mp read)
    exact ⟨writer, labels.readsFrom_iff.mpr source⟩
  · intro index unread
    have originalUnread : ∀ location value, ¬ Reads strong index location value := by
      intro location value read
      exact unread location value (labels.reads_iff.mpr read)
    simpa only [labels.readsFrom_eq] using wellFormed.noReadSource index originalUnread

/-- Each coherence implication has fewer possible HB premises after weakening;
its reads, writes, RF edges and rank conclusions remain the same. -/
theorem Coherent.weaken (coherent : Coherent strong)
    (labels : Candidate.Weakens strong weak) : Coherent weak := by
  refine {
    writeWrite := ?_
    readRead := ?_
    readWrite := ?_
    writeRead := ?_
  }
  · intro first second location a b firstWrite secondWrite path
    simpa only [labels.rank_eq] using coherent.writeWrite
      (labels.writes_iff.mp firstWrite) (labels.writes_iff.mp secondWrite)
      (labels.happensBefore path)
  · intro first second left right location a b firstRead secondRead leftSource rightSource path
    simpa only [labels.rank_eq] using coherent.readRead
      (labels.reads_iff.mp firstRead) (labels.reads_iff.mp secondRead)
      (labels.readsFrom_iff.mp leftSource) (labels.readsFrom_iff.mp rightSource)
      (labels.happensBefore path)
  · intro reader observed writer location a b read source write path
    simpa only [labels.rank_eq] using coherent.readWrite
      (labels.reads_iff.mp read) (labels.readsFrom_iff.mp source)
      (labels.writes_iff.mp write) (labels.happensBefore path)
  · intro writer reader observed location a b write read source path
    simpa only [labels.rank_eq] using coherent.writeRead
      (labels.writes_iff.mp write) (labels.reads_iff.mp read)
      (labels.readsFrom_iff.mp source) (labels.happensBefore path)

/-- A legal stronger candidate stays legal when only its memory-order flags
are weakened. Both RMW predecessor and absence of intervening modifications
transport through the invariant modification order. This theorem provides no
converse strengthening rule or operational/native/source realization. -/
theorem Legal.weaken (legal : Legal strong)
    (labels : Candidate.Weakens strong weak) : Legal weak := by
  refine {
    wellFormed := legal.wellFormed.weaken labels
    coherent := legal.coherent.weaken labels
    acyclic := ?_
    noFutureRead := ?_
    rmwPredecessor := ?_
  }
  · intro index cycle
    exact legal.acyclic index (labels.happensBefore cycle)
  · intro reader writer source future
    exact legal.noFutureRead (labels.readsFrom_iff.mp source) (labels.happensBefore future)
  · intro index writer rmw source
    obtain ⟨predecessor, immediate⟩ :=
      legal.rmwPredecessor (labels.isRMW_iff.mp rmw) (labels.readsFrom_iff.mp source)
    refine ⟨labels.modBefore_iff.mpr predecessor, ?_⟩
    intro middle lower upper
    exact immediate middle (labels.modBefore_iff.mp lower) (labels.modBefore_iff.mp upper)

end EDSL.Concurrency.C23Atomic
