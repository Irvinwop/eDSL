/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.Queue.Authority
import EDSL.X86.StoreBuffer.WholeQWord

set_option autoImplicit false

namespace EDSL.OS.TSO64.Queue
open X86

/-- Managed occurrence numbers in FIFO order. Ordinary stores consume sequence
numbers, but need not retain them, so this list may contain gaps. -/
def occurrences : List Entry → List Nat
  | [] => []
  | .ordinary _ _ :: entries => occurrences entries
  | .managed _ _ occurrence :: entries => occurrence :: occurrences entries

/-- Per-worker queue metadata. `nextStore` counts successful enqueues since
setup and does not depend on the current queue length. A scheduler must commit
an enqueue together with successful instruction execution, and pair a
managed occurrence with its worker identifier before using it as an identity.
This structure alone is neither a scheduler history nor a reads-from proof. -/
structure Cursor where
  pending : List Entry
  nextStore : Nat
  deriving DecidableEq, Repr

/-- The initial boundary has issued no stores. A nonempty initial queue needs a
separate provenance boundary; an invariant cannot invent earlier issue events. -/
def Cursor.empty : Cursor := ⟨[], 0⟩

/-- FIFO order and a strict upper bound on every retained managed occurrence.
This is metadata integrity; current resource authority is `Queue.Valid`. -/
def Cursor.Ordered (cursor : Cursor) : Prop :=
  (occurrences cursor.pending).Pairwise (fun first second => first < second) ∧
    ∀ occurrence ∈ occurrences cursor.pending, occurrence < cursor.nextStore

/-- Every successful ordinary store consumes one issue number. -/
def Cursor.enqueueOrdinary (cursor : Cursor) (ticket : Ownership.Ticket) (store : Store) : Cursor :=
  ⟨cursor.pending ++ [.ordinary ticket store], cursor.nextStore + 1⟩

/-- Allocate the managed occurrence from the pre-enqueue counter, independently
of the value, address, instruction pointer and number of stores still pending. -/
def Cursor.enqueueManaged (cursor : Cursor) (reference : ManagedRef) (value : Word) : Cursor :=
  ⟨cursor.pending ++ [.managed reference value cursor.nextStore], cursor.nextStore + 1⟩

/-- Pure queue bookkeeping after selecting the head for publication. This does
not authorize or publish a store, and never changes the sequence counter. -/
def Cursor.dropHead (cursor : Cursor) : Cursor :=
  ⟨cursor.pending.tail, cursor.nextStore⟩

/-- Checked admission followed by typed occurrence allocation. No caller can
supply a managed occurrence here. Admission itself changes no world memory. -/
def Cursor.enqueue (cursor : Cursor) (world : World) (resources : Resources)
    (store : Store) (profile : Profile := .ownedOnly) : Except Fault Cursor := do
  let entry ← admit world resources store cursor.nextStore profile
  match entry with
  | .ordinary ticket admittedStore => pure (cursor.enqueueOrdinary ticket admittedStore)
  | .managed reference value _ => pure (cursor.enqueueManaged reference value)

@[simp] theorem occurrences_nil : occurrences [] = [] := rfl

@[simp] theorem occurrences_ordinary (ticket : Ownership.Ticket) (store : Store)
    (entries : List Entry) :
    occurrences (.ordinary ticket store :: entries) = occurrences entries := rfl

@[simp] theorem occurrences_managed (reference : ManagedRef) (value : Word)
    (occurrence : Nat) (entries : List Entry) :
    occurrences (.managed reference value occurrence :: entries) =
      occurrence :: occurrences entries := rfl

theorem occurrences_append (first second : List Entry) :
    occurrences (first ++ second) = occurrences first ++ occurrences second := by
  induction first with
  | nil => rfl
  | cons entry entries ih =>
    cases entry <;> simp only [List.cons_append, occurrences, ih]

@[simp] theorem Cursor.empty_ordered : Cursor.empty.Ordered := by
  simp [Cursor.empty, Cursor.Ordered]

private theorem pairwise_append_last (values : List Nat) (last : Nat)
    (ordered : values.Pairwise (fun first second => first < second))
    (below : ∀ value ∈ values, value < last) :
    (values ++ [last]).Pairwise (fun first second => first < second) := by
  revert ordered below
  induction values with
  | nil => intro _ _; simp
  | cons first rest ih =>
    intro ordered below
    obtain ⟨head, tail⟩ := List.pairwise_cons.mp ordered
    apply List.pairwise_cons.mpr
    constructor
    · intro value member
      rcases List.mem_append.mp member with member | member
      · exact head value member
      · have equal : value = last := by simpa only [List.mem_singleton] using member
        subst value
        exact below first List.mem_cons_self
    · exact ih tail (fun value member => below value (List.mem_cons_of_mem first member))

theorem Cursor.enqueueOrdinary_ordered (cursor : Cursor) (ticket : Ownership.Ticket)
    (store : Store) (ordered : cursor.Ordered) :
    (cursor.enqueueOrdinary ticket store).Ordered := by
  rcases ordered with ⟨pairwise, below⟩
  constructor
  · simpa only [Cursor.enqueueOrdinary, occurrences_append, occurrences_ordinary,
      occurrences_nil, List.append_nil] using pairwise
  · intro occurrence member
    have old : occurrence ∈ occurrences cursor.pending := by
      simpa only [Cursor.enqueueOrdinary, occurrences_append, occurrences_ordinary,
        occurrences_nil, List.append_nil] using member
    exact Nat.lt_trans (below occurrence old) (Nat.lt_succ_self cursor.nextStore)

theorem Cursor.enqueueManaged_ordered (cursor : Cursor) (reference : ManagedRef)
    (value : Word) (ordered : cursor.Ordered) :
    (cursor.enqueueManaged reference value).Ordered := by
  rcases ordered with ⟨pairwise, below⟩
  constructor
  · simpa only [Cursor.enqueueManaged, occurrences_append, occurrences_managed,
      occurrences_nil] using pairwise_append_last (occurrences cursor.pending)
        cursor.nextStore pairwise below
  · intro occurrence member
    have present : occurrence ∈ occurrences cursor.pending ++ [cursor.nextStore] := by
      simpa only [Cursor.enqueueManaged, occurrences_append, occurrences_managed,
        occurrences_nil] using member
    rcases List.mem_append.mp present with old | fresh
    · exact Nat.lt_trans (below occurrence old) (Nat.lt_succ_self cursor.nextStore)
    · have equal : occurrence = cursor.nextStore := by
        simpa only [List.mem_singleton] using fresh
      subst occurrence
      exact Nat.lt_succ_self cursor.nextStore

theorem Cursor.dropHead_ordered (cursor : Cursor) (ordered : cursor.Ordered) :
    cursor.dropHead.Ordered := by
  rcases cursor with ⟨entries, nextStore⟩
  cases entries with
  | nil => exact ordered
  | cons entry entries =>
    cases entry with
    | ordinary ticket store => exact ordered
    | managed reference value occurrence =>
      rcases ordered with ⟨pairwise, below⟩
      constructor
      · exact (List.pairwise_cons.mp pairwise).2
      · intro next member
        exact below next (List.mem_cons_of_mem occurrence member)

/-- Checked enqueue retains the exact admitted tag. In particular the actual
admission effect establishes the managed occurrence, rather than trusting an
arbitrary raw entry supplied by a caller. -/
theorem Cursor.enqueue_effect (cursor : Cursor) (world : World) (resources : Resources)
    (store : Store) (profile : Profile) (next : Cursor)
    (success : cursor.enqueue world resources store profile = .ok next) :
    ∃ entry, Admission world resources store cursor.nextStore profile entry ∧
      next.pending = cursor.pending ++ [entry] ∧ next.nextStore = cursor.nextStore + 1 := by
  cases admitted : admit world resources store cursor.nextStore profile with
  | error fault => simp [Cursor.enqueue, admitted] at success
  | ok entry =>
    have effect := admit_effect admitted
    cases effect with
    | ordinary ticket selected =>
      have equal : cursor.enqueueOrdinary ticket store = next := by
        simpa [Cursor.enqueue, admitted] using success
      subst next
      exact ⟨_, .ordinary ticket selected, rfl, rfl⟩
    | managed reference value ordinaryAbsent shared qword selected =>
      have equal : cursor.enqueueManaged reference value = next := by
        simpa [Cursor.enqueue, admitted] using success
      subst next
      exact ⟨_, .managed reference value ordinaryAbsent shared qword selected, rfl, rfl⟩

/-- Enqueue preserves current authority of the queue if its preexisting entries
have current authority. Sequence integrity is a separate theorem below. -/
theorem Cursor.enqueue_valid (cursor : Cursor) (world : World) (resources : Resources)
    (store : Store) (profile : Profile) (next : Cursor)
    (valid : ∀ entry ∈ cursor.pending, Valid world resources entry profile)
    (success : cursor.enqueue world resources store profile = .ok next) :
    ∀ entry ∈ next.pending, Valid world resources entry profile := by
  obtain ⟨admitted, effect, pending, _counter⟩ :=
    cursor.enqueue_effect world resources store profile next success
  intro entry member
  rw [pending] at member
  rcases List.mem_append.mp member with old | fresh
  · exact valid entry old
  · have equal : entry = admitted := by simpa only [List.mem_singleton] using fresh
    subst entry
    exact effect.valid

/-- A successful checked admission consumes precisely one number, even when
ordinary authority wins over a possible managed fallback. -/
theorem Cursor.enqueue_nextStore (cursor : Cursor) (world : World) (resources : Resources)
    (store : Store) (profile : Profile) (next : Cursor)
    (success : cursor.enqueue world resources store profile = .ok next) :
    next.nextStore = cursor.nextStore + 1 := by
  obtain ⟨_entry, _effect, _pending, counter⟩ :=
    cursor.enqueue_effect world resources store profile next success
  exact counter

/-- The successor invariant follows from the typed enqueue operations; the
executable admission does not test a desired successor invariant. -/
theorem Cursor.enqueue_ordered (cursor : Cursor) (world : World) (resources : Resources)
    (store : Store) (profile : Profile) (next : Cursor) (ordered : cursor.Ordered)
    (success : cursor.enqueue world resources store profile = .ok next) :
    next.Ordered := by
  cases admitted : admit world resources store cursor.nextStore profile with
  | error fault => simp [Cursor.enqueue, admitted] at success
  | ok entry =>
    cases entry with
    | ordinary ticket admittedStore =>
      have equal : cursor.enqueueOrdinary ticket admittedStore = next := by
        simpa [Cursor.enqueue, admitted] using success
      subst next
      exact cursor.enqueueOrdinary_ordered ticket admittedStore ordered
    | managed reference value occurrence =>
      have equal : cursor.enqueueManaged reference value = next := by
        simpa [Cursor.enqueue, admitted] using success
      subst next
      exact cursor.enqueueManaged_ordered reference value ordered

@[simp] theorem Cursor.dropHead_nextStore (cursor : Cursor) :
    cursor.dropHead.nextStore = cursor.nextStore := rfl

/-- FIFO removal preserves every remaining tag and its original occurrence;
there is no renumbering after a publication. -/
theorem Cursor.dropHead_cons (entry : Entry) (entries : List Entry) (nextStore : Nat) :
    (Cursor.mk (entry :: entries) nextStore).dropHead = ⟨entries, nextStore⟩ := rfl

/-- The second managed enqueue has a different occurrence even when its value
and complete descriptor equal those of the first. Ordinary enqueues may
leave gaps, and draining cannot recycle either sequence number. -/
theorem Cursor.two_managed_enqueues (cursor : Cursor) (reference : ManagedRef) (value : Word) :
    ((cursor.enqueueManaged reference value).enqueueManaged reference value).pending =
      cursor.pending ++ [.managed reference value cursor.nextStore,
        .managed reference value (cursor.nextStore + 1)] ∧
    cursor.nextStore ≠ cursor.nextStore + 1 := by
  constructor
  · simp only [Cursor.enqueueManaged, List.append_assoc, List.cons_append, List.nil_append]
  · exact Nat.ne_of_lt (Nat.lt_succ_self cursor.nextStore)

/-- The invariant rules out duplicate managed occurrence numbers, including
repeated stores of equal values to the same descriptor. -/
theorem Cursor.occurrences_nodup (cursor : Cursor) (ordered : cursor.Ordered) :
    (occurrences cursor.pending).Nodup := by
  apply List.nodup_iff_pairwise_ne.mpr
  exact ordered.1.imp (fun less => Nat.ne_of_lt less)

theorem managed_mem_occurrences (entries : List Entry) (reference : ManagedRef)
    (value : Word) (occurrence : Nat)
    (member : .managed reference value occurrence ∈ entries) :
    occurrence ∈ occurrences entries := by
  revert member
  induction entries with
  | nil => intro member; cases member
  | cons entry entries ih =>
    intro member
    rcases List.mem_cons.mp member with same | later
    · subst entry
      exact List.mem_cons_self
    · cases entry with
      | ordinary ticket store => exact ih later
      | managed reference value prior => exact List.mem_cons_of_mem prior (ih later)

/-- A retained managed tag is below the counter. Actual issue provenance also
requires a history or reachability proof; this numerical bound cannot supply it. -/
theorem Cursor.managed_occurrence_lt (cursor : Cursor) (ordered : cursor.Ordered)
    (reference : ManagedRef) (value : Word) (occurrence : Nat)
    (member : .managed reference value occurrence ∈ cursor.pending) :
    occurrence < cursor.nextStore :=
  ordered.2 occurrence (managed_mem_occurrences cursor.pending reference value occurrence member)

/-- Lifting a production byte-buffer position recovers the exact tagged queue
entry, rather than identifying a writer from its stored value. -/
theorem payload_getElem?_some (entries : List Entry) (index : Nat) (store : Store)
    (found : (payload entries)[index]? = some store) :
    ∃ entry, entries[index]? = some entry ∧ entry.store = store := by
  induction entries generalizing index with
  | nil => simp [payload] at found
  | cons entry entries ih =>
    cases index with
    | zero =>
      have equal : entry.store = store := by
        simpa only [payload_cons, List.getElem?_cons_zero, Option.some.injEq] using found
      exact ⟨entry, rfl, equal⟩
    | succ index =>
      have tail : (payload entries)[index]? = some store := by
        simpa only [payload_cons, List.getElem?_cons_succ] using found
      obtain ⟨selected, present, equal⟩ := ih index tail
      exact ⟨selected, by simpa only [List.getElem?_cons_succ] using present, equal⟩

/-- `newestQWord` positions become actual queue entries. An ordinary entry is
still possible until a resource theorem rules it out for the selected cell. -/
theorem newestQWord_entry (entries : List Entry) (address : Word)
    (origin : StoreBuffer.Mixed.QWordOrigin)
    (found : StoreBuffer.Mixed.newestQWord (payload entries) address = some origin) :
    ∃ entry, entries[origin.index]? = some entry ∧
      entry.store = ⟨address, .qword origin.value⟩ :=
  payload_getElem?_some entries origin.index _
    (StoreBuffer.Mixed.newestQWord_getElem? (payload entries) address origin found)


/-- Recover the tag at the production newest-qword position. A managed case
retains its exact sequence ID and an established counter bound, including
when other entries store the same word. The ordinary alternative cannot be
removed by metadata integrity alone. -/
theorem Cursor.newestQWord_tag (cursor : Cursor) (ordered : cursor.Ordered)
    (address : Word) (origin : StoreBuffer.Mixed.QWordOrigin)
    (found : StoreBuffer.Mixed.newestQWord (payload cursor.pending) address = some origin) :
    (∃ ticket, cursor.pending[origin.index]? =
      some (.ordinary ticket ⟨address, .qword origin.value⟩)) ∨
    (∃ reference occurrence, cursor.pending[origin.index]? =
      some (.managed reference origin.value occurrence) ∧
      reference.cell.address = address ∧ occurrence < cursor.nextStore) := by
  obtain ⟨entry, present, storeEq⟩ := newestQWord_entry cursor.pending address origin found
  cases entry with
  | ordinary ticket store =>
    have equal : store = ⟨address, .qword origin.value⟩ := storeEq
    subst store
    exact .inl ⟨ticket, present⟩
  | managed reference value occurrence =>
    have addressEq : reference.cell.address = address := congrArg (fun store : Store => store.address) storeEq
    have valueEq : value = origin.value := by
      have equal := congrArg (fun store : Store => store.value) storeEq
      exact StoreBuffer.Mixed.Value.qword.inj equal
    subst value
    exact .inr ⟨reference, occurrence, present, addressEq,
      cursor.managed_occurrence_lt ordered reference origin.value occurrence
        (List.mem_of_getElem? present)⟩

end EDSL.OS.TSO64.Queue
