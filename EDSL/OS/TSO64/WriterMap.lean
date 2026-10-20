/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.Model

set_option autoImplicit false

namespace EDSL.OS.TSO64.PublishedHistory

/-- The complete observed writer identity. Buffered writes retain the issuing
thread, original authority descriptor and persistent per-worker occurrence.
An RMW retains its thread and complete event; its global position is in `Stamp`.
Equal payloads and zero-delta RMWs are still distinct write observations. -/
inductive WriteCause where
  | buffered (tid : Nat) (reference : Queue.ManagedRef) (value : X86.Word)
      (occurrence : Nat)
  | rmw (tid : Nat) (event : Atomics64.FetchAddEvent)
  deriving DecidableEq, Repr

def WriteCause.cell : WriteCause → Atomics64.CellId64
  | .buffered _ reference _ _ => reference.handle.cell
  | .rmw _ event => event.cell

def WriteCause.value : WriteCause → X86.Word
  | .buffered _ _ value _ => value
  | .rmw _ event => event.arithmetic.event.after

def WriteCause.tid : WriteCause → Nat
  | .buffered tid _ _ _ => tid
  | .rmw tid _ => tid

/-- Classify actual managed publications and RMWs without inspecting whether
the stored bits changed. Ordinary drains and nonwriting observations have no
managed-cell writer. This classifier itself asserts no execution or authority. -/
def writeOf : Observation → Option WriteCause
  | .drained tid (.managed reference value occurrence) =>
      some (.buffered tid reference value occurrence)
  | .rmw tid event => some (.rmw tid event)
  | _ => none

/-- Position in the supplied global observation stream, including all silent
observations. The caller supplies the stream's starting position to `after`. -/
structure Stamp where
  position : Nat
  cause : WriteCause
  deriving DecidableEq, Repr

abbrev Writers := Atomics64.CellId64 → Option Stamp

def empty : Writers := fun _ => none

/-- Ghost event metadata only: this changes no scheduler, CPU or world state. -/
def update (writers : Writers) (position : Nat) (observation : Observation) : Writers :=
  match writeOf observation with
  | none => writers
  | some cause => fun target =>
      if cause.cell = target then some ⟨position, cause⟩ else writers target

/-- Fold an oldest-first observation stream. Every observation consumes one
global position, whether or not it supplies a managed writer. -/
def after (offset : Nat) (observations : List Observation) (writers : Writers) : Writers :=
  match observations with
  | [] => writers
  | observation :: rest => after (offset + 1) rest (update writers offset observation)

/-- An absent writer reads from an explicit boundary word, with no invented
prehistory for that word or for arbitrary initial stamps. -/
def valueOf (writers : Writers) (target : Atomics64.CellId64) (boundary : X86.Word) :
    X86.Word :=
  match writers target with
  | none => boundary
  | some stamp => stamp.cause.value

theorem update_apply (writers : Writers) (position : Nat) (observation : Observation)
    (target : Atomics64.CellId64) :
    update writers position observation target =
      match writeOf observation with
      | none => writers target
      | some cause =>
          if cause.cell = target then some ⟨position, cause⟩ else writers target := by
  cases written : writeOf observation <;> simp only [update, written]

theorem update_written {writers : Writers} {position : Nat} {observation : Observation}
    {cause : WriteCause} (written : writeOf observation = some cause) :
    update writers position observation cause.cell = some ⟨position, cause⟩ := by
  simp [update, written]

theorem update_unchanged {writers : Writers} {position : Nat} {observation : Observation}
    {target : Atomics64.CellId64}
    (absent : ∀ cause, writeOf observation = some cause → cause.cell ≠ target) :
    update writers position observation target = writers target := by
  cases written : writeOf observation with
  | none => simp only [update, written]
  | some cause => simp only [update, written, ite_eq_right (absent cause written)]

theorem valueOf_update (writers : Writers) (position : Nat) (observation : Observation)
    (target : Atomics64.CellId64) (boundary : X86.Word) :
    valueOf (update writers position observation) target boundary =
      match writeOf observation with
      | none => valueOf writers target boundary
      | some cause =>
          if cause.cell = target then cause.value else valueOf writers target boundary := by
  cases written : writeOf observation with
  | none => simp only [update, written]
  | some cause =>
      by_cases same : cause.cell = target <;> simp [update, written, same, valueOf]

@[simp] theorem after_nil (offset : Nat) (writers : Writers) :
    after offset [] writers = writers := rfl

theorem after_cons (offset : Nat) (observation : Observation) (rest : List Observation)
    (writers : Writers) :
    after offset (observation :: rest) writers =
      after (offset + 1) rest (update writers offset observation) := rfl

/-- Appending a suffix advances its initial position by the entire prefix
length, including observations which do not update the writer map. -/
theorem after_append (offset : Nat) (first second : List Observation) (writers : Writers) :
    after offset (first ++ second) writers =
      after (offset + first.length) second (after offset first writers) := by
  induction first generalizing offset writers with
  | nil => simp only [List.nil_append, List.length_nil, Nat.add_zero, after_nil]
  | cons observation rest ih =>
      simp only [List.cons_append, after_cons, List.length_cons]
      rw [ih]
      have aligned : offset + 1 + rest.length = offset + (rest.length + 1) := by omega
      rw [aligned]

/-- No observation in this list writes the selected persistent cell. This
predicate refers directly to observations and complete causes, not values. -/
def NoWrites (observations : List Observation) (target : Atomics64.CellId64) : Prop :=
  ∀ observation ∈ observations, ∀ cause, writeOf observation = some cause → cause.cell ≠ target

theorem noWrites_nil (target : Atomics64.CellId64) : NoWrites [] target := by
  intro observation member
  cases member

private theorem noWrites_cons {observation : Observation} {rest : List Observation}
    {target : Atomics64.CellId64}
    (head : ∀ cause, writeOf observation = some cause → cause.cell ≠ target)
    (tail : NoWrites rest target) : NoWrites (observation :: rest) target := by
  intro actual member cause written
  rcases List.mem_cons.mp member with same | later
  · subst actual
    exact head cause written
  · exact tail actual later cause written

theorem after_noWrites {offset : Nat} {observations : List Observation} {writers : Writers}
    {target : Atomics64.CellId64} (absent : NoWrites observations target) :
    after offset observations writers target = writers target := by
  induction observations generalizing offset writers with
  | nil => rfl
  | cons observation rest ih =>
      have head : ∀ cause, writeOf observation = some cause → cause.cell ≠ target :=
        absent observation List.mem_cons_self
      have tail : NoWrites rest target := by
        intro actual member cause written
        exact absent actual (List.mem_cons_of_mem observation member) cause written
      calc
        after offset (observation :: rest) writers target =
            update writers offset observation target := ih tail
        _ = writers target := update_unchanged head

/-- Exact final-writer provenance. Either no observation writes this cell and
the stamp is from the supplied boundary, or the stamp names a real observation
at its exact global position and no later observation writes that cell.

The boundary is arbitrary: its stamp need not describe any earlier execution.
In particular, equality with an initial stamp alone does not prove absence of
writes; an observation may install a stamp identical to an arbitrary boundary. -/
theorem after_newest {offset : Nat} {observations : List Observation} {writers : Writers}
    {target : Atomics64.CellId64} {stamp : Stamp}
    (found : after offset observations writers target = some stamp) :
    (writers target = some stamp ∧ NoWrites observations target) ∨
      ∃ index observation, index < observations.length ∧
        observations[index]? = some observation ∧
        writeOf observation = some stamp.cause ∧
        stamp.position = offset + index ∧ stamp.cause.cell = target ∧
        NoWrites (observations.drop (index + 1)) target := by
  induction observations generalizing offset writers with
  | nil => exact .inl ⟨found, noWrites_nil target⟩
  | cons observation rest ih =>
      have following : after (offset + 1) rest (update writers offset observation) target =
          some stamp := found
      rcases ih following with boundary | later
      · obtain ⟨atHead, noTail⟩ := boundary
        cases written : writeOf observation with
        | none =>
            have noHead : ∀ cause, writeOf observation = some cause → cause.cell ≠ target := by
              intro cause impossible
              rw [written] at impossible
              cases impossible
            exact .inl ⟨by simpa only [update, written] using atHead,
              noWrites_cons noHead noTail⟩
        | some cause =>
            by_cases same : cause.cell = target
            · have equal : (⟨offset, cause⟩ : Stamp) = stamp := by
                apply Option.some.inj
                simpa only [update, written, ite_eq_left same] using atHead
              subst stamp
              exact .inr ⟨0, observation, Nat.zero_lt_succ _, rfl, written, rfl, same, noTail⟩
            · have noHead : ∀ other, writeOf observation = some other → other.cell ≠ target := by
                intro other otherWritten
                have equal : cause = other := Option.some.inj (written.symm.trans otherWritten)
                subst other
                exact same
              exact .inl ⟨by simpa only [update, written, ite_eq_right same] using atHead,
                noWrites_cons noHead noTail⟩
      · obtain ⟨index, actual, bound, present, written, position, cell, noLater⟩ := later
        refine .inr ⟨index + 1, actual, Nat.succ_lt_succ bound, ?_, written, ?_, cell, ?_⟩
        · simpa only [List.getElem?_cons_succ] using present
        · omega
        · simpa only [List.drop_succ_cons] using noLater

/-- A convenient weaker projection of `after_newest`. The initial alternative
is a source-boundary equality, not by itself a claim that no writes occurred. -/
theorem after_origin {offset : Nat} {observations : List Observation} {writers : Writers}
    {target : Atomics64.CellId64} {stamp : Stamp}
    (found : after offset observations writers target = some stamp) :
    writers target = some stamp ∨
      ∃ index observation, index < observations.length ∧
        observations[index]? = some observation ∧
        writeOf observation = some stamp.cause ∧
        stamp.position = offset + index ∧ stamp.cause.cell = target := by
  rcases after_newest found with boundary | current
  · exact .inl boundary.1
  · obtain ⟨index, observation, bound, present, written, position, cell, _noLater⟩ := current
    exact .inr ⟨index, observation, bound, present, written, position, cell⟩

/-- An empty boundary forces a real newest observation, even for repeated
equal-valued publications or an RMW whose arithmetic result is unchanged. -/
theorem after_empty_newest {offset : Nat} {observations : List Observation}
    {target : Atomics64.CellId64} {stamp : Stamp}
    (found : after offset observations empty target = some stamp) :
    ∃ index observation, index < observations.length ∧
      observations[index]? = some observation ∧
      writeOf observation = some stamp.cause ∧
      stamp.position = offset + index ∧ stamp.cause.cell = target ∧
      NoWrites (observations.drop (index + 1)) target := by
  rcases after_newest found with boundary | current
  · have impossible : (none : Option Stamp) = some stamp := boundary.1
    cases impossible
  · exact current

end EDSL.OS.TSO64.PublishedHistory
