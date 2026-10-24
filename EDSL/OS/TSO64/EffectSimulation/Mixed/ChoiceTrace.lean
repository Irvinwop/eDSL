/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Audit
import EDSL.OS.TSO64.Model

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Thread-local AF accounting for finite issue traces, starting at arbitrary
current per-thread offsets. Concatenation advances each thread by its own
issues in the entire left trace, including repeated and interleaved threads.
Drains do not consume choices and are excluded from chosen issue traces.

These are trace properties only: they do not assert successful execution,
retirement, fairness, termination, or any machine or resource precondition.
-/

namespace EDSL.OS.TSO64.EffectSimulation.Mixed.ChoiceTrace

/-- Count exactly the issue actions for this thread; drains do not count. -/
def issues (tid : Nat) (actions : List Action) : Nat :=
  (actions.filter fun action => match action with
    | .issue thread _ => decide (thread = tid)
    | .drain _ => false).length

/-- Consume one choice of the issuing thread at the current offsets. -/
def bump (offset : Nat → Nat) (tid : Nat) : Nat → Nat :=
  fun query => offset query + if query = tid then 1 else 0

/-- Every original position is an issue with AF selected by that thread's
current offset plus its own issues strictly before this position. -/
def ChosenFrom (choices : Nat → Nat → Bool) (offset : Nat → Nat)
    (actions : List Action) : Prop :=
  (∀ action ∈ actions, ∃ tid af, action = .issue tid af) ∧
  (∀ index tid af, actions[index]? = some (.issue tid af) →
    af = choices tid (offset tid + issues tid (actions.take index)))

def ChosenIssues (choices : Nat → Nat → Bool) (actions : List Action) : Prop :=
  ChosenFrom choices (fun _ => 0) actions

theorem issues_nil (tid : Nat) : issues tid [] = 0 := by
  simp [issues]

theorem issues_cons_issue (query tid : Nat) (af : Bool) (rest : List Action) :
    issues query (.issue tid af :: rest) =
      issues query rest + if query = tid then 1 else 0 := by
  by_cases same : query = tid
  · subst query
    simp [issues]
  · simp [issues, same, Ne.symm same]

theorem issues_cons_drain (query tid : Nat) (rest : List Action) :
    issues query (.drain tid :: rest) = issues query rest := by
  simp [issues]

/-- Issue counts compose for arbitrary actions, even when threads overlap. -/
theorem issues_append (tid : Nat) (left right : List Action) :
    issues tid (left ++ right) = issues tid left + issues tid right := by
  simp [issues, List.filter_append]

theorem bump_self (offset : Nat → Nat) (tid : Nat) :
    bump offset tid tid = offset tid + 1 := by
  simp [bump]

theorem bump_other (offset : Nat → Nat) (tid query : Nat) (different : query ≠ tid) :
    bump offset tid query = offset query := by
  simp [bump, different]

/-- Adding the whole cons prefix is the same as first consuming its head. -/
theorem offset_issue_cons (offset : Nat → Nat) (query tid : Nat) (af : Bool)
    (rest : List Action) :
    offset query + issues query (.issue tid af :: rest) =
      bump offset tid query + issues query rest := by
  simp only [issues_cons_issue, bump, Nat.add_assoc, Nat.add_comm]

theorem chosen_nil (choices : Nat → Nat → Bool) (offset : Nat → Nat) :
    ChosenFrom choices offset [] := by
  constructor
  · intro action member
    cases member
  · intro index tid af atIndex
    simp at atIndex

/-- Peeling an original issue consumes exactly that thread's next choice,
regardless of subsequent interleaving or repeated issues of the same thread. -/
theorem chosen_issue_cons_iff {choices : Nat → Nat → Bool} {offset : Nat → Nat}
    {tid : Nat} {af : Bool} {rest : List Action} :
    ChosenFrom choices offset (.issue tid af :: rest) ↔
      af = choices tid (offset tid) ∧ ChosenFrom choices (bump offset tid) rest := by
  constructor
  · intro chosen
    constructor
    · simpa only [List.take_zero, issues_nil, Nat.add_zero] using
        chosen.2 0 tid af rfl
    · constructor
      · intro action member
        exact chosen.1 action (List.mem_cons_of_mem _ member)
      · intro index query value atIndex
        have atCons : (.issue tid af :: rest)[index + 1]? = some (.issue query value) := by
          simpa only [List.getElem?_cons_succ] using atIndex
        simpa only [List.take_succ_cons, offset_issue_cons] using
          chosen.2 (index + 1) query value atCons
  · rintro ⟨head, tail⟩
    constructor
    · intro action member
      rcases List.mem_cons.mp member with same | later
      · subst action
        exact ⟨tid, af, rfl⟩
      · exact tail.1 action later
    · intro index query value atIndex
      cases index with
      | zero =>
        have same : tid = query ∧ af = value := by simpa using atIndex
        obtain ⟨rfl, rfl⟩ := same
        simpa only [List.take_zero, issues_nil, Nat.add_zero] using head
      | succ index =>
        have atRest : rest[index]? = some (.issue query value) := by
          simpa only [List.getElem?_cons_succ] using atIndex
        simpa only [List.take_succ_cons, offset_issue_cons] using
          tail.2 index query value atRest

theorem chosen_cons {choices : Nat → Nat → Bool} {offset : Nat → Nat}
    {tid : Nat} {rest : List Action}
    (chosen : ChosenFrom choices (bump offset tid) rest) :
    ChosenFrom choices offset (.issue tid (choices tid (offset tid)) :: rest) :=
  chosen_issue_cons_iff.mpr ⟨rfl, chosen⟩

/-- Continue from all current thread-local offsets after the entire left
trace. There is no restriction on which threads either trace may issue. -/
theorem chosen_append {choices : Nat → Nat → Bool} {offset : Nat → Nat}
    {left right : List Action}
    (leftChosen : ChosenFrom choices offset left)
    (rightChosen : ChosenFrom choices (fun tid => offset tid + issues tid left) right) :
    ChosenFrom choices offset (left ++ right) := by
  induction left generalizing offset with
  | nil =>
    simpa only [List.nil_append, issues_nil, Nat.add_zero] using rightChosen
  | cons action rest ih =>
    obtain ⟨tid, af, rfl⟩ := leftChosen.1 action (by simp)
    obtain ⟨head, tail⟩ := chosen_issue_cons_iff.mp leftChosen
    apply chosen_issue_cons_iff.mpr
    refine ⟨head, ih tail ?_⟩
    simpa only [offset_issue_cons] using rightChosen

#print axioms issues
#print axioms bump
#print axioms ChosenFrom
#print axioms ChosenIssues
#print axioms issues_nil
#print axioms issues_cons_issue
#print axioms issues_cons_drain
#print axioms issues_append
#print axioms bump_self
#print axioms bump_other
#print axioms offset_issue_cons
#print axioms chosen_nil
#print axioms chosen_issue_cons_iff
#print axioms chosen_cons
#print axioms chosen_append

end EDSL.OS.TSO64.EffectSimulation.Mixed.ChoiceTrace

#audit_edsl
