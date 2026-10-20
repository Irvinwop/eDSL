/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Concurrency.Linearizability

namespace EDSL.Concurrency.ModuloCounter

abbrev Call (width : Nat) (Id Thread : Type) :=
  Linearizability.Call Id Thread (BitVec width) (BitVec width)

abbrev Event (width : Nat) (Id Thread : Type) :=
  Linearizability.Event Id Thread (BitVec width) (BitVec width)

variable {width : Nat} {Id Thread : Type}

/-- Independent mathematical fetch-add contract, including the full old word.
The initial state and width are arbitrary, including the degenerate width zero.
The input is an argument, never reconstructed from an observed state change. -/
def Step (prior input response next : BitVec width) : Prop :=
  response = prior ∧ next.toNat = (prior.toNat + input.toNat) % 2^width

theorem step_iff {prior input response next : BitVec width} :
    Step prior input response next ↔ response = prior ∧ next = prior + input := by
  constructor
  · rintro ⟨returned, updated⟩
    exact ⟨returned, BitVec.eq_of_toNat_eq (updated.trans (BitVec.toNat_add _ _).symm)⟩
  · rintro ⟨returned, rfl⟩
    exact ⟨returned, BitVec.toNat_add _ _⟩

/-- Legal sequential object histories, independent of the executable checker.
Identity and actor matching belong to the generic complete-call protocol. -/
inductive Sequential : BitVec width → List (Call width Id Thread) → BitVec width → Prop where
  | nil (value) : Sequential value [] value
  | cons {prior middle final call calls}
      (step : Step prior call.input call.output middle)
      (tail : Sequential middle calls final) :
      Sequential prior (call :: calls) final

/-- Unbounded sum of invocation arguments in the proposed serial order. -/
def inputSum : List (Call width Id Thread) → Nat
  | [] => 0
  | call :: calls => call.input.toNat + inputSum calls

theorem Sequential.final_fold {prior final : BitVec width} {calls : List (Call width Id Thread)}
    (legal : Sequential prior calls final) :
    final = calls.foldl (fun state call => state + call.input) prior := by
  induction legal with
  | nil => rfl
  | cons step _ ih =>
    rw [List.foldl_cons, ← (step_iff.mp step).2]
    exact ih

/-- Natural-number conservation, reduced only at the object's width. -/
theorem Sequential.total {prior final : BitVec width} {calls : List (Call width Id Thread)}
    (legal : Sequential prior calls final) :
    final.toNat = (prior.toNat + inputSum calls) % 2^width := by
  induction legal with
  | nil value => simp [inputSum, Nat.mod_eq_of_lt value.isLt]
  | cons step _ ih =>
    rw [ih, step.2]
    simp only [inputSum, Nat.mod_add_mod, Nat.add_assoc]

/-- Executable sequential checker. It consumes each point's explicitly recorded
input and requires its output to equal the entire current state. -/
def eval (prior : BitVec width) : List (Call width Id Thread) → Option (BitVec width)
  | [] => some prior
  | call :: calls =>
    if call.output = prior then eval (prior + call.input) calls else none

theorem eval_sound {prior final : BitVec width} {calls : List (Call width Id Thread)}
    (accepted : eval prior calls = some final) : Sequential prior calls final := by
  induction calls generalizing prior with
  | nil =>
    have same : prior = final := Option.some.inj accepted
    subst final
    exact .nil _
  | cons call calls ih =>
    by_cases returned : call.output = prior
    · simp only [eval, returned, ↓reduceIte] at accepted
      exact .cons ⟨returned, BitVec.toNat_add _ _⟩ (ih accepted)
    · simp [eval, returned] at accepted

theorem eval_complete {prior final : BitVec width} {calls : List (Call width Id Thread)}
    (legal : Sequential prior calls final) : eval prior calls = some final := by
  induction legal with
  | nil => rfl
  | cons step _ ih =>
    simp only [eval, step.1, ↓reduceIte]
    rw [← (step_iff.mp step).2]
    exact ih

theorem eval_eq_some_iff {prior final : BitVec width} {calls : List (Call width Id Thread)} :
    eval prior calls = some final ↔ Sequential prior calls final :=
  ⟨eval_sound, eval_complete⟩

theorem Sequential.deterministic {prior left right : BitVec width}
    {calls : List (Call width Id Thread)}
    (first : Sequential prior calls left) (second : Sequential prior calls right) : left = right :=
  Option.some.inj ((eval_complete first).symm.trans (eval_complete second))

/-- Independent complete logical-history relation. The generic protocol binds
invocation input, actor, identity and response to exactly one internal point.
Object legality uses those point records in chronological point order. -/
def LegalHistory [DecidableEq Id] (prior final : BitVec width)
    (history : List (Event width Id Thread)) : Prop :=
  Linearizability.Protocol history ∧ Sequential prior (Linearizability.calls history) final

/-- Complete-history checker. Pending calls, missing boundaries and duplicate
points or returns are rejected even when their arithmetic effect is zero. -/
def checkComplete [DecidableEq Id] [DecidableEq Thread] (prior : BitVec width)
    (history : List (Event width Id Thread)) : Option (BitVec width) :=
  if Linearizability.check history then eval prior (Linearizability.calls history) else none

theorem checkComplete_sound [DecidableEq Id] [DecidableEq Thread]
    {prior final : BitVec width} {history : List (Event width Id Thread)}
    (accepted : checkComplete prior history = some final) : LegalHistory prior final history := by
  by_cases protocol : Linearizability.check history = true
  · exact ⟨Linearizability.check_sound protocol,
      eval_sound (by simpa only [checkComplete, protocol, ↓reduceIte] using accepted)⟩
  · simp [checkComplete, protocol] at accepted

theorem checkComplete_complete [DecidableEq Id] [DecidableEq Thread]
    {prior final : BitVec width} {history : List (Event width Id Thread)}
    (legal : LegalHistory prior final history) : checkComplete prior history = some final := by
  have protocol : Linearizability.check history = true := by
    exact decide_eq_true legal.1
  simp only [checkComplete, protocol, ↓reduceIte]
  exact eval_complete legal.2

theorem checkComplete_eq_some_iff [DecidableEq Id] [DecidableEq Thread]
    {prior final : BitVec width} {history : List (Event width Id Thread)} :
    checkComplete prior history = some final ↔ LegalHistory prior final history :=
  ⟨checkComplete_sound, checkComplete_complete⟩

/-- Composition with the existing interval/protocol theorem supplies exact
coverage, uniqueness and an order extending response-before-invocation time. -/
theorem LegalHistory.linearization [DecidableEq Id]
    {prior final : BitVec width} {history : List (Event width Id Thread)}
    (legal : LegalHistory prior final history) :
    Linearizability.Linearization history (fun calls => Sequential prior calls final) :=
  Linearizability.linearize legal.1 legal.2

/-- Logical histories only: supplied labels have no machine, OS or TSO origin
here. A future emitter must separately prove actual execution backing and the
invocation/RET boundaries. Acceptance alone makes no binary or scheduler claim. -/
theorem checked_linearization [DecidableEq Id] [DecidableEq Thread]
    {prior final : BitVec width} {history : List (Event width Id Thread)}
    (accepted : checkComplete prior history = some final) :
    Linearizability.Linearization history (fun calls => Sequential prior calls final) :=
  (checkComplete_sound accepted).linearization

theorem checked_total [DecidableEq Id] [DecidableEq Thread]
    {prior final : BitVec width} {history : List (Event width Id Thread)}
    (accepted : checkComplete prior history = some final) :
    final.toNat = (prior.toNat + inputSum (Linearizability.calls history)) % 2^width :=
  (checkComplete_sound accepted).2.total

end EDSL.Concurrency.ModuloCounter

#audit_edsl
