/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.EffectSimulation.Mixed.Idle

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Subject-local Nat counts of native RMW observation labels, including projections
of complete Tick logs. Counting does not authenticate an arbitrary incoming
history. Idle transport uses each suffix position's native origin or exact own
blocked result; independent prefix authenticity is transported separately.
All profiles and RMW families are retained. These laws supply no program
success, fairness, completion or hardware refinement claim.
-/

namespace EDSL.OS.TSO64.EffectSimulation.Mixed.Counts

/-- Exactly one for the subject's RMW label, independently of its event payload. -/
def ownRMW (subject : Nat) : Observation → Nat
  | .rmw thread _ => if thread = subject then 1 else 0
  | _ => 0

/-- Count the subject's RMW events in an unfiltered observation list. -/
def countRMW (subject : Nat) : List Observation → Nat
  | [] => 0
  | observation :: rest => ownRMW subject observation + countRMW subject rest

/-- Inspect actual result labels without removing any scheduler positions. -/
def logRMW (subject : Nat) (history : Log) : Nat :=
  countRMW subject (history.map (fun tick => tick.result.2))

@[simp] theorem ownRMW_rmw (subject thread : Nat) (event : Atomics64.FetchAddEvent) :
    ownRMW subject (.rmw thread event) = (if thread = subject then 1 else 0) := rfl

@[simp] theorem ownRMW_ordinary (subject thread : Nat) :
    ownRMW subject (.ordinary thread) = 0 := rfl

@[simp] theorem ownRMW_returned (subject thread : Nat) :
    ownRMW subject (.returned thread) = 0 := rfl

@[simp] theorem ownRMW_blocked (subject thread : Nat) :
    ownRMW subject (.blocked thread) = 0 := rfl

@[simp] theorem ownRMW_drained (subject thread : Nat) (pending : Pending) :
    ownRMW subject (.drained thread pending) = 0 := rfl

@[simp] theorem countRMW_nil (subject : Nat) : countRMW subject [] = 0 := rfl

@[simp] theorem countRMW_cons (subject : Nat) (observation : Observation)
    (rest : List Observation) :
    countRMW subject (observation :: rest) = ownRMW subject observation + countRMW subject rest := rfl

theorem countRMW_append (subject : Nat) (front back : List Observation) :
    countRMW subject (front ++ back) = countRMW subject front + countRMW subject back := by
  induction front with
  | nil => simp only [List.nil_append, countRMW_nil, Nat.zero_add]
  | cons head tail ih =>
    simp only [List.cons_append, countRMW_cons, ih, Nat.add_assoc]

theorem countRMW_snoc (subject : Nat) (history : List Observation) (observation : Observation) :
    countRMW subject (history ++ [observation]) = countRMW subject history + ownRMW subject observation := by
  simp only [countRMW_append, countRMW_cons, countRMW_nil, Nat.add_zero]

@[simp] theorem logRMW_nil (subject : Nat) : logRMW subject [] = 0 := rfl

@[simp] theorem logRMW_cons (subject : Nat) (tick : Tick) (rest : Log) :
    logRMW subject (tick :: rest) = ownRMW subject tick.result.2 + logRMW subject rest := rfl

theorem logRMW_eq_countRMW_map (subject : Nat) (history : Log) :
    logRMW subject history = countRMW subject (history.map (fun tick => tick.result.2)) := rfl

theorem logRMW_append (subject : Nat) (front back : Log) :
    logRMW subject (front ++ back) = logRMW subject front + logRMW subject back := by
  simp only [logRMW, List.map_append, countRMW_append]

theorem logRMW_snoc (subject : Nat) (history : Log) (tick : Tick) :
    logRMW subject (history ++ [tick]) = logRMW subject history + ownRMW subject tick.result.2 := by
  simp only [logRMW_append, logRMW_cons, logRMW_nil, Nat.add_zero]

/-- The own native RMW label increments the count at its full issue position. -/
theorem logRMW_snoc_rmw (subject : Nat) (history : Log) (before after : State)
    (af : Bool) (event : Atomics64.FetchAddEvent) :
    logRMW subject (history ++ [⟨before, .issue subject af, (after, .rmw subject event)⟩]) =
      logRMW subject history + 1 := by
  rw [logRMW_snoc]
  change logRMW subject history + (if subject = subject then 1 else 0) = _
  rw [ite_eq_left rfl]

theorem logRMW_snoc_ordinary (subject thread : Nat) (history : Log) (before after : State) (af : Bool) :
    logRMW subject (history ++ [⟨before, .issue thread af, (after, .ordinary thread)⟩]) =
      logRMW subject history := by
  simp only [logRMW_snoc, ownRMW_ordinary, Nat.add_zero]

theorem logRMW_snoc_returned (subject thread : Nat) (history : Log) (before after : State) (af : Bool) :
    logRMW subject (history ++ [⟨before, .issue thread af, (after, .returned thread)⟩]) =
      logRMW subject history := by
  simp only [logRMW_snoc, ownRMW_returned, Nat.add_zero]

theorem logRMW_snoc_blocked (subject thread : Nat) (history : Log) (before : State) (af : Bool) :
    logRMW subject (history ++ [⟨before, .issue thread af, (before, .blocked thread)⟩]) =
      logRMW subject history := by
  simp only [logRMW_snoc, ownRMW_blocked, Nat.add_zero]

theorem logRMW_snoc_drained (subject thread : Nat) (history : Log) (before after : State) (pending : Pending) :
    logRMW subject (history ++ [⟨before, .drain thread, (after, .drained thread pending)⟩]) =
      logRMW subject history := by
  simp only [logRMW_snoc, ownRMW_drained, Nat.add_zero]

/-- Passive actions alone do not determine a label: the native origin does.
Ordinary finishes are inverted; peer RMW labels use the actual issuer index. -/
theorem origin_passive {profile : Profile} {family : RMWFamily} {subject : Nat}
    {before : State} {action : Action} {result : State × Observation}
    (origin : Origin before action result profile family) (quiet : passive subject action) :
    ownRMW subject result.2 = 0 := by
  cases origin with
  | ordinary _live _running _code _caller _fetched effect =>
    cases effect with
    | intro _supported _bounds _decoded _reads _queue _step finish =>
      cases finish <;> rfl
  | blocked => rfl
  | rmw => exact ite_eq_right quiet
  | drained => rfl

/-- Includes own blocked issues with their exact complete unchanged result. -/
theorem idleStep_zero {profile : Profile} {family : RMWFamily} {subject : Nat}
    {tick : Tick} (allowed : IdleStep profile family subject tick) :
    ownRMW subject tick.result.2 = 0 := by
  rcases allowed.admissible with quiet | ⟨_af, _action, unchanged⟩
  · exact origin_passive allowed.origin quiet
  · rw [unchanged]
    rfl

private theorem idleLog_zero {profile : Profile} {family : RMWFamily} {subject : Nat}
    (history : Log) :
    (∀ tick ∈ history, IdleStep profile family subject tick) → logRMW subject history = 0 := by
  induction history with
  | nil => intro _allowed; rfl
  | cons tick rest ih =>
    intro allowed
    have headZero := idleStep_zero (allowed tick List.mem_cons_self)
    have restZero := ih (fun next member => allowed next (List.mem_cons_of_mem tick member))
    simp only [logRMW_cons, headZero, restZero, Nat.zero_add]

/-- Any connected idle extension preserves the exact count of its incoming
log. Own blocked positions remain present, even though they contribute zero. -/
theorem logRMW_idle {profile : Profile} {family : RMWFamily} {subject : Nat}
    {before after : State × Log} (idle : Idle profile subject before after family) :
    logRMW subject after.2 = logRMW subject before.2 := by
  obtain ⟨suffix, _trace, allowed, same⟩ := idle
  rw [same, logRMW_append, idleLog_zero suffix allowed, Nat.add_zero]

/-- Transport an independently authenticated incoming history and its count. -/
theorem logRMW_idle_authentic {profile : Profile} {family : RMWFamily} {subject : Nat}
    {initial : State} {before after : State × Log}
    (idle : Idle profile subject before after family)
    (prior : OriginTrace profile initial before.2 before.1 family) :
    OriginTrace profile initial after.2 after.1 family ∧
      logRMW subject after.2 = logRMW subject before.2 :=
  ⟨idle.authentic prior, logRMW_idle idle⟩

#print axioms ownRMW
#print axioms countRMW
#print axioms logRMW
#print axioms ownRMW_rmw
#print axioms ownRMW_ordinary
#print axioms ownRMW_returned
#print axioms ownRMW_blocked
#print axioms ownRMW_drained
#print axioms countRMW_nil
#print axioms countRMW_cons
#print axioms countRMW_append
#print axioms countRMW_snoc
#print axioms logRMW_nil
#print axioms logRMW_cons
#print axioms logRMW_eq_countRMW_map
#print axioms logRMW_append
#print axioms logRMW_snoc
#print axioms logRMW_snoc_rmw
#print axioms logRMW_snoc_ordinary
#print axioms logRMW_snoc_returned
#print axioms logRMW_snoc_blocked
#print axioms logRMW_snoc_drained
#print axioms origin_passive
#print axioms idleStep_zero
#print axioms idleLog_zero
#print axioms logRMW_idle
#print axioms logRMW_idle_authentic

end EDSL.OS.TSO64.EffectSimulation.Mixed.Counts

#audit_edsl
