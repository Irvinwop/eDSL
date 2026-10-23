/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.EffectSimulation.Resources

/-!
Authenticated idle histories for resumable mixed blocks. A native passive
origin or an exact own blocked attempt can extend the history. Every actual
position remains in the connected suffix, including an own issue that retires
nothing. The blocked case requires the entire output state to equal the input;
a blocked observation alone never authenticates an idle position.

The existing `Pause` keeps its passive-only meaning. All invariant, code,
resource and protected-loan transport factors through the existing native
`OriginTrace`. The subject's saved context, phase, resource identity and store
counter survive; pending entries and current RAM may change. No future schedule,
Origin-to-step converse, instruction evaluator or progress claim is supplied.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.OS.TSO64.EffectSimulation.Mixed
open X86 AddressSpace

/-- A real native origin, restricted to passive interference or an own issue
whose complete result is the unchanged state and its own blocked observation. -/
structure IdleStep (profile : Profile) (family : RMWFamily) (tid : Nat) (tick : Tick) : Prop where
  origin : Origin tick.before tick.action tick.result profile family
  admissible : passive tid tick.action ∨
    ∃ af, tick.action = .issue tid af ∧ tick.result = (tick.before, .blocked tid)

/-- A connected finite extension of the exact log. Prefix admission remains a
separate obligation, transported by `Idle.authentic`. The family is trailing
and defaults to the existing XADD-only native semantics. -/
def Idle (profile : Profile) (tid : Nat) (before after : State × Log)
    (family : RMWFamily := .xaddOnly) : Prop :=
  ∃ suffix, OriginTrace profile before.1 suffix after.1 family ∧
    (∀ tick ∈ suffix, IdleStep profile family tid tick) ∧ after.2 = before.2 ++ suffix

theorem Idle.refl {profile : Profile} {family : RMWFamily} {tid : Nat}
    {current : State × Log} : Idle profile tid current current family :=
  ⟨[], .nil, by simp, by simp only [List.append_nil]⟩

/-- Append exactly one authenticated idle position. -/
theorem Idle.single {profile : Profile} {family : RMWFamily} {tid : Nat}
    {tick : Tick} {history : Log} (allowed : IdleStep profile family tid tick) :
    Idle profile tid (tick.before, history)
      (tick.result.1, history ++ [tick]) family := by
  refine ⟨[tick], OriginTrace.cons (tick := tick) allowed.origin .nil, ?_, rfl⟩
  intro next member
  have same := List.mem_singleton.mp member
  subst next
  exact allowed

/-- Every passive native origin is one idle position. -/
theorem Idle.step {profile : Profile} {family : RMWFamily} {tid : Nat} {before : State}
    {history : Log} {action : Action} {result : State × Observation}
    (quiet : passive tid action) (origin : Origin before action result profile family) :
    Idle profile tid (before, history)
      (result.1, history ++ [⟨before, action, result⟩]) family :=
  Idle.single (tick := ⟨before, action, result⟩) ⟨origin, Or.inl quiet⟩

/-- An actual successful own blocked step appends its real position. Native
blocking supplies whole-state equality, even when the result was presented
with a separate successor variable. There is no future-run premise. -/
theorem Idle.blocked_step {profile : Profile} {family : RMWFamily} {tid : Nat}
    {before after : State} {history : Log} {af : Bool}
    (actual : TSO64.step before (.issue tid af) profile family = .ok (after, .blocked tid)) :
    Idle profile tid (before, history)
      (after, history ++ [⟨before, .issue tid af, (after, .blocked tid)⟩]) family := by
  have unchanged : after = before := blocked_unchanged actual
  subst after
  exact Idle.single (tick := ⟨before, .issue tid af, (before, .blocked tid)⟩)
    ⟨step_origin actual, Or.inr ⟨af, rfl, rfl⟩⟩

theorem Idle.trans {profile : Profile} {family : RMWFamily} {tid : Nat}
    {before middle after : State × Log}
    (first : Idle profile tid before middle family)
    (second : Idle profile tid middle after family) :
    Idle profile tid before after family := by
  obtain ⟨front, firstTrace, firstAllowed, firstLog⟩ := first
  obtain ⟨back, secondTrace, secondAllowed, secondLog⟩ := second
  refine ⟨front ++ back, firstTrace.append secondTrace, ?_, ?_⟩
  · intro tick member
    rcases List.mem_append.mp member with old | new
    · exact firstAllowed tick old
    · exact secondAllowed tick new
  · rw [secondLog, firstLog, List.append_assoc]

/-- An idle extension transports an independently authenticated prefix. -/
theorem Idle.authentic {profile : Profile} {family : RMWFamily} {tid : Nat}
    {initial : State} {before after : State × Log}
    (idle : Idle profile tid before after family)
    (priorTrace : OriginTrace profile initial before.2 before.1 family) :
    OriginTrace profile initial after.2 after.1 family := by
  obtain ⟨suffix, trace, _allowed, same⟩ := idle
  rw [same]
  exact priorTrace.append trace

theorem Idle.wellFormed {profile : Profile} {family : RMWFamily} {tid : Nat}
    {before after : State × Log} (idle : Idle profile tid before after family)
    (valid : WellFormed before.1 profile) : WellFormed after.1 profile := by
  obtain ⟨_suffix, trace, _allowed, _same⟩ := idle
  exact trace.wellFormed valid

theorem Idle.code {profile : Profile} {family : RMWFamily} {tid : Nat}
    {before after : State × Log} (idle : Idle profile tid before after family)
    {base : Word} {bytes : List Byte} (code : CodeAt (published before.1.world) base bytes) :
    CodeAt (published after.1.world) base bytes := by
  obtain ⟨_suffix, trace, _allowed, _same⟩ := idle
  exact trace.code code

/-- Original resources survive at the same live index. -/
theorem Idle.resources {profile : Profile} {family : RMWFamily} {tid : Nat}
    {before after : State × Log} {prior : Worker}
    (idle : Idle profile tid before after family)
    (live : before.1.workers[tid]? = some prior) :
    ∃ current, after.1.workers[tid]? = some current ∧ current.resources = prior.resources := by
  obtain ⟨_suffix, trace, _allowed, _same⟩ := idle
  exact trace.resources live

/-- Current authority follows in the actual final world under the same profile. -/
theorem Idle.current_resources {profile : Profile} {family : RMWFamily} {tid : Nat}
    {before after : State × Log} {prior : Worker}
    (idle : Idle profile tid before after family) (valid : WellFormed before.1 profile)
    (live : before.1.workers[tid]? = some prior) :
    ∃ current, after.1.workers[tid]? = some current ∧ current.resources = prior.resources ∧
      ResourcesValid after.1.world current.resources := by
  obtain ⟨_suffix, trace, _allowed, _same⟩ := idle
  exact trace.current_resources valid live

/-- The fixed original protected borrowing read survives at its original
borrower, identifier and address; arbitrary shared RAM is not framed. -/
theorem Idle.loan_read_preserved {profile : Profile} {family : RMWFamily} {tid : Nat}
    {before after : State × Log} (idle : Idle profile tid before after family)
    (valid : WellFormed before.1 profile) {borrower identifier : Nat} {address value : Word}
    (read : Borrowing.loadWord64 before.1.world.legacy.shared borrower identifier address = .ok value) :
    Borrowing.loadWord64 after.1.world.legacy.shared borrower identifier address = .ok value := by
  obtain ⟨_suffix, trace, _allowed, _same⟩ := idle
  exact trace.loan_read_preserved valid read

/-- Passive origin transport handles interference; exact own blocking keeps
the entire input state, so it also retains all four saved worker fields. -/
theorem IdleStep.saved {profile : Profile} {family : RMWFamily} {tid : Nat}
    {tick : Tick} {prior : Worker} (allowed : IdleStep profile family tid tick)
    (live : tick.before.workers[tid]? = some prior) :
    ∃ current, tick.result.1.workers[tid]? = some current ∧ SavedFrame prior current := by
  rcases allowed.admissible with quiet | ⟨_af, _action, unchanged⟩
  · exact origin_saved allowed.origin quiet live
  · rw [unchanged]
    exact ⟨prior, live, SavedFrame.refl prior⟩

private theorem idleTrace_saved {profile : Profile} {family : RMWFamily} {tid : Nat}
    {initial final : State} {history : Log}
    (trace : OriginTrace profile initial history final family) :
    (∀ tick ∈ history, IdleStep profile family tid tick) →
    ∀ {prior : Worker}, initial.workers[tid]? = some prior →
      ∃ current, final.workers[tid]? = some current ∧ SavedFrame prior current := by
  induction trace with
  | nil => intro _allowed prior live; exact ⟨prior, live, .refl _⟩
  | cons _head _tail ih =>
    intro allowed prior live
    obtain ⟨middle, middleLive, first⟩ := (allowed _ List.mem_cons_self).saved live
    obtain ⟨current, currentLive, second⟩ :=
      ih (fun tick member => allowed tick (List.mem_cons_of_mem _ member)) middleLive
    exact ⟨current, currentLive, first.trans second⟩

/-- Saved context, phase, resource record and next-store counter survive.
Neither current RAM nor the own pending FIFO is required to remain unchanged. -/
theorem Idle.saved {profile : Profile} {family : RMWFamily} {tid : Nat}
    {before after : State × Log} {prior : Worker}
    (idle : Idle profile tid before after family) (live : before.1.workers[tid]? = some prior) :
    ∃ current, after.1.workers[tid]? = some current ∧ SavedFrame prior current := by
  obtain ⟨_suffix, trace, allowed, _same⟩ := idle
  exact idleTrace_saved trace allowed live

/-- Universal closure over all authenticated finite idle extensions. -/
def IdleBox (profile : Profile) (tid : Nat) (P : State → Log → Prop)
    (state : State) (history : Log) (family : RMWFamily := .xaddOnly) : Prop :=
  ∀ after extended, Idle profile tid (state, history) (after, extended) family → P after extended

theorem IdleBox.here {profile : Profile} {family : RMWFamily} {tid : Nat}
    {P : State → Log → Prop} {state : State} {history : Log}
    (closed : IdleBox profile tid P state history family) : P state history :=
  closed state history (Idle.refl (family := family))

theorem IdleBox.stable {profile : Profile} {family : RMWFamily} {tid : Nat}
    {P : State → Log → Prop} {before after : State} {history extended : Log}
    (closed : IdleBox profile tid P before history family)
    (idle : Idle profile tid (before, history) (after, extended) family) :
    IdleBox profile tid P after extended family := by
  intro final later following
  exact closed final later (idle.trans following)

private theorem trace_origins {profile : Profile} {family : RMWFamily}
    {initial final : State} {history : Log}
    (trace : OriginTrace profile initial history final family) :
    ∀ tick ∈ history, Origin tick.before tick.action tick.result profile family := by
  induction trace with
  | nil => intro tick member; simp at member
  | cons head _tail ih =>
    intro tick member
    rcases List.mem_cons.mp member with same | rest
    · subst tick
      exact head
    · exact ih tick rest

end EDSL.OS.TSO64.EffectSimulation.Mixed

namespace EDSL.OS.TSO64.EffectSimulation

/-- Existing passive pauses embed without changing the meaning of `Pause`. -/
theorem Pause.toIdle {profile : Profile} {family : RMWFamily} {tid : Nat}
    {before after : State × Log} (paused : Pause profile tid before after family) :
    Mixed.Idle profile tid before after family := by
  obtain ⟨suffix, trace, quiet, same⟩ := paused
  refine ⟨suffix, trace, ?_, same⟩
  intro tick member
  exact ⟨Mixed.trace_origins trace tick member, Or.inl (quiet tick member)⟩

end EDSL.OS.TSO64.EffectSimulation

#print axioms EDSL.OS.TSO64.EffectSimulation.Mixed.IdleStep
#print axioms EDSL.OS.TSO64.EffectSimulation.Mixed.Idle
#print axioms EDSL.OS.TSO64.EffectSimulation.Mixed.Idle.refl
#print axioms EDSL.OS.TSO64.EffectSimulation.Mixed.Idle.single
#print axioms EDSL.OS.TSO64.EffectSimulation.Mixed.Idle.step
#print axioms EDSL.OS.TSO64.EffectSimulation.Mixed.Idle.blocked_step
#print axioms EDSL.OS.TSO64.EffectSimulation.Mixed.Idle.trans
#print axioms EDSL.OS.TSO64.EffectSimulation.Mixed.Idle.authentic
#print axioms EDSL.OS.TSO64.EffectSimulation.Mixed.Idle.wellFormed
#print axioms EDSL.OS.TSO64.EffectSimulation.Mixed.Idle.code
#print axioms EDSL.OS.TSO64.EffectSimulation.Mixed.Idle.resources
#print axioms EDSL.OS.TSO64.EffectSimulation.Mixed.Idle.current_resources
#print axioms EDSL.OS.TSO64.EffectSimulation.Mixed.Idle.loan_read_preserved
#print axioms EDSL.OS.TSO64.EffectSimulation.Mixed.IdleStep.saved
#print axioms EDSL.OS.TSO64.EffectSimulation.Mixed.Idle.saved
#print axioms EDSL.OS.TSO64.EffectSimulation.Mixed.IdleBox
#print axioms EDSL.OS.TSO64.EffectSimulation.Mixed.IdleBox.here
#print axioms EDSL.OS.TSO64.EffectSimulation.Mixed.IdleBox.stable
#print axioms EDSL.OS.TSO64.EffectSimulation.Pause.toIdle
#audit_edsl
