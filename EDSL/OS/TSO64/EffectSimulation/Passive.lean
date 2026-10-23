/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.EffectSimulation.Lifting

/-!
Passive interference for resumable ordinary blocks. Every drain is
passive, including an own drain after RET; only peer issues are passive.
Histories retain the real before/result states and all scheduler positions.

`OriginTrace` authenticates a connected prefix from a separately admitted
initial state. `Pause` only extends an existing history; it does not certify
that history's admission. Its edges use native `Origin`, as supplied by
`Simulation.lift`, without requiring or asserting an Origin-to-step converse.
Successful schedules supply such edges through `step_origin`.

The saved-worker frame omits pending entries and RAM. Own drains can change
both; peer publication can change the reconstructed local CPU. No return
postcondition, generated block WP, scheduler interpreter or progress result
is supplied here.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.OS.TSO64.EffectSimulation
open X86 AddressSpace

/-- All native publications, and issues by workers other than the subject. -/
def passive (tid : Nat) : Action → Prop
  | .issue peer _ => peer ≠ tid
  | .drain _ => True

/-- One unfiltered scheduler position, with its actual current input and
complete output. Its position is its index in the containing log. -/
structure Tick where
  before : State
  action : Action
  result : State × Observation

abbrev Log := List Tick

/-- Independent prefix authenticity relative to a fixed initial state.
Admission of that initial state is a separate client obligation. Adjacent
ticks share the actual result/input state; no disconnected history is admitted.
These are native origins, not a claim of an executable Origin converse. -/
inductive OriginTrace (profile : Profile) : State → Log → State → Prop where
  | nil {state : State} : OriginTrace profile state [] state
  | cons {tick : Tick} {history : Log} {final : State}
      (head : Origin tick.before tick.action tick.result profile)
      (tail : OriginTrace profile tick.result.1 history final) :
      OriginTrace profile tick.before (tick :: history) final

theorem OriginTrace.append {profile : Profile} {initial middle final : State}
    {front back : Log}
    (first : OriginTrace profile initial front middle)
    (second : OriginTrace profile middle back final) :
    OriginTrace profile initial (front ++ back) final := by
  induction first with
  | nil => exact second
  | cons head _ ih => exact .cons head (ih second)

/-- The single extension needed by an origin-indexed simulation law. -/
theorem OriginTrace.snoc {profile : Profile} {initial before : State}
    {history : Log} {action : Action} {result : State × Observation}
    (priorTrace : OriginTrace profile initial history before)
    (origin : Origin before action result profile) :
    OriginTrace profile initial (history ++ [⟨before, action, result⟩]) result.1 :=
  priorTrace.append (OriginTrace.cons (tick := ⟨before, action, result⟩) origin .nil)

/-- Recover both authentic cuts and the native origin at an original log
index. Drains and blocked attempts are retained and consume positions. -/
theorem OriginTrace.at {profile : Profile} {initial final : State}
    {history : Log} (trace : OriginTrace profile initial history final)
    {index : Nat} {tick : Tick} (found : history[index]? = some tick) :
    OriginTrace profile initial (history.take index) tick.before ∧
      Origin tick.before tick.action tick.result profile ∧
      OriginTrace profile initial (history.take (index + 1)) tick.result.1 := by
  induction trace generalizing index with
  | nil => simp at found
  | cons head _ ih =>
    cases index with
    | zero =>
      have same := Option.some.inj found
      subst tick
      exact ⟨.nil, head, .cons head .nil⟩
    | succ index =>
      obtain ⟨priorTrace, origin, next⟩ := ih (index := index) found
      exact ⟨.cons head priorTrace, origin, .cons head next⟩

/-- Reflexive-transitive native passive interference, appending exactly a
connected passive suffix. An arbitrary preexisting log needs the separate
`OriginTrace` premise in `Pause.authentic`. -/
def Pause (profile : Profile) (tid : Nat) (before after : State × Log) : Prop :=
  ∃ suffix, OriginTrace profile before.1 suffix after.1 ∧
    (∀ tick ∈ suffix, passive tid tick.action) ∧ after.2 = before.2 ++ suffix

theorem Pause.refl {profile : Profile} {tid : Nat} {current : State × Log} :
    Pause profile tid current current :=
  ⟨[], .nil, by simp, by simp only [List.append_nil]⟩

theorem Pause.step {profile : Profile} {tid : Nat} {before : State}
    {history : Log} {action : Action} {result : State × Observation}
    (quiet : passive tid action) (origin : Origin before action result profile) :
    Pause profile tid (before, history)
      (result.1, history ++ [⟨before, action, result⟩]) := by
  refine ⟨[⟨before, action, result⟩],
    OriginTrace.cons (tick := ⟨before, action, result⟩) origin .nil, ?_, rfl⟩
  intro tick member
  have same := List.mem_singleton.mp member
  subst tick
  exact quiet

theorem Pause.trans {profile : Profile} {tid : Nat} {before middle after : State × Log}
    (first : Pause profile tid before middle) (second : Pause profile tid middle after) :
    Pause profile tid before after := by
  obtain ⟨front, firstTrace, firstQuiet, firstLog⟩ := first
  obtain ⟨back, secondTrace, secondQuiet, secondLog⟩ := second
  refine ⟨front ++ back, firstTrace.append secondTrace, ?_, ?_⟩
  · intro tick member
    rcases List.mem_append.mp member with old | new
    · exact firstQuiet tick old
    · exact secondQuiet tick new
  · rw [secondLog, firstLog, List.append_assoc]

/-- Authenticity is transported, never inferred from the pause alone. -/
theorem Pause.authentic {profile : Profile} {tid : Nat} {initial : State}
    {before after : State × Log} (paused : Pause profile tid before after)
    (priorTrace : OriginTrace profile initial before.2 before.1) :
    OriginTrace profile initial after.2 after.1 := by
  obtain ⟨suffix, trace, _quiet, same⟩ := paused
  rw [same]
  exact priorTrace.append trace

/-- Universal closure under all native passive origins from the current state. -/
def Box (profile : Profile) (tid : Nat) (P : State → Log → Prop)
    (state : State) (history : Log) : Prop :=
  ∀ after extended, Pause profile tid (state, history) (after, extended) → P after extended

theorem Box.here {profile : Profile} {tid : Nat} {P : State → Log → Prop}
    {state : State} {history : Log} (closed : Box profile tid P state history) :
    P state history :=
  closed state history Pause.refl

theorem Box.stable {profile : Profile} {tid : Nat} {P : State → Log → Prop}
    {before after : State} {history extended : Log}
    (closed : Box profile tid P before history)
    (paused : Pause profile tid (before, history) (after, extended)) :
    Box profile tid P after extended := by
  intro final later following
  exact closed final later (paused.trans following)

/-- A successful passive schedule yields a pause with all original actions
and observations in order. This theorem only extracts production origins;
it defines no scheduler or instruction evaluator and needs no future run. -/
theorem Pause.of_schedule {profile : Profile} {tid : Nat} {before after : State}
    {actions : List Action} {observations : List Observation}
    (actual : TSO64.schedule before actions profile = .ok (after, observations))
    (only : ∀ action ∈ actions, passive tid action) (history : Log) :
    ∃ suffix, Pause profile tid (before, history) (after, history ++ suffix) ∧
      suffix.map Tick.action = actions ∧
      suffix.map (fun tick => tick.result.2) = observations := by
  induction actions generalizing before after observations history with
  | nil =>
    have same : (before, []) = (after, observations) := Except.ok.inj actual
    have afterEq : before = after := congrArg Prod.fst same
    have observationsEq : [] = observations := congrArg Prod.snd same
    subst after
    subst observations
    refine ⟨[], ?_, rfl, rfl⟩
    simpa only [List.append_nil] using
      (Pause.refl (profile := profile) (tid := tid) (current := (before, history)))
  | cons action rest ih =>
    obtain ⟨⟨middle, observation⟩, ⟨last, seen⟩, stepped, scheduled, same⟩ :=
      schedule_cons_ok actual
    let tick : Tick := ⟨before, action, (middle, observation)⟩
    have edge : Pause profile tid (before, history) (middle, history ++ [tick]) :=
      Pause.step (only action List.mem_cons_self) (step_origin stepped)
    have restOnly : ∀ next ∈ rest, passive tid next :=
      fun next member => only next (List.mem_cons_of_mem action member)
    obtain ⟨suffix, paused, actionsEq, seenEq⟩ :=
      ih (before := middle) (after := last) (observations := seen)
        (history := history ++ [tick]) scheduled restOnly
    have afterEq : after = last := congrArg Prod.fst same
    have observationsEq : observations = observation :: seen := congrArg Prod.snd same
    refine ⟨tick :: suffix, ?_, ?_, ?_⟩
    · rw [afterEq]
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using edge.trans paused
    · change action :: suffix.map Tick.action = action :: rest
      rw [actionsEq]
    · rw [observationsEq]
      change observation :: suffix.map (fun tick => tick.result.2) = observation :: seen
      rw [seenEq]

/-- Metadata/permission stability factored directly through native origins.
Published byte values need not be stable. -/
theorem origin_stable {state : State} {action : Action} {result : State × Observation}
    {profile : Profile} (origin : Origin state action result profile) :
    Stable state.world result.1.world := by
  cases origin with
  | ordinary _live _running _code _caller _fetched effect =>
    cases effect with
    | intro _supported _bounds _decoded _reads _queue _step finish =>
      cases finish <;> exact Stable.refl _
  | blocked => exact Stable.refl _
  | rmw _live _running _code _caller _fetched _bounds _empty _grant effect =>
    exact fetchAdd_stable effect.checked
  | drained _live _fifo _gate _changed effect => exact effect.stable

/-- Origin-indexed invariant transport, including the checked coupled RMW and
both native publication cases. No executable step converse is used. -/
theorem origin_wellFormed {state : State} {action : Action} {result : State × Observation}
    {profile : Profile} (origin : Origin state action result profile)
    (valid : WellFormed state profile) : WellFormed result.1 profile := by
  cases origin with
  | ordinary live _running _code _caller _fetched effect => exact effect.wellFormed valid live
  | blocked => exact valid
  | rmw live _running _code _caller _fetched _bounds _empty _grant effect =>
    have workerValid := valid.2 _ (List.mem_of_getElem? live)
    have frame := fetchAdd_stable effect.checked
    exact install_valid valid frame (effect.wellFormed valid.1)
      ⟨frame.resources workerValid.1,
        fun pending member => frame.pending (workerValid.2 pending member)⟩
  | drained live fifo _gate changed effect =>
    have workerValid := valid.2 _ (List.mem_of_getElem? live)
    have frame := effect.stable
    apply install_valid valid frame (changed.wellFormed valid.1)
    refine ⟨frame.resources workerValid.1, ?_⟩
    intro pending member
    exact frame.pending (workerValid.2 pending
      (by rw [fifo]; exact List.mem_cons_of_mem _ member))

/-- All executable bytes survive every origin, independently of worker RIP. -/
theorem origin_code {state : State} {action : Action} {result : State × Observation}
    {profile : Profile} (origin : Origin state action result profile)
    {base : Word} {bytes : List Byte} (code : CodeAt (published state.world) base bytes) :
    CodeAt (published result.1.world) base bytes := by
  cases origin with
  | ordinary _live _running _lease _caller _fetched effect =>
    cases effect with
    | intro _supported _bounds _decoded _reads _queue _step finish =>
      cases finish <;> exact code
  | blocked => exact code
  | rmw _live _running _lease _caller _fetched _bounds _empty _grant effect =>
    have preserved := effect.preserves_all_code base bytes code
    rw [effect.memory] at preserved
    exact preserved
  | drained _live _fifo gate _changed effect =>
    dsimp only [install]
    rw [effect.projection]
    exact dataOnly_preserves_code gate.dataOnly code

/-- The retained part of a subject worker across passive interference.
Pending entries and reconstructed memory are intentionally absent. -/
structure SavedFrame (before after : Worker) : Prop where
  context : after.context = before.context
  phase : after.phase = before.phase
  resources : after.resources = before.resources
  nextStore : after.nextStore = before.nextStore

theorem SavedFrame.refl (worker : Worker) : SavedFrame worker worker := ⟨rfl, rfl, rfl, rfl⟩

theorem SavedFrame.trans {before middle after : Worker}
    (first : SavedFrame before middle) (second : SavedFrame middle after) : SavedFrame before after :=
  ⟨second.context.trans first.context, second.phase.trans first.phase,
    second.resources.trans first.resources, second.nextStore.trans first.nextStore⟩

private theorem install_drain_saved {state : State} {owner tid : Nat} {world : World}
    {subject prior : Worker} {tail : List Pending}
    (subjectLive : state.workers[owner]? = some subject)
    (priorLive : state.workers[tid]? = some prior) :
    ∃ current, (install state owner world { subject with pending := tail }).workers[tid]? =
      some current ∧ SavedFrame prior current := by
  by_cases same : tid = owner
  · subst tid
    have priorEq : prior = subject := Option.some.inj (priorLive.symm.trans subjectLive)
    subst prior
    exact ⟨{ subject with pending := tail },
      List.getElem?_set_self (List.getElem_of_getElem? subjectLive).1, ⟨rfl, rfl, rfl, rfl⟩⟩
  · exact ⟨prior, (install_peer same).trans priorLive, .refl _⟩

/-- Passive native origins preserve the subject's saved context, phase,
original resource identity and occurrence counter. This includes own drains
with returned phase; no running or empty-FIFO assumption occurs. -/
theorem origin_saved {state : State} {action : Action} {result : State × Observation}
    {profile : Profile} {tid : Nat} {prior : Worker}
    (origin : Origin state action result profile) (quiet : passive tid action)
    (live : state.workers[tid]? = some prior) :
    ∃ current, result.1.workers[tid]? = some current ∧ SavedFrame prior current := by
  cases origin with
  | ordinary _subjectLive _running _code _caller _fetched effect =>
    cases effect with
    | intro _supported _bounds _decoded _reads _queue _step finish =>
      cases finish <;> exact ⟨prior, (install_peer (Ne.symm quiet)).trans live, .refl _⟩
  | blocked => exact ⟨prior, live, .refl _⟩
  | rmw => exact ⟨prior, (install_peer (Ne.symm quiet)).trans live, .refl _⟩
  | drained subjectLive _fifo _gate _changed _effect => exact install_drain_saved subjectLive live

theorem OriginTrace.wellFormed {profile : Profile} {initial final : State} {history : Log}
    (trace : OriginTrace profile initial history final) :
    WellFormed initial profile → WellFormed final profile := by
  induction trace with
  | nil => exact id
  | cons head _ ih => intro valid; exact ih (origin_wellFormed head valid)

theorem OriginTrace.code {profile : Profile} {initial final : State} {history : Log}
    (trace : OriginTrace profile initial history final) {base : Word} {bytes : List Byte} :
    CodeAt (published initial.world) base bytes → CodeAt (published final.world) base bytes := by
  induction trace with
  | nil => exact id
  | cons head _ ih => intro code; exact ih (origin_code head code)

theorem OriginTrace.passive_saved {profile : Profile} {tid : Nat}
    {initial final : State} {history : Log} (trace : OriginTrace profile initial history final) :
    (∀ tick ∈ history, passive tid tick.action) →
    ∀ {prior : Worker}, initial.workers[tid]? = some prior →
      ∃ current, final.workers[tid]? = some current ∧ SavedFrame prior current := by
  induction trace with
  | nil => intro _quiet prior live; exact ⟨prior, live, .refl _⟩
  | cons head _ ih =>
    intro quiet prior live
    obtain ⟨middle, middleLive, first⟩ := origin_saved head (quiet _ List.mem_cons_self) live
    obtain ⟨current, currentLive, second⟩ :=
      ih (fun tick member => quiet tick (List.mem_cons_of_mem _ member)) middleLive
    exact ⟨current, currentLive, first.trans second⟩

theorem Pause.wellFormed {profile : Profile} {tid : Nat} {before after : State × Log}
    (paused : Pause profile tid before after) (valid : WellFormed before.1 profile) :
    WellFormed after.1 profile := by
  obtain ⟨_suffix, trace, _quiet, _same⟩ := paused
  exact trace.wellFormed valid

theorem Pause.code {profile : Profile} {tid : Nat} {before after : State × Log}
    (paused : Pause profile tid before after) {base : Word} {bytes : List Byte}
    (code : CodeAt (published before.1.world) base bytes) :
    CodeAt (published after.1.world) base bytes := by
  obtain ⟨_suffix, trace, _quiet, _same⟩ := paused
  exact trace.code code

theorem Pause.saved {profile : Profile} {tid : Nat} {before after : State × Log}
    {prior : Worker} (paused : Pause profile tid before after)
    (live : before.1.workers[tid]? = some prior) :
    ∃ current, after.1.workers[tid]? = some current ∧ SavedFrame prior current := by
  obtain ⟨_suffix, trace, quiet, _same⟩ := paused
  exact trace.passive_saved quiet live

end EDSL.OS.TSO64.EffectSimulation

#print axioms EDSL.OS.TSO64.EffectSimulation.OriginTrace.at
#print axioms EDSL.OS.TSO64.EffectSimulation.Pause.refl
#print axioms EDSL.OS.TSO64.EffectSimulation.Pause.step
#print axioms EDSL.OS.TSO64.EffectSimulation.Pause.trans
#print axioms EDSL.OS.TSO64.EffectSimulation.Pause.authentic
#print axioms EDSL.OS.TSO64.EffectSimulation.Box.here
#print axioms EDSL.OS.TSO64.EffectSimulation.Box.stable
#print axioms EDSL.OS.TSO64.EffectSimulation.Pause.of_schedule
#print axioms EDSL.OS.TSO64.EffectSimulation.origin_stable
#print axioms EDSL.OS.TSO64.EffectSimulation.origin_wellFormed
#print axioms EDSL.OS.TSO64.EffectSimulation.origin_code
#print axioms EDSL.OS.TSO64.EffectSimulation.origin_saved
#print axioms EDSL.OS.TSO64.EffectSimulation.Pause.wellFormed
#print axioms EDSL.OS.TSO64.EffectSimulation.Pause.code
#print axioms EDSL.OS.TSO64.EffectSimulation.Pause.saved
#audit_edsl
