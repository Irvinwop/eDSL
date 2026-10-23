/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.EffectSimulation.Passive

/-!
Original-resource and protected-loan frames indexed by actual native origins.
Every originally live worker remains at its original index with its complete
resource record, including across its own ordinary, blocked, RMW and drain
origins. Current authority follows from current WF. Loan reads retain their
original borrower, identifier and address.

The proofs factor the native origin constructors directly. They need no
Origin-to-step converse, initial empty queue, running phase or RSP equality.
Protected loan bytes are separate from shared writable data; no RAM or whole
CPU frame is asserted for the latter. These laws cover only the current
scheduler action set, which has no resource allocation or revocation action.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.OS.TSO64.EffectSimulation
open X86 AddressSpace

private theorem install_resources_at {state : State} {owner tid : Nat} {world : World}
    {subject replacement prior : Worker}
    (subjectLive : state.workers[owner]? = some subject)
    (priorLive : state.workers[tid]? = some prior)
    (retained : replacement.resources = subject.resources) :
    ∃ current, (install state owner world replacement).workers[tid]? = some current ∧
      current.resources = prior.resources := by
  by_cases same : tid = owner
  · subst tid
    have priorEq : prior = subject := Option.some.inj (priorLive.symm.trans subjectLive)
    subst prior
    exact ⟨replacement, List.getElem?_set_self (List.getElem_of_getElem? subjectLive).1,
      retained⟩
  · exact ⟨prior, (install_peer same).trans priorLive, rfl⟩

/-- Every originally live index retains its complete original resources.
The current worker is obtained from the actual origin's installed state. -/
theorem origin_resources {state : State} {action : Action} {result : State × Observation}
    {profile : Profile} (origin : Origin state action result profile)
    {tid : Nat} {prior : Worker} (live : state.workers[tid]? = some prior) :
    ∃ current, result.1.workers[tid]? = some current ∧ current.resources = prior.resources := by
  cases origin with
  | ordinary subjectLive _running _code _caller _fetched effect =>
    cases effect with
    | intro _supported _bounds _decoded _reads _queue _step finish =>
      cases finish <;> exact install_resources_at subjectLive live rfl
  | blocked => exact ⟨prior, live, rfl⟩
  | rmw subjectLive _running _code _caller _fetched _bounds _empty _grant _effect =>
    exact install_resources_at subjectLive live rfl
  | drained subjectLive _fifo _gate _changed _effect =>
    exact install_resources_at subjectLive live rfl

/-- Original identity is bound to a worker at the same current index, whose
resources are valid in the actual successor world under the same profile. -/
theorem origin_current_resources {state : State} {action : Action}
    {result : State × Observation} {profile : Profile}
    (origin : Origin state action result profile) (valid : WellFormed state profile)
    {tid : Nat} {prior : Worker} (live : state.workers[tid]? = some prior) :
    ∃ current, result.1.workers[tid]? = some current ∧ current.resources = prior.resources ∧
      ResourcesValid result.1.world current.resources := by
  obtain ⟨current, currentLive, retained⟩ := origin_resources origin live
  exact ⟨current, currentLive, retained,
    ((origin_wellFormed origin valid).2 current (List.mem_of_getElem? currentLive)).1⟩

/-- Every byte in any live loan survives each actual native origin. Ordinary
and blocked origins leave the world unchanged; RMW and drain origins supply
their checked OS effects, including either kind of tagged publication. -/
theorem origin_loan_contents {state : State} {action : Action}
    {result : State × Observation} {profile : Profile}
    (origin : Origin state action result profile) (valid : WellFormed state profile)
    {identifier : Nat} {loan : Borrowing.Loan}
    (live : state.world.legacy.shared.loans identifier = some loan) (address : Word)
    (inside : loan.region.Contains address) :
    result.1.world.legacy.shared.resources.space.cells address =
      state.world.legacy.shared.resources.space.cells address := by
  cases origin with
  | ordinary _subjectLive _running _code _caller _fetched effect =>
    cases effect with
    | intro _supported _bounds _decoded _reads _queue _step finish => cases finish <;> rfl
  | blocked => rfl
  | rmw _subjectLive _running _code _caller _fetched _bounds _empty _grant effect =>
    exact Atomics64.fetchAdd_loan_contents _ _ _ _ _ valid.1 effect.checked
      identifier loan live address inside
  | drained _subjectLive _fifo _gate changed _effect =>
    exact changed.loan_contents valid.1 identifier loan live address inside

/-- Transport a real full-width borrowing read at the original identity and
address. Authorization, loan confinement and all eight published bytes are
retained; no current stack-pointer equality is needed or established. -/
theorem origin_loan_read_preserved {state : State} {action : Action}
    {result : State × Observation} {profile : Profile}
    (origin : Origin state action result profile) (valid : WellFormed state profile)
    {borrower identifier : Nat} {address value : Word}
    (read : Borrowing.loadWord64 state.world.legacy.shared borrower identifier address = .ok value) :
    Borrowing.loadWord64 result.1.world.legacy.shared borrower identifier address = .ok value := by
  obtain ⟨loan, authority, fits, observed⟩ := Borrowing.loadWord64_ok _ _ _ _ _ read
  obtain ⟨live, owns⟩ := Borrowing.authorize_ok _ _ _ _ authority
  have stable := origin_stable origin
  have finalAuthority : Borrowing.authorize result.1.world.legacy.shared borrower identifier = .ok loan := by
    simp [Borrowing.authorize, stable.loans, live, owns]
  apply Borrowing.loadWord64_success _ _ _ _ _ loan finalAuthority fits
  apply (loadQWord_congr _ _ _ ?_).trans observed
  intro offset bound
  have loanValid := (valid.1.legacy.shared.2 identifier loan live).2
  obtain ⟨_, _, _, _, _, regionValid, _⟩ := loanValid
  exact (AddressSpace.toMemory_agrees_at _ _ _
    (origin_loan_contents origin valid live _
      (Borrowing.qword_inside loan regionValid address fits offset bound))).1

/-- Complete original resource identity along an authentic native prefix,
without any passive-only restriction on its own issues. -/
theorem OriginTrace.resources {profile : Profile} {tid : Nat}
    {initial final : State} {history : Log} (trace : OriginTrace profile initial history final) :
    ∀ {prior : Worker}, initial.workers[tid]? = some prior →
      ∃ current, final.workers[tid]? = some current ∧ current.resources = prior.resources := by
  induction trace with
  | nil => intro prior live; exact ⟨prior, live, rfl⟩
  | cons head _ ih =>
    intro prior live
    obtain ⟨middle, middleLive, first⟩ := origin_resources head live
    obtain ⟨current, currentLive, second⟩ := ih middleLive
    exact ⟨current, currentLive, second.trans first⟩

theorem OriginTrace.current_resources {profile : Profile} {tid : Nat}
    {initial final : State} {history : Log} (trace : OriginTrace profile initial history final)
    (valid : WellFormed initial profile) {prior : Worker}
    (live : initial.workers[tid]? = some prior) :
    ∃ current, final.workers[tid]? = some current ∧ current.resources = prior.resources ∧
      ResourcesValid final.world current.resources := by
  obtain ⟨current, currentLive, retained⟩ := trace.resources live
  exact ⟨current, currentLive, retained,
    ((trace.wellFormed valid).2 current (List.mem_of_getElem? currentLive)).1⟩

/-- A fixed original borrowing read survives every connected origin prefix,
including own retirements and later publications after return. -/
theorem OriginTrace.loan_read_preserved {profile : Profile}
    {initial final : State} {history : Log} (trace : OriginTrace profile initial history final)
    {borrower identifier : Nat} {address value : Word} :
    WellFormed initial profile →
    Borrowing.loadWord64 initial.world.legacy.shared borrower identifier address = .ok value →
    Borrowing.loadWord64 final.world.legacy.shared borrower identifier address = .ok value := by
  induction trace with
  | nil => intro _valid read; exact read
  | cons head _ ih =>
    intro valid read
    exact ih (origin_wellFormed head valid) (origin_loan_read_preserved head valid read)

/-- A pause also retains the live index and complete original resource record. -/
theorem Pause.resources {profile : Profile} {tid : Nat} {before after : State × Log}
    {prior : Worker} (paused : Pause profile tid before after)
    (live : before.1.workers[tid]? = some prior) :
    ∃ current, after.1.workers[tid]? = some current ∧ current.resources = prior.resources := by
  obtain ⟨_suffix, trace, _quiet, _same⟩ := paused
  exact trace.resources live

theorem Pause.current_resources {profile : Profile} {tid : Nat} {before after : State × Log}
    {prior : Worker} (paused : Pause profile tid before after)
    (valid : WellFormed before.1 profile) (live : before.1.workers[tid]? = some prior) :
    ∃ current, after.1.workers[tid]? = some current ∧ current.resources = prior.resources ∧
      ResourcesValid after.1.world current.resources := by
  obtain ⟨_suffix, trace, _quiet, _same⟩ := paused
  exact trace.current_resources valid live

theorem Pause.loan_read_preserved {profile : Profile} {tid : Nat} {before after : State × Log}
    (paused : Pause profile tid before after) (valid : WellFormed before.1 profile)
    {borrower identifier : Nat} {address value : Word}
    (read : Borrowing.loadWord64 before.1.world.legacy.shared borrower identifier address = .ok value) :
    Borrowing.loadWord64 after.1.world.legacy.shared borrower identifier address = .ok value := by
  obtain ⟨_suffix, trace, _quiet, _same⟩ := paused
  exact trace.loan_read_preserved valid read

end EDSL.OS.TSO64.EffectSimulation

#print axioms EDSL.OS.TSO64.EffectSimulation.origin_resources
#print axioms EDSL.OS.TSO64.EffectSimulation.origin_current_resources
#print axioms EDSL.OS.TSO64.EffectSimulation.origin_loan_contents
#print axioms EDSL.OS.TSO64.EffectSimulation.origin_loan_read_preserved
#print axioms EDSL.OS.TSO64.EffectSimulation.OriginTrace.resources
#print axioms EDSL.OS.TSO64.EffectSimulation.OriginTrace.current_resources
#print axioms EDSL.OS.TSO64.EffectSimulation.OriginTrace.loan_read_preserved
#print axioms EDSL.OS.TSO64.EffectSimulation.Pause.resources
#print axioms EDSL.OS.TSO64.EffectSimulation.Pause.current_resources
#print axioms EDSL.OS.TSO64.EffectSimulation.Pause.loan_read_preserved
#audit_edsl
