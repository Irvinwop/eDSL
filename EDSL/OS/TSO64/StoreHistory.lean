/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.Run

namespace EDSL.OS.TSO64.StoreHistory
open X86

/-- An exact tagged queue entry at one scheduler thread. Neither the stored
value nor the numerical occurrence bound substitutes for this membership. -/
def Queued (state : State) (tid : Nat) (entry : Pending) : Prop :=
  ∃ worker, state.workers[tid]? = some worker ∧ entry ∈ worker.pending

/-- A real successful ordinary store issue. The original entry is retained
through the current admission and the committed FIFO/counter update. The
instruction, both decode results, prestate operands and actual machine effect
are available through `effect`, `fetched` and `intent`. -/
inductive Issued (state : State) (action : Action) (result : State × Observation)
    (profile : Profile) (tid : Nat) (entry : Pending) : Prop where
  | ordinary {af : Bool} {worker : Worker} {instruction : Sequential.Instruction}
      {store : Store} {observation : Sequential.Observation}
      (issuing : action = .issue tid af)
      (success : step state action profile = .ok result)
      (live : state.workers[tid]? = some worker)
      (fetched : decode (fetchCPU state worker) = .ok (.ordinary instruction))
      (effect : OrdinaryEffect state tid worker instruction af result profile)
      (intent : storeIntent instruction (localCPU state worker) = some store)
      (admission : Queue.Admission state.world worker.resources store worker.nextStore profile entry)
      (committed : FinishEffect state tid worker (worker.pending ++ [entry]) observation
        result (worker.nextStore + 1)) :
      Issued state action result profile tid entry

/-- A managed tag carries the counter from its actual issuing prestate. This
fact is obtained from the real admission, rather than from a later queue bound. -/
theorem Issued.managed_occurrence {state : State} {action : Action}
    {result : State × Observation} {profile : Profile} {tid : Nat}
    {reference : Queue.ManagedRef} {value : Word} {occurrence : Nat}
    (issued : Issued state action result profile tid (.managed reference value occurrence)) :
    ∃ worker, state.workers[tid]? = some worker ∧ occurrence = worker.nextStore := by
  cases issued with
  | ordinary issuing success live fetched effect intent admission committed =>
      exact ⟨_, live, admission.managed_occurrence rfl⟩

private theorem queued_install_iff {state : State} {tid : Nat} {world : World}
    {prior replacement : Worker} {entry : Pending}
    (live : state.workers[tid]? = some prior) :
    Queued (install state tid world replacement) tid entry ↔ entry ∈ replacement.pending := by
  have installed : (install state tid world replacement).workers[tid]? = some replacement :=
    List.getElem?_set_self (List.getElem_of_getElem? live).1
  constructor
  · rintro ⟨worker, current, member⟩
    have same : worker = replacement := Option.some.inj (current.symm.trans installed)
    subst worker
    exact member
  · intro member
    exact ⟨replacement, installed, member⟩

private theorem finish_pending {state : State} {tid : Nat} {worker : Worker}
    {pending : List Pending} {observation : Sequential.Observation}
    {result : State × Observation} {nextStore : Nat} {entry : Pending}
    (live : state.workers[tid]? = some worker)
    (finish : FinishEffect state tid worker pending observation result nextStore)
    (queued : Queued result.1 tid entry) : entry ∈ pending := by
  cases finish <;> exact (queued_install_iff live).mp queued

/-- Every successful action either retains an exact entry at the same thread,
or actually enqueues it through that thread's decoded ordinary store issue.
No reachability, authority invariant or empty-initial-queue premise is needed. -/
theorem step_pending_origin {state : State} {action : Action} {result : State × Observation}
    {profile : Profile} {tid : Nat} {entry : Pending}
    (success : step state action profile = .ok result)
    (queued : Queued result.1 tid entry) :
    Queued state tid entry ∨ Issued state action result profile tid entry := by
  cases action with
  | issue issuer af =>
      by_cases same : tid = issuer
      · subst tid
        obtain ⟨worker, live, _running, _code, _caller, instruction, fetched, effect⟩ :=
          issue_effect (profile := profile) success
        cases instruction with
        | ordinary instruction =>
            have actualEffect := effect
            cases effect with
            | intro supported bounds decoded reads queue executed finish =>
                have member := finish_pending live finish queued
                cases queue with
                | unchanged intent => exact .inl ⟨worker, live, member⟩
                | enqueued intent admission =>
                    rcases List.mem_append.mp member with old | fresh
                    · exact .inl ⟨worker, live, old⟩
                    · have equal := List.mem_singleton.mp fresh
                      subst entry
                      exact .inr (.ordinary rfl success live fetched actualEffect intent admission finish)
        | locked instruction =>
            cases effect with
            | blocked => exact .inl queued
            | rmw bounds empty decoded selected changed executed =>
                have remaining := (queued_install_iff live).mp queued
                exact .inl ⟨worker, live, remaining⟩
      · rcases queued with ⟨worker, live, member⟩
        have unchanged := step_peer (profile := profile) success same
        exact .inl ⟨worker, unchanged.symm.trans live, member⟩
  | drain issuer =>
      by_cases same : tid = issuer
      · subst tid
        obtain ⟨worker, head, tail, output, live, fifo, _gate, _changed, resultEq⟩ :=
          drain_effect (profile := profile) success
        have remaining : entry ∈ tail := by
          rw [resultEq] at queued
          exact (queued_install_iff live).mp queued
        refine .inl ⟨worker, live, ?_⟩
        rw [fifo]
        exact List.mem_cons_of_mem head remaining
      · rcases queued with ⟨worker, live, member⟩
        have unchanged := step_peer (profile := profile) success same
        exact .inl ⟨worker, unchanged.symm.trans live, member⟩

/-- A store issue at a real position of an actual schedule. Each constructor
retains the actual next step and suffix run, including their observations.
This is a proof annotation of the existing executor, not another executor. -/
inductive IssuedIn (profile : Profile) (tid : Nat) (entry : Pending) :
    State → List Action → (State × List Observation) → Prop where
  | head {state : State} {action : Action} {rest : List Action}
      {first : State × Observation} {tail : State × List Observation}
      (stepped : step state action profile = .ok first)
      (following : schedule first.1 rest profile = .ok tail)
      (issued : Issued state action first profile tid entry) :
      IssuedIn profile tid entry state (action :: rest) (tail.1, first.2 :: tail.2)
  | later {state : State} {action : Action} {rest : List Action}
      {first : State × Observation} {tail : State × List Observation}
      (stepped : step state action profile = .ok first)
      (following : schedule first.1 rest profile = .ok tail)
      (issued : IssuedIn profile tid entry first.1 rest tail) :
      IssuedIn profile tid entry state (action :: rest) (tail.1, first.2 :: tail.2)

/-- The issue annotation describes a successful run of precisely its indexed
actions and observation list. -/
theorem IssuedIn.scheduled {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {tid : Nat} {entry : Pending}
    (history : IssuedIn profile tid entry state actions result) :
    schedule state actions profile = .ok result := by
  cases history with
  | head stepped following issued => simp [schedule, stepped, following]
  | later stepped following issued => simp [schedule, stepped, following]

/-- The boundary alternative retains the original tag and original thread of
an arbitrary nonempty initial FIFO. It does not invent an earlier issue. -/
def Origin (initial : State) (actions : List Action) (result : State × List Observation)
    (profile : Profile) (tid : Nat) (entry : Pending) : Prop :=
  Queued initial tid entry ∨ IssuedIn profile tid entry initial actions result

/-- Every final pending entry is either an exact initial-boundary entry at the
same scheduler thread or has a real successful store issue in this schedule. -/
theorem schedule_pending_origin {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {tid : Nat} {entry : Pending}
    (success : schedule state actions profile = .ok result)
    (queued : Queued result.1 tid entry) : Origin state actions result profile tid entry := by
  induction actions generalizing state result with
  | nil =>
      have same : (state, []) = result := Except.ok.inj success
      subst result
      exact .inl queued
  | cons action rest ih =>
      obtain ⟨first, tail, stepped, following, same⟩ := schedule_cons_ok (profile := profile) success
      have finalQueued : Queued tail.1 tid entry := by simpa only [same] using queued
      rcases ih following finalQueued with boundary | issued
      · rcases step_pending_origin stepped boundary with initial | current
        · exact .inl initial
        · right
          rw [same]
          exact .head stepped following current
      · right
        rw [same]
        exact .later stepped following issued

/-- Empty setup eliminates the arbitrary initial boundary. Every surviving
tag, including a managed tag with a repeated value, has an actual issue. -/
theorem schedule_pending_issued {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {tid : Nat} {entry : Pending}
    (empty : Quiescent state)
    (success : schedule state actions profile = .ok result)
    (queued : Queued result.1 tid entry) : IssuedIn profile tid entry state actions result := by
  rcases schedule_pending_origin success queued with boundary | issued
  · rcases boundary with ⟨worker, live, member⟩
    have none := empty worker (List.mem_of_getElem? live)
    rw [none] at member
    cases member
  · exact issued

/-- The tag actually published after a prefix run has the same exact
initial-boundary-or-real-issue origin. Publication cannot replace it with an
equal-valued store, a different descriptor or another thread's queue entry. -/
theorem drain_after_schedule_origin {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {tid : Nat} {entry : Pending}
    {after : State}
    (success : schedule state actions profile = .ok result)
    (drained : drain result.1 tid profile = .ok (after, .drained tid entry)) :
    Origin state actions result profile tid entry := by
  obtain ⟨worker, head, tail, output, live, fifo, _gate, _changed, same⟩ :=
    drain_effect (profile := profile) drained
  have equal : entry = head := by
    have tags : some entry = some head := congrArg
      (fun pair : State × Observation => match pair.2 with
        | .drained _ original => some original
        | _ => none) same
    exact Option.some.inj tags
  apply schedule_pending_origin success
  refine ⟨worker, live, ?_⟩
  rw [equal, fifo]
  exact List.mem_cons_self

/-- A managed drain retains the complete original descriptor, full word and
occurrence as its origin tag. There is no value-based writer reconstruction. -/
theorem managed_drain_after_schedule_origin {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {tid : Nat}
    {reference : Queue.ManagedRef} {value : Word} {occurrence : Nat} {after : State}
    (success : schedule state actions profile = .ok result)
    (drained : drain result.1 tid profile =
      .ok (after, .drained tid (.managed reference value occurrence))) :
    Origin state actions result profile tid (.managed reference value occurrence) :=
  drain_after_schedule_origin success drained

/-- With an empty initial boundary, an actually published entry was issued by
this same scheduler thread during the supplied prefix. -/
theorem drain_after_schedule_issued {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {tid : Nat} {entry : Pending}
    {after : State} (empty : Quiescent state)
    (success : schedule state actions profile = .ok result)
    (drained : drain result.1 tid profile = .ok (after, .drained tid entry)) :
    IssuedIn profile tid entry state actions result := by
  rcases drain_after_schedule_origin success drained with boundary | issued
  · rcases boundary with ⟨worker, live, member⟩
    have none := empty worker (List.mem_of_getElem? live)
    rw [none] at member
    cases member
  · exact issued

end EDSL.OS.TSO64.StoreHistory
