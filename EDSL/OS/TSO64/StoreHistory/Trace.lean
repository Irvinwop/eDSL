/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.StoreHistory.Indexed

set_option autoImplicit false

namespace EDSL.OS.TSO64.StoreHistory.Trace
open X86

/-- One actual store issue at an action position. The complete original queue
entry retains ordinary authority or a managed descriptor, value and occurrence.
Positions count all actions, including drains and blocked attempts. -/
structure Issue where
  position : Nat
  tid : Nat
  entry : Pending
  deriving DecidableEq, Repr

/-- A computed prestate classification, never an input to execution. This
alone does not certify success: a later check or machine operation may fail.
Locked instructions, drains, failed lookups/decodes/admissions and nonstores
produce no candidate. Both ordinary and managed admissions are retained. -/
def capture (state : State) (action : Action) (profile : Profile := .ownedOnly) :
    Option (Nat × Pending) :=
  match action with
  | .drain _ => none
  | .issue tid _ =>
      match state.workers[tid]? with
      | none => none
      | some worker =>
          match decode (fetchCPU state worker) with
          | .error _ | .ok (.locked _) => none
          | .ok (.ordinary instruction) =>
              match storeIntent instruction (localCPU state worker) with
              | none => none
              | some store =>
                  match Queue.admit state.world worker.resources store worker.nextStore profile with
                  | .error _ => none
                  | .ok entry => some (tid, entry)

/-- The converse of admission extraction follows from its actual lookup
fields, including the ordinary-grant priority and explicit managed profile. -/
private theorem admission_complete {world : World} {resources : Resources} {store : Store}
    {occurrence : Nat} {profile : Profile} {entry : Pending}
    (admission : Queue.Admission world resources store occurrence profile entry) :
    Queue.admit world resources store occurrence profile = .ok entry := by
  cases admission with
  | ordinary ticket selected => simp only [Queue.admit, selected]
  | managed reference value ordinaryAbsent shared qword selected =>
      simp only [Queue.admit, ordinaryAbsent, shared, qword, selected]

/-- Actual admission and commit cannot be omitted by the classifier. In
particular this covers ordinary entries as well as managed store occurrences. -/
theorem capture_complete {state : State} {action : Action} {result : State × Observation}
    {profile : Profile} {tid : Nat} {entry : Pending}
    (issued : Issued state action result profile tid entry) :
    capture state action profile = some (tid, entry) := by
  cases issued with
  | ordinary issuing success live fetched effect intent admission committed =>
      subst action
      simp only [capture, live, fetched, intent, admission_complete admission]

/-- A candidate becomes an actual issue only under a real successful step.
The witness comes from production dispatch, its queue effect and its committed
finish effect; no classification-correctness premise is supplied by a caller. -/
theorem capture_sound {state : State} {action : Action} {result : State × Observation}
    {profile : Profile} {tid : Nat} {entry : Pending}
    (success : step state action profile = .ok result)
    (captured : capture state action profile = some (tid, entry)) :
    Issued state action result profile tid entry := by
  cases action with
  | drain issuer => simp only [capture, reduceCtorEq] at captured
  | issue issuer af =>
      obtain ⟨worker, live, _running, _code, _caller, instruction, fetched, effect⟩ :=
        issue_effect (profile := profile) success
      cases instruction with
      | locked instruction => simp only [capture, live, fetched, reduceCtorEq] at captured
      | ordinary instruction =>
          have actualEffect := effect
          cases effect with
          | intro supported bounds decoded reads queue executed finish =>
              cases queue with
              | unchanged intent =>
                  simp only [capture, live, fetched, intent, reduceCtorEq] at captured
              | enqueued intent admission =>
                  have actual : Issued state (.issue issuer af) result profile issuer _ :=
                    .ordinary rfl success live fetched actualEffect intent admission finish
                  have same := Option.some.inj (captured.symm.trans (capture_complete actual))
                  obtain ⟨sameTid, sameEntry⟩ := Prod.mk.inj same
                  subst tid
                  cases sameEntry
                  exact actual

/-- Exact classification of a successful production step. Success is essential:
`capture` does not replace any executor check. -/
theorem capture_iff_issued {state : State} {action : Action} {result : State × Observation}
    {profile : Profile} {tid : Nat} {entry : Pending}
    (success : step state action profile = .ok result) :
    capture state action profile = some (tid, entry) ↔
      Issued state action result profile tid entry :=
  ⟨capture_sound success, capture_complete⟩

/-- The scheduler's final state and observations with computed store issues. -/
structure Result where
  state : State
  observations : List Observation
  issues : List Issue

/-- Erase only the annotation, retaining the actual state and observations. -/
def Result.execution (result : Result) : State × List Observation :=
  (result.state, result.observations)

private def record (position : Nat) (captured : Option (Nat × Pending))
    (issues : List Issue) : List Issue :=
  match captured with
  | none => issues
  | some emitted => ⟨position, emitted.1, emitted.2⟩ :: issues

private theorem record_mem {position : Nat} {captured : Option (Nat × Pending)}
    {issues : List Issue} {issue : Issue} :
    issue ∈ record position captured issues ↔
      (∃ emitted, captured = some emitted ∧
        issue = ⟨position, emitted.1, emitted.2⟩) ∨ issue ∈ issues := by
  cases captured with
  | none => simp [record]
  | some emitted =>
      simp only [record, List.mem_cons]
      constructor
      · rintro (same | member)
        · exact .inl ⟨emitted, rfl, same⟩
        · exact .inr member
      · rintro (⟨other, equal, same⟩ | member)
        · have samePair := Option.some.inj equal
          subst other
          exact .inl same
        · exact .inr member

/-- Instrument the existing scheduler, propagating its exact first fault.
Capture uses the original prestate and is recorded only after the production
step and recursive suffix succeed. The running offset avoids shifting a suffix
list at each action. No instruction executor or supplied origin oracle is used. -/
def scan (state : State) (actions : List Action) (profile : Profile := .ownedOnly)
    (offset : Nat := 0) : Except Fault Result :=
  match actions with
  | [] => .ok ⟨state, [], []⟩
  | action :: rest => do
      let first ← step state action profile
      let tail ← scan first.1 rest profile (offset + 1)
      return ⟨tail.state, first.2 :: tail.observations,
        record offset (capture state action profile) tail.issues⟩

/-- Erasure is exactly the real scheduler, including its error result. -/
theorem scan_execution (state : State) (actions : List Action) (profile : Profile)
    (offset : Nat) :
    (scan state actions profile offset).map Result.execution = schedule state actions profile := by
  induction actions generalizing state offset with
  | nil => rfl
  | cons action rest ih =>
      cases stepped : step state action profile with
      | error fault => simp [scan, schedule, stepped, Except.map]
      | ok first =>
          have tailExecution := ih first.1 (offset + 1)
          cases following : scan first.1 rest profile (offset + 1) with
          | error fault =>
              have scheduled : schedule first.1 rest profile = .error fault := by
                simpa only [following, Except.map] using tailExecution.symm
              simp [scan, schedule, stepped, following, scheduled, Except.map]
          | ok tail =>
              have scheduled : schedule first.1 rest profile = .ok tail.execution := by
                simpa only [following, Except.map] using tailExecution.symm
              simp [scan, schedule, stepped, following, scheduled, Except.map, Result.execution]

/-- Every successful scan retains exactly an actual schedule's state and
observation list, without any extra execution assumptions. -/
theorem scan_scheduled {state : State} {actions : List Action} {profile : Profile}
    {offset : Nat} {result : Result}
    (success : scan state actions profile offset = .ok result) :
    schedule state actions profile = .ok result.execution := by
  have execution := scan_execution state actions profile offset
  rw [success] at execution
  exact execution.symm

/-- Instrumentation neither invents nor masks faults, including their exact
constructors and payloads. It also cannot fail when the real schedule succeeds. -/
theorem scan_error_iff (state : State) (actions : List Action) (profile : Profile)
    (offset : Nat) (fault : Fault) :
    scan state actions profile offset = .error fault ↔
      schedule state actions profile = .error fault := by
  rw [← scan_execution state actions profile offset]
  cases scan state actions profile offset <;> simp [Except.map]

private theorem scan_cons_ok {state : State} {action : Action} {rest : List Action}
    {profile : Profile} {offset : Nat} {result : Result}
    (success : scan state (action :: rest) profile offset = .ok result) :
    ∃ first tail, step state action profile = .ok first ∧
      scan first.1 rest profile (offset + 1) = .ok tail ∧
      result = ⟨tail.state, first.2 :: tail.observations,
        record offset (capture state action profile) tail.issues⟩ := by
  cases stepped : step state action profile with
  | error fault => simp [scan, stepped] at success
  | ok first =>
      cases following : scan first.1 rest profile (offset + 1) with
      | error fault => simp [scan, stepped, following] at success
      | ok tail =>
          simp [scan, stepped, following] at success
          exact ⟨first, tail, rfl, following, success.symm⟩

/-- Every computed issue has an actual indexed issue at precisely its offset
plus action index. The witness retains the complete entry and successful run. -/
theorem scan_sound {state : State} {actions : List Action} {profile : Profile}
    {offset : Nat} {result : Result} {issue : Issue}
    (success : scan state actions profile offset = .ok result)
    (member : issue ∈ result.issues) :
    ∃ index, issue.position = offset + index ∧
      IssuedAt profile issue.tid issue.entry index state actions result.execution := by
  induction actions generalizing state result offset with
  | nil =>
      have same : (⟨state, [], []⟩ : Result) = result := Except.ok.inj success
      subst result
      cases member
  | cons action rest ih =>
      obtain ⟨first, tail, stepped, following, same⟩ := scan_cons_ok success
      have scheduled := scan_scheduled following
      have selected : issue ∈ record offset (capture state action profile) tail.issues := by
        simpa only [same] using member
      rcases record_mem.mp selected with ⟨⟨tid, entry⟩, captured, equal⟩ | later
      · subst issue
        refine ⟨0, rfl, ?_⟩
        rw [same]
        exact .head stepped scheduled (capture_sound stepped captured)
      · obtain ⟨index, position, actual⟩ := ih following later
        refine ⟨index + 1, ?_, ?_⟩
        · omega
        · rw [same]
          exact .later stepped scheduled actual

/-- Conversely every actual indexed store issue is computed. The actual run
may be supplied with any result: deterministic real steps identify its prefix
with the successful scan. No entry or origin list is supplied to `scan`. -/
theorem scan_complete {state : State} {actions : List Action} {profile : Profile}
    {offset : Nat} {result : Result} {execution : State × List Observation}
    {tid index : Nat} {entry : Pending}
    (success : scan state actions profile offset = .ok result)
    (issued : IssuedAt profile tid entry index state actions execution) :
    (⟨offset + index, tid, entry⟩ : Issue) ∈ result.issues := by
  induction issued generalizing offset result with
  | head actualStep actualFollowing actual =>
      obtain ⟨first, tail, stepped, following, same⟩ := scan_cons_ok success
      have equal := Except.ok.inj (actualStep.symm.trans stepped)
      cases equal
      rw [same]
      apply record_mem.mpr
      exact .inl ⟨(tid, entry), capture_complete actual, rfl⟩
  | later actualStep actualFollowing actual ih =>
      obtain ⟨first, tail, stepped, following, same⟩ := scan_cons_ok success
      have equal := Except.ok.inj (actualStep.symm.trans stepped)
      cases equal
      rw [same]
      apply record_mem.mpr
      right
      have member := ih following
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using member

/-- Exact membership rules out both invented issues and silent omission of
successful stores. Offsets count actions rather than observations or stores. -/
theorem scan_issues_iff {state : State} {actions : List Action} {profile : Profile}
    {offset : Nat} {result : Result} {issue : Issue}
    (success : scan state actions profile offset = .ok result) :
    issue ∈ result.issues ↔
      ∃ index, issue.position = offset + index ∧
        IssuedAt profile issue.tid issue.entry index state actions result.execution := by
  constructor
  · exact scan_sound success
  · rintro ⟨index, atPosition, actual⟩
    rcases issue with ⟨position, tid, entry⟩
    change position = offset + index at atPosition
    subst position
    exact scan_complete success actual

/-- Every issue position belongs to the original action interval. -/
theorem scan_bounds {state : State} {actions : List Action} {profile : Profile}
    {offset : Nat} {result : Result} {issue : Issue}
    (success : scan state actions profile offset = .ok result)
    (member : issue ∈ result.issues) :
    offset ≤ issue.position ∧ issue.position < offset + actions.length := by
  obtain ⟨index, position, actual⟩ := scan_sound success member
  have bound := actual.bound
  omega

/-- A successful scan emits issues in strictly increasing action order. This
also rules out duplicate copies of an otherwise valid issue annotation. -/
theorem scan_issues_ordered {state : State} {actions : List Action} {profile : Profile}
    {offset : Nat} {result : Result}
    (success : scan state actions profile offset = .ok result) :
    result.issues.Pairwise (fun first second => first.position < second.position) := by
  induction actions generalizing state result offset with
  | nil =>
      have same : (⟨state, [], []⟩ : Result) = result := Except.ok.inj success
      subst result
      exact .nil
  | cons action rest ih =>
      obtain ⟨first, tail, stepped, following, same⟩ := scan_cons_ok success
      rw [same]
      cases captured : capture state action profile with
      | none => simpa only [record, captured] using ih following
      | some emitted =>
          simp only [record]
          apply List.pairwise_cons.mpr
          constructor
          · intro issue member
            have bounds := scan_bounds following member
            exact Nat.lt_of_lt_of_le (Nat.lt_succ_self offset) bounds.1
          · exact ih following

theorem scan_issues_nodup {state : State} {actions : List Action} {profile : Profile}
    {offset : Nat} {result : Result}
    (success : scan state actions profile offset = .ok result) : result.issues.Nodup := by
  apply List.nodup_iff_pairwise_ne.mpr
  exact (scan_issues_ordered success).imp (fun less same => by
    rw [same] at less
    exact Nat.lt_irrefl _ less)

/-- A successful annotation certificate contains the real execution and an
exact, complete account of ordinary and managed store issues. It makes no
load-source, RMW-source or source-language memory-order assertion. -/
structure Certificate (initial : State) (actions : List Action) (profile : Profile)
    (offset : Nat) (result : Result) : Prop where
  scheduled : schedule initial actions profile = .ok result.execution
  ordered : result.issues.Pairwise (fun first second => first.position < second.position)
  issues : ∀ issue, issue ∈ result.issues ↔
    ∃ index, issue.position = offset + index ∧
      IssuedAt profile issue.tid issue.entry index initial actions result.execution

/-- The certificate follows from scan success alone. The caller supplies no
legal-history oracle, issue witnesses or classification-correctness premise. -/
theorem scan_certificate {state : State} {actions : List Action} {profile : Profile}
    {offset : Nat} {result : Result}
    (success : scan state actions profile offset = .ok result) :
    Certificate state actions profile offset result :=
  ⟨scan_scheduled success, scan_issues_ordered success, fun _ => scan_issues_iff success⟩

end EDSL.OS.TSO64.StoreHistory.Trace
