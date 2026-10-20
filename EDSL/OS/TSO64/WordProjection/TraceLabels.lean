/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.WordProjection.Simulation

/-!
Computable annotation of the existing checked executor. These functions do not
execute reference transitions, alter machine execution, compare postconditions
or admit code by a second semantics. Ordinary annotations inspect the actual
prestate request, authority selector and load; locked/publication annotations
inspect the actual checked observation. `scheduleLabels` traverses the existing
`step` function and propagates its failures unchanged.
-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.WordProjection
open X86 Concurrency

/-- Annotate an ordinary instruction's actual managed-memory effect. Admission
is the existing OS admission function. Ordinary grants are erased; only its
actual managed admission yields a write label. A managed read uses the selected
current descriptor and the actual local qword load. -/
def ordinaryLabels (state : TSO64.State) (tid : Nat) (worker : Worker)
    (instruction : Sequential.Instruction) (profile : Profile := .ownedOnly) :
    List ReferenceLabel :=
  match storeIntent instruction (localCPU state worker) with
  | some store =>
      match Queue.admit state.world worker.resources store worker.nextStore profile with
      | .ok (.managed reference value _) => [.write tid reference.handle.cell value]
      | _ => []
  | none =>
      match instruction with
      | .loadMem64 _ address =>
          match atomicFor state.world worker.resources (address.eval (localCPU state worker)) with
          | some (_, handle, cell) =>
              match loadQWord (localCPU state worker).memory cell.address with
              | .ok value => [.read tid handle.cell value]
              | .error _ => []
          | none => []
      | _ => []

/-- Annotate the ordinary instruction fetched from this actual worker's
prestate. Invalid indices, failed decodes and locked instructions yield no
ordinary labels; successful-step theorems exclude those cases where needed. -/
def issueLabels (state : TSO64.State) (tid : Nat) (profile : Profile := .ownedOnly) :
    List ReferenceLabel :=
  match state.workers[tid]? with
  | none => []
  | some worker =>
      match decode (fetchCPU state worker) with
      | .ok (.ordinary instruction) => ordinaryLabels state tid worker instruction profile
      | _ => []

/-- Annotate the actual observation. A checked RMW expands to five labels;
a managed publication contributes one Tau; blocked and ordinary publications
are erased. Ordinary/return observations use the actual prestate instruction. -/
def stepLabels (state : TSO64.State) (observation : Observation)
    (profile : Profile := .ownedOnly) : List ReferenceLabel :=
  match observation with
  | .ordinary tid | .returned tid => issueLabels state tid profile
  | .rmw tid event =>
      [.lock tid, .read tid event.cell event.arithmetic.event.before,
        .write tid event.cell event.arithmetic.event.after, .tau, .unlock tid]
  | .drained _ (.managed _ _ _) => [.tau]
  | .drained _ (.ordinary _ _) | .blocked _ => []

/-- Traverse the existing checked step function, appending annotations only.
This accessor preserves the first actual executor failure and does not run a
reference-model executor or add a criterion for successful execution. -/
def scheduleLabels (state : TSO64.State) (actions : List Action)
    (profile : Profile := .ownedOnly) : Except Fault (List ReferenceLabel) :=
  match actions with
  | [] => .ok []
  | action :: rest => do
      let result ← step state action profile
      let following ← scheduleLabels result.1 rest profile
      return stepLabels state result.2 profile ++ following

private theorem admission_checked {world : World} {resources : Resources} {store : Store}
    {occurrence : Nat} {profile : Profile} {entry : Pending}
    (admission : Queue.Admission world resources store occurrence profile entry) :
    Queue.admit world resources store occurrence profile = .ok entry := by
  cases admission with
  | ordinary ticket selected => exact Queue.admit_ordinary _ _ selected
  | managed reference value absent shared qword selected =>
    subst profile
    exact Queue.admit_managed _ absent qword selected

/-- Computational ordinary annotations agree with every constrained ordinary
trace. The quiet case's selector-absence premise prevents a managed MOV64 from
being silently erased even when it leaves the projected endpoint unchanged. -/
theorem OrdinaryTrace.labels {state : TSO64.State} {tid : Nat} {worker : Worker}
    {instruction : Sequential.Instruction} {result : TSO64.State × Observation}
    {profile : Profile} {labels : List ReferenceLabel}
    (trace : OrdinaryTrace state tid worker instruction result profile labels) :
    ordinaryLabels state tid worker instruction profile = labels := by
  cases trace with
  | quiet intent erasable same =>
    simp only [ordinaryLabels, intent]
    cases instruction <;> try rfl
    case loadMem64 destination address =>
      simp only [erasable destination address rfl]
  | owned store ticket intent admission same =>
    simp only [ordinaryLabels, intent, admission_checked admission]
  | managed store reference value occurrence intent admission same =>
    simp only [ordinaryLabels, intent, admission_checked admission]
  | load destination address reference value decoded selected loaded same =>
    subst instruction
    simp only [ordinaryLabels, storeIntent, Sequential.Instruction.storeIntent64,
      Sequential.Instruction.storeIntent, Option.map_none, selected, loaded]

/-- Computable annotations agree with every actual-step classification, using
the actual fetched instruction and ordinary finish result rather than guessing
which kind of observation an instruction ought to produce. -/
theorem StepTrace.labels {state : TSO64.State} {action : Action}
    {result : TSO64.State × Observation} {profile : Profile} {labels : List ReferenceLabel}
    (trace : StepTrace state action result profile labels) :
    stepLabels state result.2 profile = labels := by
  cases trace with
  | ordinary success live fetched effect classified =>
    have annotated := classified.labels
    cases effect with
    | intro supported bounds decoded reads queue executed finish =>
      cases finish <;> simpa only [stepLabels, issueLabels, live, fetched] using annotated
  | blocked success => rfl
  | ordinaryDrain success => rfl
  | managedDrain success => rfl
  | rmw success => rfl

/-- Classified schedules carry exactly the computationally extracted labels.
The proof traverses their real successful steps, preserving action order. -/
theorem ScheduleTrace.labels {profile : Profile} {state : TSO64.State}
    {actions : List Action} {result : TSO64.State × List Observation}
    {labels : List ReferenceLabel}
    (trace : ScheduleTrace profile state actions result labels) :
    scheduleLabels state actions profile = .ok labels := by
  induction trace with
  | nil => rfl
  | cons stepped scheduled ih =>
    simp only [scheduleLabels, stepped.success, ok_bind, ih, stepped.labels, pure_ok]

/-- The existing schedule's computational annotations always succeed and
retain both per-action classification and reference-path soundness. -/
theorem schedule_labels {state : TSO64.State} {actions : List Action}
    {result : TSO64.State × List Observation} {profile : Profile}
    (valid : WellFormed state profile)
    (success : schedule state actions profile = .ok result) :
    ∃ labels, scheduleLabels state actions profile = .ok labels ∧
      ScheduleTrace profile state actions result labels ∧
      TSOWord.Path (project state) labels (project result.1) := by
  obtain ⟨labels, trace, path⟩ := schedule_trace valid success
  exact ⟨labels, trace.labels, trace, path⟩

/-- Bind a computed label list to the actual checked schedule and its general
refinement theorem. Clients need only evaluate the unchanged scheduler and its
annotation accessor, rather than hand-constructing a proof for each program. -/
theorem schedule_labels_sound {state : TSO64.State} {actions : List Action}
    {result : TSO64.State × List Observation} {profile : Profile}
    {labels : List ReferenceLabel}
    (valid : WellFormed state profile)
    (success : schedule state actions profile = .ok result)
    (annotated : scheduleLabels state actions profile = .ok labels) :
    ScheduleTrace profile state actions result labels ∧
      TSOWord.Path (project state) labels (project result.1) := by
  obtain ⟨actual, trace, path⟩ := schedule_trace valid success
  have same : actual = labels := Except.ok.inj (trace.labels.symm.trans annotated)
  subst actual
  exact ⟨trace, path⟩

end EDSL.OS.TSO64.WordProjection
