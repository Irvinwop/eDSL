/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.FetchAddClaims
import EDSL.Corpus.V1.FetchAddResources

set_option warningAsError true
set_option autoImplicit false

/-!
Inhabitants of the fixed concurrent certificate for the unchanged GCC/Clang
ELF functions. The universal contract is the reusable checked-family theorem;
this module separately supplies loaded resources and an actual overlapping
completed execution with nonzero inputs. No corpus registry is modified here.
-/

namespace EDSL.Corpus.V1.FetchAddCertificates
open X86 OS Concurrency

abbrev Compiler := FetchAddWindows.Compiler

/-- Only an actual observation of the selected thread and cell is retained. -/
def selected (target : Atomics64.CellId64) (tid : Nat) :
    Option TSO64.Observation → Option Atomics64.FetchAddEvent
  | some (.rmw thread event) =>
      if thread = tid ∧ event.cell = target then some event else none
  | _ => none

theorem selected_sound {target : Atomics64.CellId64} {tid : Nat}
    {observation : Option TSO64.Observation} {event : Atomics64.FetchAddEvent}
    (found : selected target tid observation = some event) :
    observation = some (.rmw tid event) ∧ event.cell = target := by
  cases observation with
  | none => cases found
  | some observation =>
    cases observation with
    | rmw thread actual =>
      by_cases chosen : thread = tid ∧ actual.cell = target
      · simp only [selected, ite_eq_left chosen, Option.some.injEq] at found
        subst actual
        exact ⟨by rw [chosen.1], chosen.2⟩
      · simp [selected, chosen] at found
    | ordinary | returned | blocked | drained => cases found

/-- A check on the real scheduler result. It cannot manufacture an execution
or observation, and it checks every actual worker's returned phase. -/
def overlapCheck (target : Atomics64.CellId64) (i j k : Nat)
    (result : Except TSO64.Fault (TSO64.State × List TSO64.Observation)) : Bool :=
  match result with
  | .error _ => false
  | .ok actual =>
      actual.1.workers.all (fun worker => decide (worker.phase = .returned)) &&
      (selected target 0 actual.2[i]?).isSome &&
      (selected target 1 actual.2[j]?).isSome &&
      decide (actual.2[k]? = some (.returned 0))

theorem overlapCheck_sound {target : Atomics64.CellId64} {i j k : Nat}
    {state : TSO64.State} {actions : List TSO64.Action}
    (accepted : overlapCheck target i j k (TSO64.schedule state actions) = true) :
    ∃ (actual : TSO64.State × List TSO64.Observation)
      (first second : Atomics64.FetchAddEvent),
      TSO64.schedule state actions = .ok actual ∧ TSO64.Returned actual.1 ∧
      actual.2[i]? = some (.rmw 0 first) ∧ actual.2[j]? = some (.rmw 1 second) ∧
      actual.2[k]? = some (.returned 0) ∧ first.cell = target ∧ second.cell = target := by
  cases success : TSO64.schedule state actions with
  | error fault => simp [overlapCheck, success] at accepted
  | ok actual =>
    have facts := accepted
    simp only [overlapCheck, success, Bool.and_eq_true, decide_eq_true_eq] at facts
    cases first : selected target 0 actual.2[i]? with
    | none => simp [first] at facts
    | some eventA =>
      cases second : selected target 1 actual.2[j]? with
      | none => simp [second] at facts
      | some eventB =>
        have a := selected_sound first
        have b := selected_sound second
        refine ⟨actual, eventA, eventB, rfl, ?_, a.1, b.1, facts.2, a.2, b.2⟩
        intro worker member
        exact of_decide_eq_true ((List.all_eq_true.mp facts.1.1.1) worker member)

/-- Both calls reach the RMW before the first returns. GCC retains its actual
ENDBR64 issue for each participant under the recorded CET-off assumption. -/
def actions : Compiler → List TSO64.Action
  | .defaultGCC => [.issue 0 false, .issue 1 false, .issue 0 false, .issue 1 false,
      .issue 0 false, .issue 1 false, .issue 1 false, .issue 0 false]
  | .defaultClang => [.issue 0 false, .issue 1 false, .issue 0 false,
      .issue 1 false, .issue 1 false, .issue 0 false]

def firstIndex : Compiler → Nat | .defaultGCC => 4 | .defaultClang => 2
def secondIndex : Compiler → Nat | .defaultGCC => 5 | .defaultClang => 3
def returnIndex : Compiler → Nat | .defaultGCC => 7 | .defaultClang => 5

/-- The kernel checks the actual modeled execution, rather than native code. -/
theorem overlap_checked (compiler : Compiler) :
    overlapCheck FetchAddResources.target (firstIndex compiler) (secondIndex compiler)
      (returnIndex compiler)
      (TSO64.schedule (FetchAddResources.current compiler 17 1 2).state (actions compiler)) = true := by
  cases compiler <;> fetch_add_kernel_rfl

/-- Independent admission of the two actual initial contexts. -/
theorem pre (compiler : Compiler) :
    Grading.ConcurrentTask.FetchAdd64.Pre (Concurrent.Image (FetchAddWindows.input compiler))
      (FetchAddResources.current compiler 17 1 2) [1, 2] := by
  refine ⟨FetchAddResources.workers_length compiler 17 1 2, ?_⟩
  intro tid
  rcases tid with ⟨tid, bound⟩
  have choices : tid = 0 ∨ tid = 1 := by change tid < 2 at bound; omega
  rcases choices with rfl | rfl
  · exact FetchAddResources.gate compiler 17 1 2 0 (0 : Nat)
  · exact FetchAddResources.gate compiler 17 1 2 1 (1 : Nat)

/-- Original caller disjointness covers all distinct actual context indices. -/
theorem privateCallers (compiler : Compiler) (i j : Nat)
    (first second : TSO64.Worker) (distinct : i ≠ j)
    (firstLive : (FetchAddResources.current compiler 17 1 2).state.workers[i]? = some first)
    (secondLive : (FetchAddResources.current compiler 17 1 2).state.workers[j]? = some second) :
    Ownership.Disjoint first.resources.caller.loan.region second.resources.caller.loan.region := by
  have iBound : i < 2 := by
    rw [← FetchAddResources.workers_length compiler 17 1 2]
    exact (List.getElem_of_getElem? firstLive).1
  have jBound : j < 2 := by
    rw [← FetchAddResources.workers_length compiler 17 1 2]
    exact (List.getElem_of_getElem? secondLive).1
  have firstEq : first = FetchAddResources.worker compiler 17 1 2 ⟨i, iBound⟩ :=
    Option.some.inj (firstLive.symm.trans (FetchAddResources.worker_live compiler 17 1 2 ⟨i, iBound⟩))
  have secondEq : second = FetchAddResources.worker compiler 17 1 2 ⟨j, jBound⟩ :=
    Option.some.inj (secondLive.symm.trans (FetchAddResources.worker_live compiler 17 1 2 ⟨j, jBound⟩))
  rw [firstEq, secondEq]
  have iChoices : i = 0 ∨ i = 1 := by omega
  have jChoices : j = 0 ∨ j = 1 := by omega
  rcases iChoices with rfl | rfl <;> rcases jChoices with rfl | rfl
  · exact False.elim (distinct rfl)
  · exact (FetchAddResources.private_callers compiler 17 1 2).1
  · exact Ownership.disjoint_symm (FetchAddResources.private_callers compiler 17 1 2).1
  · exact False.elim (distinct rfl)

/-- Concrete useful resources retain the complete checked ELF installation.
The stored trace is completed and overlaps on the same selected cell. -/
def loaded (compiler : Compiler) : Concurrent.LoadedFetchAddBatch
    (FetchAddWindows.file compiler) FetchAddWindows.name (FetchAddWindows.input compiler) where
  priorSpace := AddressSpace.empty
  loaded := FetchAddResources.installed compiler
  admitted := FetchAddResources.admitted compiler
  target := FetchAddResources.target
  cell := FetchAddResources.cell
  before := FetchAddResources.current compiler 17 1 2
  deltas := [1, 2]
  pre := pre compiler
  initialValue := 17
  initialRead := FetchAddResources.initial_read compiler 17 1 2
  text := FetchAddResources.text compiler 17 1 2
  retainedImage := fun _ _ present => FetchAddResources.full_image compiler 17 1 2 present
  population := by decide
  useful := by
    intro tid
    rcases tid with ⟨tid, bound⟩
    have choices : tid = 0 ∨ tid = 1 := by omega
    rcases choices with rfl | rfl
    · exact ⟨1, rfl, by decide⟩
    · exact ⟨2, rfl, by decide⟩
  privateCallers := privateCallers compiler
  interleaving := by
    obtain ⟨actual, first, second, success, done, a, b, returned, targetA, targetB⟩ :=
      overlapCheck_sound (overlap_checked compiler)
    refine ⟨actions compiler, actual, firstIndex compiler, secondIndex compiler, returnIndex compiler,
      first, second, success, done, ?_, ?_, a, b, returned, targetA, targetB⟩
    · cases compiler <;> decide
    · cases compiler <;> decide

/-- Exact-file certificates combine one reusable universal checked-code Claim
with genuine loaded resources and their same actual overlapping trace. -/
def certificate (compiler : Compiler) : Concurrent.FetchAddCertificate
    (FetchAddWindows.file compiler) FetchAddWindows.name where
  input := FetchAddWindows.input compiler
  checked := FetchAddWindows.checked compiler
  claim := FetchAddClaims.claim compiler
  inhabited := ⟨loaded compiler⟩

#print axioms overlapCheck_sound
#print axioms overlap_checked
#print axioms pre
#print axioms privateCallers
#print axioms loaded
#print axioms certificate

end EDSL.Corpus.V1.FetchAddCertificates

#audit_edsl
