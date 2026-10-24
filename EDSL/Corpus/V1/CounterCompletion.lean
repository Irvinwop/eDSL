/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.CounterRanks
import EDSL.Corpus.V1.CounterFrame
import EDSL.Corpus.V1.CounterRetirement
import EDSL.OS.TSO64.EffectSimulation.Mixed.RankedCohort

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Finite execution of independently admitted frozen counter workers. Compiler
selection supplies every local rule, rank law and initial invariant. The
initial worker list fixes the complete scheduler-slot universe; initially
empty queues and the owned-only profile remain explicit environmental inputs.

The common ranked engine constructs an actual returning schedule for arbitrary
per-thread AF choices. The two-worker adapter composes that same execution with
the independent counter total, byte frame and production resource retirement.
No future successful schedule, returned state, desired result or fairness
assumption is supplied. The action bound counts model issues, not minimum
hardware operations. These model theorems establish neither native refinement
nor a whole-program or whole-corpus admission.
-/

namespace EDSL.Corpus.V1.CounterCommon
open X86 OS OS.TSO64 OS.TSO64.EffectSimulation

/-- Current compiler admission selects its complete local rules. -/
def checkedRules {c : Compiler} {site : Site c} {call : Call} {initial : S}
    (pre : Pre site call initial) : Mixed.LocalRules (descriptor site call) (Post site call) := by
  cases c with
  | defaultGCC => exact CounterGCC.rules site call pre.callerCanonical
  | defaultClang => exact CounterClang.rules site call pre.callerCanonical pre.stack

/-- The corresponding checked rank laws use the same exact local rules. -/
def checkedRankLaws {c : Compiler} {site : Site c} {call : Call} {initial : S}
    (pre : Pre site call initial) : Mixed.RankLaws (checkedRules pre) := by
  cases c with
  | defaultGCC => exact CounterGCC.rankLaws pre
  | defaultClang => exact CounterClang.rankLaws pre

/-- Both frozen windows begin at their independently checked node zero. -/
def checkedInitialNode {c : Compiler} (site : Site c) (call : Call) :
    (descriptor site call).graph.Index := by
  cases c with
  | defaultGCC => exact (⟨0, by decide +kernel⟩ : CounterGCC.Index)
  | defaultClang => exact (0 : CounterClang.Index)

/-- Independent present admission initializes the exact selected local rules. -/
theorem checkedRules_entry {c : Compiler} {site : Site c} {call : Call} {initial : S}
    (pre : Pre site call initial) :
    Mixed.Entry (checkedRules pre).annotations initial (checkedInitialNode site call) := by
  cases c with
  | defaultGCC => exact CounterGCC.entry_of_pre pre
  | defaultClang => exact CounterClang.entry_of_pre pre

/-- Finite ranked subjects cover exact physical scheduler slots. Compilers may
be selected independently when all present admissions hold in the same state. -/
def counterRankedCohort {n : Nat} {initial : S}
    (subjects : Fin n → CohortSubject initial)
    (slots : ∀ i : Fin n, (subjects i).site.tid = i.val) :
    Mixed.RankedCohort n .ownedOnly .arithmetic where
  descriptor i := descriptor (subjects i).site (subjects i).call
  post i := Post (subjects i).site (subjects i).call
  rules i := checkedRules (subjects i).pre
  rankLaws i := checkedRankLaws (subjects i).pre
  profile_eq i := (subjects i).ownedOnly
  family_eq _i := rfl
  tid_eq := slots
  callerPolicy i state := descriptor_policy (subjects i).site (subjects i).call state

/-- Exact initial ghosts use the independent entry nodes and empty histories. -/
def counterInitialGhosts {n : Nat} {initial : S}
    (subjects : Fin n → CohortSubject initial)
    (slots : ∀ i : Fin n, (subjects i).site.tid = i.val) :
    (counterRankedCohort subjects slots).Ghosts initial :=
  fun i => Mixed.initialGhost (descriptor (subjects i).site (subjects i).call)
    initial (Post (subjects i).site (subjects i).call)
    (checkedInitialNode (subjects i).site (subjects i).call)

/-- The initial every-node invariants follow from present Pre, not a residual
projected from a future execution. -/
theorem counterInitialGhosts_current {n : Nat} {initial : S}
    (subjects : Fin n → CohortSubject initial)
    (slots : ∀ i : Fin n, (subjects i).site.tid = i.val) :
    (counterRankedCohort subjects slots).Current initial (counterInitialGhosts subjects slots) := by
  intro i
  exact (checkedRules (subjects i).pre).localRelated_initial
    (checkedRules_entry (subjects i).pre)

/-- Construct an actual finite returned execution, with exact lifted histories,
per-thread AF choices, retirement labels and the finite rank issue upper bound.
Explicit initial validity also covers the empty worker universe. -/
theorem counterCohort_complete {n : Nat} {initial : S}
    (subjects : Fin n → CohortSubject initial)
    (slots : ∀ i : Fin n, (subjects i).site.tid = i.val)
    (valid : WellFormed initial .ownedOnly) (workerUniverse : initial.workers.length = n)
    (empty : Quiescent initial) (choices : Nat → Nat → Bool) :
    Nonempty ((counterRankedCohort subjects slots).Suffix (before := initial)
      (counterInitialGhosts subjects slots) choices (fun _ => 0)) :=
  (counterRankedCohort subjects slots).complete valid workerUniverse
    (counterInitialGhosts_current subjects slots) empty choices

/-- The finite two-slot collection retains the two independent admissions. -/
def twoCounterSubjects {leftCompiler rightCompiler : Compiler}
    {left : Site leftCompiler} {right : Site rightCompiler} {leftCall rightCall : Call}
    {initial : S} (leftPre : Pre left leftCall initial) (rightPre : Pre right rightCall initial)
    (leftProfile : left.profile = .ownedOnly) (rightProfile : right.profile = .ownedOnly) :
    Fin 2 → CohortSubject initial :=
  fun i => if i.val = 0 then ⟨leftCompiler, left, leftCall, leftPre, leftProfile⟩
    else ⟨rightCompiler, right, rightCall, rightPre, rightProfile⟩

/-- Exact independent slots authenticate the complete two-worker universe. -/
theorem twoCounterSubjects_slots {leftCompiler rightCompiler : Compiler}
    {left : Site leftCompiler} {right : Site rightCompiler} {leftCall rightCall : Call}
    {initial : S} (leftPre : Pre left leftCall initial) (rightPre : Pre right rightCall initial)
    (leftProfile : left.profile = .ownedOnly) (rightProfile : right.profile = .ownedOnly)
    (leftSlot : left.tid = 0) (rightSlot : right.tid = 1) :
    ∀ i : Fin 2,
      (twoCounterSubjects leftPre rightPre leftProfile rightProfile i).site.tid = i.val := by
  intro i
  by_cases atLeft : i.val = 0
  · unfold twoCounterSubjects
    rw [ite_eq_left atLeft]
    exact leftSlot.trans atLeft.symm
  · have atRight : i.val = 1 := by have bound := i.isLt; omega
    unfold twoCounterSubjects
    rw [ite_eq_right atLeft]
    exact rightSlot.trans atRight.symm

/-- One constructed returning schedule, its independent modular sum and its
byte frame. The result retains the complete ranked execution certificate. -/
theorem two_complete_total_frame {leftCompiler rightCompiler : Compiler}
    {left : Site leftCompiler} {right : Site rightCompiler} {leftCall rightCall : Call}
    {initial : S}
    (leftPre : Pre left leftCall initial) (rightPre : Pre right rightCall initial)
    (leftProfile : left.profile = .ownedOnly) (rightProfile : right.profile = .ownedOnly)
    (leftSlot : left.tid = 0) (rightSlot : right.tid = 1)
    (workerUniverse : initial.workers.length = 2) (empty : Quiescent initial)
    (choices : Nat → Nat → Bool)
    (target : Atomics64.CellId64) (cell : Atomics64.Cell)
    (registered : initial.world.cells target = some cell)
    (leftTarget : leftCall.target = target) (rightTarget : rightCall.target = target)
    (prior : Word) (readBefore : loadQWord (published initial.world) cell.address = .ok prior) :
    let subjects := twoCounterSubjects leftPre rightPre leftProfile rightProfile
    let slots := twoCounterSubjects_slots leftPre rightPre leftProfile rightProfile leftSlot rightSlot
    ∃ suffix : (counterRankedCohort subjects slots).Suffix (before := initial)
        (counterInitialGhosts subjects slots) choices (fun _ => 0),
      ∃ value, loadQWord (published suffix.final.world) cell.address = .ok value ∧
        value.toNat =
          (prior.toNat + leftCall.iterations.toNat + rightCall.iterations.toNat) % 2^64 ∧
        ∀ query : Word, 8 ≤ (query - cell.address).toNat →
          (published suffix.final.world).read query = (published initial.world).read query := by
  intro subjects slots
  have valid : WellFormed initial .ownedOnly := by
    simpa only [descriptor, leftProfile] using leftPre.admitted.wellFormed
  obtain ⟨suffix⟩ := counterCohort_complete subjects slots valid workerUniverse empty choices
  have leftBound : left.tid < suffix.final.workers.length := by
    rw [leftSlot, suffix.finalWorkers]
    decide
  have rightBound : right.tid < suffix.final.workers.length := by
    rw [rightSlot, suffix.finalWorkers]
    decide
  have leftLive : suffix.final.workers[left.tid]? =
      some (suffix.final.workers[left.tid]'leftBound) := List.getElem?_eq_getElem leftBound
  have rightLive : suffix.final.workers[right.tid]? =
      some (suffix.final.workers[right.tid]'rightBound) := List.getElem?_eq_getElem rightBound
  obtain ⟨value, readAfter, total, frame⟩ := two_completed_total_frame leftPre rightPre
    leftProfile rightProfile leftSlot rightSlot workerUniverse empty suffix.actual leftLive rightLive
    (suffix.returned _ (List.mem_of_getElem? leftLive))
    (suffix.returned _ (List.mem_of_getElem? rightLive)) target cell registered
    leftTarget rightTarget prior readBefore
  exact ⟨suffix, value, readAfter, total, frame⟩

/-- Construct the same finite returning execution and then execute production
resource retirement. The cleaned world keeps its current RAM, counter result,
outside-byte frame, resource store and cell registry. The added inputs describe
only the original cleanup shapes and resource separation. -/
theorem two_complete_retired_total_frame {leftCompiler rightCompiler : Compiler}
    {left : Site leftCompiler} {right : Site rightCompiler} {leftCall rightCall : Call}
    {initial : S}
    (leftPre : Pre left leftCall initial) (rightPre : Pre right rightCall initial)
    (leftProfile : left.profile = .ownedOnly) (rightProfile : right.profile = .ownedOnly)
    (leftSlot : left.tid = 0) (rightSlot : right.tid = 1)
    (workerUniverse : initial.workers.length = 2) (empty : Quiescent initial)
    (leftShape : CleanupShape left) (rightShape : CleanupShape right)
    (separate : initial.workers.reverse.Pairwise
      (fun retiring peer => Lifecycle.Separate retiring.resources peer.resources))
    (choices : Nat → Nat → Bool)
    (target : Atomics64.CellId64) (cell : Atomics64.Cell)
    (registered : initial.world.cells target = some cell)
    (leftTarget : leftCall.target = target) (rightTarget : rightCall.target = target)
    (prior : Word) (readBefore : loadQWord (published initial.world) cell.address = .ok prior) :
    let subjects := twoCounterSubjects leftPre rightPre leftProfile rightProfile
    let slots := twoCounterSubjects_slots leftPre rightPre leftProfile rightProfile leftSlot rightSlot
    ∃ suffix : (counterRankedCohort subjects slots).Suffix (before := initial)
        (counterInitialGhosts subjects slots) choices (fun _ => 0),
      ∃ result value,
        Lifecycle.retireAll suffix.final = .ok result ∧ WellFormed result.1 .ownedOnly ∧
        result.1.workers = [] ∧ result.2 = suffix.final.workers.reverse.map Worker.context ∧
        result.1.world.legacy.shared.resources = suffix.final.world.legacy.shared.resources ∧
        result.1.world.cells = suffix.final.world.cells ∧
        published result.1.world = published suffix.final.world ∧
        (∃ labels, Atomics64.History suffix.final.world labels result.1.world) ∧
        (∀ worker ∈ suffix.final.workers, Lifecycle.WorkerRevoked result.1.world worker) ∧
        loadQWord (published result.1.world) cell.address = .ok value ∧
        value.toNat =
          (prior.toNat + leftCall.iterations.toNat + rightCall.iterations.toNat) % 2^64 ∧
        ∀ query : Word, 8 ≤ (query - cell.address).toNat →
          (published result.1.world).read query = (published initial.world).read query := by
  intro subjects slots
  obtain ⟨suffix, _value, _readAfter, _total, frame⟩ := two_complete_total_frame leftPre rightPre
    leftProfile rightProfile leftSlot rightSlot workerUniverse empty choices target cell registered
    leftTarget rightTarget prior readBefore
  have leftBound : left.tid < suffix.final.workers.length := by
    rw [leftSlot, suffix.finalWorkers]
    decide
  have rightBound : right.tid < suffix.final.workers.length := by
    rw [rightSlot, suffix.finalWorkers]
    decide
  have leftLive : suffix.final.workers[left.tid]? =
      some (suffix.final.workers[left.tid]'leftBound) := List.getElem?_eq_getElem leftBound
  have rightLive : suffix.final.workers[right.tid]? =
      some (suffix.final.workers[right.tid]'rightBound) := List.getElem?_eq_getElem rightBound
  obtain ⟨result, cleanedValue, success, cleanedValid, workers, contexts, resources, cells,
      ram, history, revoked, cleanedRead, cleanedTotal⟩ :=
    two_completed_retired_total leftPre rightPre leftProfile rightProfile leftSlot rightSlot
      workerUniverse empty leftShape rightShape separate suffix.actual leftLive rightLive
      (suffix.returned _ (List.mem_of_getElem? leftLive))
      (suffix.returned _ (List.mem_of_getElem? rightLive)) target cell registered
      leftTarget rightTarget prior readBefore
  refine ⟨suffix, result, cleanedValue, success, cleanedValid, workers, contexts, resources, cells,
    ram, history, revoked, cleanedRead, cleanedTotal, ?_⟩
  intro query outside
  rw [ram]
  exact frame query outside

#print axioms checkedRules
#print axioms checkedRankLaws
#print axioms checkedInitialNode
#print axioms checkedRules_entry
#print axioms counterRankedCohort
#print axioms counterInitialGhosts
#print axioms counterInitialGhosts_current
#print axioms counterCohort_complete
#print axioms twoCounterSubjects
#print axioms twoCounterSubjects_slots
#print axioms two_complete_total_frame
#print axioms two_complete_retired_total_frame

end EDSL.Corpus.V1.CounterCommon

#audit_edsl
