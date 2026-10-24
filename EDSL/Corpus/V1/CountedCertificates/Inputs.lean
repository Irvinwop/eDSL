/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.CountedCertificate
import EDSL.Corpus.V1.CounterResources
import EDSL.Corpus.V1.CounterCounted.Claim

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Exact named inputs and independently admitted loaded counted-call batches for
both complete frozen compiler images. Original uint32 requests, upper RSI
halves and old64 are arbitrary; flags satisfy only the independent scalar
entry's clear-DF requirement. Current authority and all initial resources come
from the actual total manager setup and two successful production attachments.

The loaded bridge proves the independent Entry/Pre fields directly rather
than replacing them with the older compiler annotation admission. The existing
universal image claim then supplies chosen completion and independent modular
results without new instruction, loop or rank proofs. The two compiler cases
are separate homogeneous executions in their own exact complete ELF image.

This module supplies no useful overlapping certificate inhabitant or corpus
registration. Modeled coherent scalar RAM, protected resources, translation/
no-alias and represented CPU/CET-off assumptions remain explicit. Native joins,
physical CPU/OS, compiler correspondence, fairness, minimum cost and installed
grader support remain separate obligations.
-/

namespace EDSL.Corpus.V1.CountedCertificates
open X86 OS OS.AddressSpace OS.TSO64

abbrev Compiler := CounterCommon.Compiler

namespace Spec
abbrev Entry := Grading.ConcurrentTask.Counted64.Entry
abbrev Pre := Grading.ConcurrentTask.Counted64.Pre
abbrev Post := Grading.ConcurrentTask.Counted64.Post
abbrev Claim := Grading.ConcurrentTask.Counted64.Claim
abbrev requestedTotal {before : TSO64.State}
    (amounts : Grading.ConcurrentTask.Counted64.Requests before) :=
  Grading.ConcurrentTask.Counted64.requestedTotal amounts
end Spec

/-- The original complete file/name/input and original explicit compiler cap. -/
def named (compiler : Compiler) : Counted.NamedImage (CounterMixedGraphs.file compiler)
    CounterMixedGraphs.name (CounterMixedGraphs.caps compiler).maxBytes where
  input := CounterMixedGraphs.input compiler
  checked := CounterMixedGraphs.namedChecked compiler

/-- The exact selected original base and bytes are the universally proved image. -/
theorem named_image (compiler : Compiler) :
    (named compiler).image = CounterCounted.image compiler := rfl

/-- No copied loop proof or weakened mathematical task is used by this adapter. -/
theorem named_claim (compiler : Compiler) : Spec.Claim (named compiler).image :=
  CounterCounted.claim compiler

/-- Transport the actual finite scheduler slot using the real worker count. -/
def slot2 (compiler : Compiler) (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word)
    (slot : Fin (CounterResources.initial compiler old count upper flags).workers.length) : Fin 2 :=
  Fin.cast (CounterResources.workerUniverse2 compiler old count upper flags) slot

/-- The inverse direction preserves the physical slot value exactly. -/
def actualSlot (compiler : Compiler) (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) (slot : Fin 2) :
    Fin (CounterResources.initial compiler old count upper flags).workers.length :=
  Fin.cast (CounterResources.workerUniverse2 compiler old count upper flags).symm slot

theorem slot2_actualSlot (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word) (slot : Fin 2) :
    slot2 compiler old count upper flags (actualSlot compiler old count upper flags slot) = slot := by
  simp only [slot2, actualSlot, Fin.cast_cast, Fin.cast_refl, id_eq]

/-- Independent requests are indexed by every actual original slot. -/
def requests (compiler : Compiler) (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) :
    Grading.ConcurrentTask.Counted64.Requests (CounterResources.initial compiler old count upper flags) :=
  fun slot => count (slot2 compiler old count upper flags slot)

theorem requests_actualSlot (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word) (slot : Fin 2) :
    requests compiler old count upper flags (actualSlot compiler old count upper flags slot) =
      count slot :=
  congrArg count (slot2_actualSlot compiler old count upper flags slot)

/-- Scalar stack facts concern the actual protected caller slots. -/
private theorem stack_facts (slot : Fin 2) :
    ((CounterResources.stack slot).toNat + 8) % 16 = 0 ∧
    (CounterResources.stack slot).toNat + 8 < 2^64 ∧
    canonical (CounterResources.stack slot + 8) = true := by
  rcases slot with ⟨slot, bound⟩
  have choices : slot = 0 ∨ slot = 1 := by omega
  rcases choices with rfl | rfl
  · change ((0x700008 : Word).toNat + 8) % 16 = 0 ∧
      (0x700008 : Word).toNat + 8 < 2^64 ∧ canonical ((0x700008 : Word) + 8) = true
    decide +kernel
  · change ((0x710008 : Word).toNat + 8) % 16 = 0 ∧
      (0x710008 : Word).toNat + 8 < 2^64 ∧ canonical ((0x710008 : Word) + 8) = true
    decide +kernel

/-- The additional independent scalar admission is proved for every actual
worker and arbitrary flag bits apart from the explicitly required clear DF. -/
theorem worker_scalar (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word)
    (clear : ∀ slot, (flags slot).getLsbD 10 = false) (slot : Fin 2) :
    ScalarCall64.Entry (CounterResources.worker compiler old count upper flags slot) := by
  constructor
  · rw [CounterResources.worker_context]
    exact (stack_facts slot).1
  · rw [CounterResources.worker_flags]
    exact clear slot
  · rw [CounterResources.worker_context]
    exact (stack_facts slot).2.1
  · rw [CounterResources.worker_context]
    exact (stack_facts slot).2.2

/-- All independent entry fields are current consequences of the actual
manager and attachment outputs; no CounterCommon.Pre is substituted. -/
theorem worker_entry (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word)
    (clear : ∀ slot, (flags slot).getLsbD 10 = false) (slot : Fin 2) :
    Spec.Entry (CounterCounted.image compiler) (CounterResources.Image.resources compiler old).target
      (CounterResources.Image.resources compiler old).cell (count slot)
      (CounterResources.initial compiler old count upper flags)
      (CounterResources.worker compiler old count upper flags slot) := by
  constructor
  · rw [CounterResources.worker_view]
    rfl
  · rw [CounterResources.worker_context]
    rfl
  · change (CounterResources.worker compiler old count upper flags slot).context.registers .rdi =
      (CounterResources.Image.resources compiler old).cell.address
    rw [CounterResources.worker_context]
    rfl
  · exact CounterResources.worker_count compiler old count upper flags slot
  · exact CounterResources.worker_resources compiler old count upper flags slot
  · exact CounterResources.Image.image_nonempty compiler
  · exact CounterResources.Image.image_canonical compiler
  · rw [CounterResources.initial_world]
    exact CounterResources.Image.code compiler old
  · rw [CounterResources.worker_view]
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  · rw [CounterResources.worker_view]
    rfl
  · exact worker_scalar compiler old count upper flags clear slot
  · exact ⟨CounterResources.atomicId compiler old slot,
      ⟨CounterResources.actor slot, (CounterResources.Image.resources compiler old).target⟩,
      CounterResources.selection compiler old count upper flags slot, rfl⟩
  · exact ⟨CounterResources.continuation slot,
      CounterResources.caller_read compiler old count upper flags slot,
      CounterResources.continuation_canonical slot⟩

/-- Enumerate the two physical orders while the regions remain abstract. -/
private theorem two_slot_disjoint (regions : Fin 2 → Region)
    (separate : Ownership.Disjoint (regions 0) (regions 1))
    (i j : Fin 2) (different : i ≠ j) :
    Ownership.Disjoint (regions i) (regions j) := by
  rcases i with ⟨i, iBound⟩
  rcases j with ⟨j, jBound⟩
  have iChoices : i = 0 ∨ i = 1 := by omega
  have jChoices : j = 0 ∨ j = 1 := by omega
  rcases iChoices with rfl | rfl <;> rcases jChoices with rfl | rfl
  · exact False.elim (different rfl)
  · exact separate
  · exact Ownership.disjoint_symm (left := regions 0) (right := regions 1) separate
  · exact False.elim (different rfl)

/-- Pairwise caller separation holds in either physical slot order. -/
private theorem private_slots (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word)
    (i j : Fin 2) (different : i ≠ j) :
    Ownership.Disjoint
      (CounterResources.worker compiler old count upper flags i).resources.caller.loan.region
      (CounterResources.worker compiler old count upper flags j).resources.caller.loan.region :=
  two_slot_disjoint
    (fun slot => (CounterResources.worker compiler old count upper flags slot).resources.caller.loan.region)
    (CounterResources.private_callers compiler old count upper flags) i j different

/-- Assemble all seven independent fields before substituting an actual
manager/attachment computation. Casts preserve physical lookup indices. -/
private theorem pre_of_two_workers (image : ScalarCall64.Image)
    (target : Atomics64.CellId64) (cell : Atomics64.Cell) (before : TSO64.State)
    (population : before.workers.length = 2) (amounts : Fin 2 → BitVec 32)
    (workers : Fin 2 → Worker)
    (valid : WellFormed before .ownedOnly) (empty : Quiescent before)
    (liveTarget : before.world.cells target = some cell)
    (validCell : Atomics64.ValidCell before.world.legacy.shared cell)
    (live : ∀ slot : Fin 2, before.workers[slot.val]? = some (workers slot))
    (entries : ∀ slot : Fin 2,
      Spec.Entry image target cell (amounts slot) before (workers slot))
    (privateCallers : ∀ (i j : Fin 2), i ≠ j →
      Ownership.Disjoint (workers i).resources.caller.loan.region
        (workers j).resources.caller.loan.region)
    (codeCallerSeparation : ∀ slot : Fin 2,
      Ownership.Disjoint ⟨image.base, image.bytes.length⟩
        (workers slot).resources.caller.loan.region) :
    Spec.Pre image target cell before (fun slot => amounts (Fin.cast population slot)) := by
  constructor
  · exact valid
  · exact empty
  · exact liveTarget
  · exact validCell
  · intro slot
    let selected : Fin 2 := Fin.cast population slot
    exact ⟨workers selected, live selected, entries selected⟩
  · intro i j first second different firstLive secondLive
    let left : Fin 2 := Fin.cast population i
    let right : Fin 2 := Fin.cast population j
    have leftLive : before.workers[left.val]? = some (workers left) := live left
    have rightLive : before.workers[right.val]? = some (workers right) := live right
    have firstEq : first = workers left :=
      Option.some.inj (firstLive.symm.trans leftLive)
    have secondEq : second = workers right :=
      Option.some.inj (secondLive.symm.trans rightLive)
    have slotDifferent : left ≠ right := by
      intro same
      apply different
      exact Fin.ext (congrArg (fun slot : Fin 2 => slot.val) same)
    rw [firstEq, secondEq]
    exact privateCallers left right slotDifferent
  · intro slot worker found
    let selected : Fin 2 := Fin.cast population slot
    have known : before.workers[selected.val]? = some (workers selected) := live selected
    have same : worker = workers selected := Option.some.inj (found.symm.trans known)
    rw [same]
    exact codeCallerSeparation selected

/-- Independent full counted-call Pre for the actual manager/setup/attach
state, arbitrary original inputs and every actual original finite slot. -/
theorem loaded_pre (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word)
    (clear : ∀ slot, (flags slot).getLsbD 10 = false) :
    Spec.Pre (CounterCounted.image compiler) (CounterResources.Image.resources compiler old).target
      (CounterResources.Image.resources compiler old).cell
      (CounterResources.initial compiler old count upper flags)
      (requests compiler old count upper flags) := by
  refine pre_of_two_workers (CounterCounted.image compiler)
    (CounterResources.Image.resources compiler old).target
    (CounterResources.Image.resources compiler old).cell
    (CounterResources.initial compiler old count upper flags)
    (CounterResources.workerUniverse2 compiler old count upper flags) count
    (CounterResources.worker compiler old count upper flags)
    (CounterResources.wellFormed compiler old count upper flags)
    (CounterResources.quiescent compiler old count upper flags)
    (CounterResources.registered compiler old count upper flags) ?_
    (CounterResources.worker_live compiler old count upper flags)
    (worker_entry compiler old count upper flags clear)
    (private_slots compiler old count upper flags) ?_
  · rw [CounterResources.initial_world]
    exact CounterResources.Image.target_valid compiler old
  · intro slot
    have separate : Ownership.Disjoint
        (CounterResources.worker compiler old count upper flags slot).resources.code.loan.region
        (CounterResources.worker compiler old count upper flags slot).resources.caller.loan.region :=
      CounterResources.code_caller_disjoint compiler old count upper flags slot slot
    simpa only [CounterResources.worker_view, CounterResources.workerView,
      CounterCounted.image, CounterResources.Image.image] using separate

/-- Exact complete-file admission, present independent Pre, full loaded-cell
retention and target freshness for every supplied input family member. -/
def loadedBatch (compiler : Compiler) (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) (clear : ∀ slot, (flags slot).getLsbD 10 = false) :
    Counted.LoadedBatch (named compiler) where
  priorSpace := empty
  loaded := CounterResources.Image.installed compiler
  admitted := CounterResources.Image.admitted compiler
  before := CounterResources.initial compiler old count upper flags
  target := (CounterResources.Image.resources compiler old).target
  cell := (CounterResources.Image.resources compiler old).cell
  requests := requests compiler old count upper flags
  pre := loaded_pre compiler old count upper flags clear
  text := BufferResources.text_of_retainedWith (CounterMixedGraphs.namedChecked compiler)
    (CounterResources.Image.executable_permissions compiler)
    (fun _address _original live => CounterResources.full_image compiler old count upper flags live)
  retainedImage := fun _address _original live =>
    CounterResources.full_image compiler old count upper flags live
  targetFresh := fun _address _original live => CounterResources.target_outside_loaded compiler old live

/-- The complete actual slot enumeration projects to both original inputs in
physical order. This does not reconstruct independent counts from events. -/
private theorem slot2_range (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word) :
    (List.finRange (CounterResources.initial compiler old count upper flags).workers.length).map
      (slot2 compiler old count upper flags) = [0, 1] := by
  apply List.ext_getElem
  · simpa only [List.length_map, List.length_finRange, List.length_cons, List.length_nil] using
      CounterResources.workerUniverse2 compiler old count upper flags
  · intro index left right
    have bound : index < 2 := by simpa only [List.length_cons, List.length_nil] using right
    have choices : index = 0 ∨ index = 1 := by omega
    rw [List.getElem_map, List.getElem_finRange]
    rcases choices with rfl | rfl <;> apply Fin.ext <;> rfl

theorem requested_total (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word) :
    Spec.requestedTotal (requests compiler old count upper flags) =
      (count 0).toNat + (count 1).toNat := by
  calc
    Spec.requestedTotal (requests compiler old count upper flags) =
        (((List.finRange (CounterResources.initial compiler old count upper flags).workers.length).map
          (slot2 compiler old count upper flags)).map (fun slot => (count slot).toNat)).sum := by
      rw [List.map_map]
      rfl
    _ = (count 0).toNat + (count 1).toNat := by
      rw [slot2_range]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]

/-- Every actual completed independent Post computes its result from the
supplied old64 and two requested low32 inputs, not observed deltas. -/
theorem loaded_post_total (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word)
    {actions : List Action} {actual : TSO64.State × List Observation}
    (post : Spec.Post (named compiler).image (CounterResources.Image.resources compiler old).target
      (CounterResources.Image.resources compiler old).cell
      (CounterResources.initial compiler old count upper flags)
      (requests compiler old count upper flags) actions actual) :
    post.current.toNat = (old.toNat + (count 0).toNat + (count 1).toNat) % 2^64 := by
  have priorRead := CounterResources.initial_read compiler old count upper flags
  have same : post.old = old := Except.ok.inj (post.oldWord.symm.trans priorRead)
  have supplied : Grading.ConcurrentTask.Counted64.requestedTotal
      (requests compiler old count upper flags) = (count 0).toNat + (count 1).toNat :=
    requested_total compiler old count upper flags
  rw [post.total, same, supplied]
  simp only [Nat.add_assoc]

/-- Every successful returned execution of these loaded inputs has a full
independent Post and the same supplied-input modular total. Completion is not
restricted to the particular future schedule chosen by loaded_completion. -/
theorem loaded_completed_total (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word)
    (clear : ∀ slot, (flags slot).getLsbD 10 = false)
    {actions : List Action} {actual : TSO64.State × List Observation}
    (success : schedule (CounterResources.initial compiler old count upper flags)
      actions .ownedOnly .arithmetic = .ok actual) (returned : Returned actual.1) :
    ∃ post : Spec.Post (named compiler).image (CounterResources.Image.resources compiler old).target
        (CounterResources.Image.resources compiler old).cell
        (CounterResources.initial compiler old count upper flags)
        (requests compiler old count upper flags) actions actual,
      post.current.toNat = (old.toNat + (count 0).toNat + (count 1).toNat) % 2^64 := by
  obtain ⟨post⟩ := (named_claim compiler).completed
    (CounterResources.initial compiler old count upper flags)
    (CounterResources.Image.resources compiler old).target
    (CounterResources.Image.resources compiler old).cell (requests compiler old count upper flags)
    (loaded_pre compiler old count upper flags clear) actions actual success returned
  exact ⟨post, loaded_post_total compiler old count upper flags
    (actions := actions) (actual := actual) post⟩

/-- Construct chosen completion and same-run retention over an abstract loaded
batch; a separately typed premise identifies its supplied-input total. -/
private theorem completion_of_total {file name : List Byte} {maxBytes : Nat}
    (named : Counted.NamedImage file name maxBytes) (batch : Counted.LoadedBatch named)
    (claim : Spec.Claim named.image) (expected : Nat)
    (total : ∀ (actions : List Action) (actual : TSO64.State × List Observation)
      (post : Spec.Post named.image batch.target batch.cell
        batch.before batch.requests actions actual), post.current.toNat = expected) :
    ∃ bound : Nat, ∀ (choices : Nat → Nat → Bool) (offset : Nat → Nat),
      ∃ (actions : List Action) (actual : TSO64.State × List Observation),
        EffectSimulation.Mixed.ChoiceTrace.ChosenFrom choices offset actions ∧
        schedule batch.before actions .ownedOnly .arithmetic = .ok actual ∧
        Finished actual.1 ∧ actions.length ≤ bound ∧
        ∃ post : Spec.Post named.image batch.target batch.cell
            batch.before batch.requests actions actual,
          post.current.toNat = expected ∧
          ∀ address original, batch.loaded.space.cells address = some original →
            actual.1.world.legacy.shared.resources.space.cells address = some original := by
  obtain ⟨bound, complete⟩ := claim.completion batch.before batch.target
    batch.cell batch.requests batch.pre [] (batch.before, []) rfl
  refine ⟨bound, ?_⟩
  intro choices offset
  obtain ⟨actions, ⟨final, observations⟩, chosen, actual, finished, bounded,
    _whole, _wholeChoices, fullPost⟩ := complete choices offset
  have selected : EffectSimulation.Mixed.ChoiceTrace.ChosenFrom choices offset actions := by
    simpa only [EffectSimulation.Mixed.ChoiceTrace.issues_nil, Nat.add_zero] using chosen
  have postExists : Nonempty (Spec.Post named.image batch.target batch.cell
      batch.before batch.requests actions (final, observations)) := by
    simpa only [List.nil_append] using fullPost
  obtain ⟨post⟩ := postExists
  refine ⟨actions, (final, observations), selected, actual, finished, bounded, post, ?_, ?_⟩
  · exact total actions (final, observations) post
  · exact batch.retained_image claim actual

/-- Construct a real completed independent Post for every loaded input and
future AF stream/offset, with a bound chosen before those choices. The same
run retains every original ELF cell. This is a finite model existence result,
without native fairness, wall-clock termination or minimum-cost claims. -/
theorem loaded_completion (compiler : Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word)
    (clear : ∀ slot, (flags slot).getLsbD 10 = false) :
    let batch := loadedBatch compiler old count upper flags clear
    ∃ bound : Nat, ∀ (choices : Nat → Nat → Bool) (offset : Nat → Nat),
      ∃ (actions : List Action) (actual : TSO64.State × List Observation),
        EffectSimulation.Mixed.ChoiceTrace.ChosenFrom choices offset actions ∧
        schedule batch.before actions .ownedOnly .arithmetic = .ok actual ∧
        Finished actual.1 ∧ actions.length ≤ bound ∧
        ∃ post : Spec.Post (named compiler).image batch.target batch.cell
            batch.before batch.requests actions actual,
          post.current.toNat = (old.toNat + (count 0).toNat + (count 1).toNat) % 2^64 ∧
          ∀ address original, batch.loaded.space.cells address = some original →
            actual.1.world.legacy.shared.resources.space.cells address = some original := by
  intro batch
  refine completion_of_total (named compiler) batch (named_claim compiler)
    ((old.toNat + (count 0).toNat + (count 1).toNat) % 2^64) ?_
  intro actions actual post
  change Spec.Post (named compiler).image (CounterResources.Image.resources compiler old).target
    (CounterResources.Image.resources compiler old).cell
    (CounterResources.initial compiler old count upper flags)
    (requests compiler old count upper flags) actions actual at post
  exact loaded_post_total compiler old count upper flags
    (actions := actions) (actual := actual) post

#print axioms named
#print axioms named_image
#print axioms named_claim
#print axioms slot2_actualSlot
#print axioms requests_actualSlot
#print axioms stack_facts
#print axioms worker_scalar
#print axioms worker_entry
#print axioms two_slot_disjoint
#print axioms private_slots
#print axioms pre_of_two_workers
#print axioms loaded_pre
#print axioms loadedBatch
#print axioms slot2_range
#print axioms requested_total
#print axioms loaded_post_total
#print axioms loaded_completed_total
#print axioms completion_of_total
#print axioms loaded_completion

end EDSL.Corpus.V1.CountedCertificates

#audit_edsl
