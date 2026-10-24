/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.CountedCertificates.Inputs
import EDSL.Corpus.V1.CountedCertificates.OverlapPositions

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Construct useful counted-call evidence for the exact loaded batch of each
complete frozen compiler image. Every old64, upper RSI pair, DF-clear flag
pair and AF stream retains the actual production 0,1,0 prefix, its cut, its
returning suffix and its logical cleanup. The independent Post is obtained
from the unrestricted named claim on that same successful returned execution.

The correlation record retains that precise output through image retention,
RET ordering and cleanup. Complete optional cells include permissions and
inaccessible contents. The final two certificate constructors specialize only
their inhabitants; their independent Claims keep every original quantifier.

The imported coherent scalar RAM, protected-resource, stable-translation/
no-alias, represented-CPU and long-mode/CET-off assumptions remain in force.
Logical retirement supplies no native join, physical OS/CPU correspondence,
source/compiler refinement, fairness, minimum cost or corpus credit.
-/

namespace EDSL.Corpus.V1.CountedCertificates
open X86 OS OS.TSO64

/-- Keep a useful run correlated with one actual production output, including
all prefix/cut/suffix projections and the entire scheduled endpoint/log. The
cleanup remains the object stored by this output, indexed by its suffix.final.
Scheduler slots 0/1 do not identify the workers' resource actors. -/
structure SameOutput {file name : List Byte} {maxBytes : Nat}
    {image : Counted.NamedImage file name maxBytes} (batch : Counted.LoadedBatch image)
    {cohort : EffectSimulation.Mixed.RankedCohort 2 .ownedOnly .arithmetic}
    {ghosts : cohort.Ghosts batch.before} {choices : Nat → Nat → Bool} {old : Word}
    (output : CounterOverlap.Output cohort ghosts choices batch.target batch.cell old) where
  run : Counted.UsefulRun batch
  own : run.own.val = 0
  peer : run.peer.val = 1
  prefixActions : run.prefixActions = output.lead.actions
  prefixObservations : run.prefixObservations = output.lead.observations
  cut : run.cut = output.lead.final
  suffixActions : run.suffixActions = output.suffix.actions
  suffixObservations : run.suffixObservations = output.suffix.observations
  final : run.final = output.suffix.final
  actions : run.actions = output.lead.actions ++ output.suffix.actions
  actual : run.actual =
    (output.suffix.final, output.lead.observations ++ output.suffix.observations)

/-- Assemble over abstract current state and output projections. No manager
computation, instruction arithmetic or ranking argument is unfolded here.
The concrete wrapper below discharges population and supplied-request facts. -/
private theorem useful_of_output {file name : List Byte} {maxBytes : Nat}
    {image : Counted.NamedImage file name maxBytes} (batch : Counted.LoadedBatch image)
    (claim : Grading.ConcurrentTask.Counted64.Claim image.image)
    (population : batch.before.workers.length = 2)
    (amounts : ∀ slot : Fin batch.before.workers.length,
      (batch.requests slot).toNat = if slot.val = 0 then 3 else 9)
    {cohort : EffectSimulation.Mixed.RankedCohort 2 .ownedOnly .arithmetic}
    {ghosts : cohort.Ghosts batch.before} {choices : Nat → Nat → Bool} {old : Word}
    (output : CounterOverlap.Output cohort ghosts choices batch.target batch.cell old) :
    Nonempty (SameOutput batch output) := by
  obtain ⟨post⟩ := claim.completed batch.before batch.target batch.cell batch.requests
    batch.pre (output.lead.actions ++ output.suffix.actions)
    (output.suffix.final, output.lead.observations ++ output.suffix.observations)
    output.actual output.suffix.returned
  obtain ⟨first, middle, last, _occurrences, _firstTid, _middleTid, _lastTid,
    firstLess, middleLess, lastBound, firstSeen, middleSeen, lastSeen⟩ :=
    overlap_positions output.lead.observations 0 1 output.lead.pattern
  let own : Fin batch.before.workers.length := Fin.cast population.symm 0
  let peer : Fin batch.before.workers.length := Fin.cast population.symm 1
  have distinct : own ≠ peer := by
    intro same
    have impossible : (0 : Nat) = 1 :=
      congrArg (fun slot : Fin batch.before.workers.length => slot.val) same
    cases impossible
  have running : ∀ slot : Fin batch.before.workers.length,
      ∃ worker, output.lead.final.workers[slot.val]? = some worker ∧
        worker.phase = .running := by
    intro slot
    exact output.lead.running (Fin.cast population slot)
  have unfinished : ∀ slot : Fin batch.before.workers.length,
      EffectSimulation.Mixed.Counts.countRMW slot.val output.lead.observations <
        (batch.requests slot).toNat := by
    intro slot
    have counted : EffectSimulation.Mixed.Counts.countRMW slot.val output.lead.observations =
        if slot.val = 0 then 2 else 1 := output.lead.counts (Fin.cast population slot)
    rw [counted, amounts slot]
    split <;> decide
  let run : Counted.UsefulRun batch := {
    population := population
    own := own
    peer := peer
    distinct := distinct
    prefixActions := output.lead.actions
    prefixObservations := output.lead.observations
    cut := output.lead.final
    prefixRun := output.lead.actual
    cutRunning := running
    unfinished := unfinished
    suffixActions := output.suffix.actions
    suffixObservations := output.suffix.observations
    final := output.suffix.final
    suffixRun := output.suffix.actual
    post := post
    first := first.index
    middle := middle.index
    last := last.index
    firstBeforeMiddle := firstLess
    middleBeforeLast := middleLess
    beforeCut := lastBound
    firstEvent := first.event
    peerEvent := middle.event
    lastEvent := last.event
    firstObserved := firstSeen
    peerObserved := middleSeen
    lastObserved := lastSeen }
  exact ⟨{
    run := run
    own := rfl
    peer := rfl
    prefixActions := rfl
    prefixObservations := rfl
    cut := rfl
    suffixActions := rfl
    suffixObservations := rfl
    final := rfl
    actions := rfl
    actual := rfl }⟩

namespace SameOutput
variable {file name : List Byte} {maxBytes : Nat}
  {image : Counted.NamedImage file name maxBytes} {batch : Counted.LoadedBatch image}
  {cohort : EffectSimulation.Mixed.RankedCohort 2 .ownedOnly .arithmetic}
  {ghosts : cohort.Ghosts batch.before} {choices : Nat → Nat → Bool} {old : Word}
  {output : CounterOverlap.Output cohort ghosts choices batch.target batch.cell old}

/-- Preserve the production whole-run AF stream, including the suffix offsets
already accumulated from the exact lead.actions. -/
theorem chosen (same : SameOutput batch output) :
    EffectSimulation.Mixed.ChoiceTrace.ChosenIssues choices same.run.actions := by
  rw [same.actions]
  exact output.chosen

/-- Reuse the generic original-index lifting on this output's entire log. -/
theorem whole_pattern (same : SameOutput batch output) :
    (output.lead.observations ++ output.suffix.observations)[same.run.first]? =
      some (.rmw 0 same.run.firstEvent) ∧
    (output.lead.observations ++ output.suffix.observations)[same.run.middle]? =
      some (.rmw 1 same.run.peerEvent) ∧
    (output.lead.observations ++ output.suffix.observations)[same.run.last]? =
      some (.rmw 0 same.run.lastEvent) := by
  have pattern := same.run.whole_pattern
  rw [same.actual, same.own, same.peer] at pattern
  exact pattern

/-- Every actual response from this Post is after this output's real cut.
The generic proof derives this from RET origin and running at the cut. -/
theorem returns_after_cut (same : SameOutput batch output)
    (slot : Fin batch.before.workers.length) :
    output.lead.observations.length ≤ (same.run.post.outcomes slot).returned := by
  rw [← same.prefixObservations]
  exact same.run.returns_after_cut slot

/-- All three prefix increments precede both actual RET positions; no extra
RET-order constructor assumption is introduced by this adapter. -/
theorem before_returns (same : SameOutput batch output) :
    same.run.last < (same.run.post.outcomes same.run.own).returned ∧
    same.run.last < (same.run.post.outcomes same.run.peer).returned :=
  same.run.before_returns

/-- The same useful Post's complete cell frame retains every installed cell
at precisely this suffix.final, including bytes outside the function. -/
theorem retained_final (same : SameOutput batch output) :
    ∀ address original, batch.loaded.space.cells address = some original →
      output.suffix.final.world.legacy.shared.resources.space.cells address = some original := by
  intro address original installed
  have retained := same.run.retained_image address original installed
  rw [same.actual] at retained
  exact retained

/-- Transfer complete cells using this exact cleanup's resource equality.
The weaker outside-byte cleanup frame is not used. -/
theorem retained_cleanup (same : SameOutput batch output) :
    ∀ address original, batch.loaded.space.cells address = some original →
      output.cleanup.result.1.world.legacy.shared.resources.space.cells address = some original := by
  intro address original installed
  rw [output.cleanup.resources]
  exact same.retained_final address original installed

/-- Both values are actual reads, connected by this cleanup's exact RAM
frame. The void call's returned RAX is not identified with either value. -/
theorem cleanup_current (same : SameOutput batch output) :
    output.cleanup.value = same.run.post.current := by
  have finalRead : loadQWord (published output.suffix.final.world) batch.cell.address =
      .ok same.run.post.current := by
    have read := same.run.post.currentWord
    change loadQWord (published same.run.actual.1.world) batch.cell.address =
      .ok same.run.post.current at read
    rw [same.actual] at read
    exact read
  have cleanupRead := output.cleanup.counter
  rw [output.cleanup.ram] at cleanupRead
  exact Except.ok.inj (cleanupRead.symm.trans finalRead)

/-- The retained cleanup is an actual retireAll of this run's endpoint with
empty workers, original final contexts, revocation and the same current word.
This is a logical lifecycle theorem; it makes no native thread-join claim. -/
theorem cleanup_spec (same : SameOutput batch output) :
    Lifecycle.retireAll same.run.final = .ok output.cleanup.result ∧
    output.cleanup.result.1.workers = [] ∧
    output.cleanup.result.2 = same.run.final.workers.reverse.map Worker.context ∧
    (∀ worker ∈ same.run.final.workers,
      Lifecycle.WorkerRevoked output.cleanup.result.1.world worker) ∧
    loadQWord (published output.cleanup.result.1.world) batch.cell.address =
      .ok same.run.post.current ∧
    same.run.post.current.toNat = (old.toNat + 12) % 2^64 := by
  have retired : Lifecycle.retireAll same.run.final = .ok output.cleanup.result := by
    rw [same.final]
    exact output.cleanup.retired
  have contexts : output.cleanup.result.2 = same.run.final.workers.reverse.map Worker.context := by
    rw [same.final]
    exact output.cleanup.contexts
  have revoked : ∀ worker ∈ same.run.final.workers,
      Lifecycle.WorkerRevoked output.cleanup.result.1.world worker := by
    rw [same.final]
    exact output.cleanup.revoked
  have counter := output.cleanup.counter
  rw [same.cleanup_current] at counter
  have total := output.cleanup.total
  rw [same.cleanup_current] at total
  exact ⟨retired, output.cleanup.workers, contexts, revoked, counter, total⟩

end SameOutput

/-- Transport the supplied request formula before substituting an actual
manager/attachment state. Only the physical Fin value enters the formula. -/
private theorem overlap_requests_cast (populationSize : Nat) (population : populationSize = 2) :
    ∀ slot : Fin populationSize,
      (CounterOverlap.requests (Fin.cast population slot)).toNat =
        if slot.val = 0 then 3 else 9 := by
  intro slot
  exact CounterOverlap.requests_nat (Fin.cast population slot)

/-- For both compilers, every supplied old64/upper pair/DF-clear flag pair/AF
stream yields the production overlap output and a useful run of EXACTLY the
corresponding loadedBatch. That output still owns its precise cleanup object.
No schedule, return, outcome, desired intermediate value or success is input. -/
theorem loaded_useful_with_cleanup (compiler : Compiler) (old : Word)
    (upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word)
    (clear : ∀ slot, (flags slot).getLsbD 10 = false) (choices : Nat → Nat → Bool) :
    ∃ output : CounterOverlap.LoadedOutput compiler old upper flags choices,
      Nonempty (SameOutput
        (loadedBatch compiler old CounterOverlap.requests upper flags clear) output) := by
  let batch : Counted.LoadedBatch (named compiler) :=
    loadedBatch compiler old CounterOverlap.requests upper flags clear
  obtain ⟨output⟩ := CounterOverlap.complete compiler old upper flags choices
  have population : batch.before.workers.length = 2 :=
    CounterResources.workerUniverse2 compiler old CounterOverlap.requests upper flags
  have amounts : ∀ slot : Fin batch.before.workers.length,
      (batch.requests slot).toNat =
        if slot.val = 0 then 3 else 9 := by
    change ∀ slot : Fin batch.before.workers.length,
      (CounterOverlap.requests (Fin.cast population slot)).toNat =
        if slot.val = 0 then 3 else 9
    exact overlap_requests_cast batch.before.workers.length population
  refine ⟨output, ?_⟩
  apply useful_of_output
  · exact named_claim compiler
  · exact population
  · exact amounts

/-- The all-input useful family is indexed by the actual batch, rather than
an existential that can select another initialization or a serial completion. -/
theorem loaded_useful (compiler : Compiler) (old : Word)
    (upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word)
    (clear : ∀ slot, (flags slot).getLsbD 10 = false) (choices : Nat → Nat → Bool) :
    Nonempty (Counted.UsefulRun
      (loadedBatch compiler old CounterOverlap.requests upper flags clear)) := by
  obtain ⟨_output, ⟨same⟩⟩ :=
    loaded_useful_with_cleanup compiler old upper flags clear choices
  exact ⟨same.run⟩

/-- Physical Fin slots agree with the existing actualSlot API. No equation
between a scheduler tid and a resource actor enters this result. -/
theorem loaded_useful_slots (compiler : Compiler) (old : Word)
    (upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word)
    (clear : ∀ slot, (flags slot).getLsbD 10 = false) (choices : Nat → Nat → Bool)
    (output : CounterOverlap.LoadedOutput compiler old upper flags choices)
    (same : SameOutput
      (loadedBatch compiler old CounterOverlap.requests upper flags clear) output) :
    same.run.own = actualSlot compiler old CounterOverlap.requests upper flags 0 ∧
    same.run.peer = actualSlot compiler old CounterOverlap.requests upper flags 1 := by
  constructor
  · apply Fin.ext
    exact same.own
  · apply Fin.ext
    exact same.peer

/-- Only the chosen inhabitants use this wrapping old word. -/
def wrappingOld : Word := 0xffffffffffffffff

/-- Both upper halves are nonzero and distinct; the low requests remain 3/9. -/
def wrappingUpper (slot : Fin 2) : BitVec 32 :=
  if slot.val = 0 then 0x12345678 else 0x9abcdef0

def wrappingFlags (_slot : Fin 2) : Word := 0

theorem wrappingFlags_clear : ∀ slot, (wrappingFlags slot).getLsbD 10 = false := by
  intro slot
  change (0 : BitVec 64).getLsbD 10 = false
  exact BitVec.getLsbD_zero (w := 64) (i := 10)

/-- The full dependent witness proposition, elaborated over an abstract batch.
This definition merely names the original existential and both read equalities;
it neither chooses another output nor replaces its independent Post. -/
private def useful_with_current {file name : List Byte} {maxBytes : Nat}
    {image : Counted.NamedImage file name maxBytes} (batch : Counted.LoadedBatch image)
    {cohort : EffectSimulation.Mixed.RankedCohort 2 .ownedOnly .arithmetic}
    {ghosts : cohort.Ghosts batch.before} {choices : Nat → Nat → Bool} {old : Word}
    (output : CounterOverlap.Output (initial := batch.before)
      cohort ghosts choices batch.target batch.cell old) (expected : Nat) : Prop :=
  ∃ same : SameOutput batch output,
    same.run.post.current.toNat = expected ∧ output.cleanup.value.toNat = expected

/-- Apply the existing same-output current theorem while all state indices
are abstract; only the closed modular arithmetic remains for specialization. -/
private theorem useful_with_current_of_total {file name : List Byte} {maxBytes : Nat}
    {image : Counted.NamedImage file name maxBytes} (batch : Counted.LoadedBatch image)
    {cohort : EffectSimulation.Mixed.RankedCohort 2 .ownedOnly .arithmetic}
    {ghosts : cohort.Ghosts batch.before} {choices : Nat → Nat → Bool} {old : Word}
    (output : CounterOverlap.Output (initial := batch.before)
      cohort ghosts choices batch.target batch.cell old) (expected : Nat)
    (useful : Nonempty (SameOutput batch output))
    (total : (old.toNat + 12) % 2^64 = expected) :
    useful_with_current batch output expected := by
  obtain ⟨same⟩ := useful
  have cleaned : output.cleanup.value.toNat = expected := output.cleanup.total.trans total
  have current : same.run.post.current.toNat = expected := by
    rw [← same.cleanup_current]
    exact cleaned
  exact ⟨same, current, cleaned⟩

/-- An actual wrapping specialization, still for every AF stream. The full
independent Post and this same output's cleanup read 11 after old UINT64_MAX
plus the independent 3/9 requests. Whole logs, exact RET origins, all loaded
cells and the cleanup correlation are retained by same and its theorems. -/
theorem wrapping_useful (compiler : Compiler) (choices : Nat → Nat → Bool) :
    ∃ output : CounterOverlap.LoadedOutput compiler wrappingOld wrappingUpper wrappingFlags choices,
      useful_with_current
        (file := CounterMixedGraphs.file compiler) (name := CounterMixedGraphs.name)
        (maxBytes := (CounterMixedGraphs.caps compiler).maxBytes) (image := named compiler)
        (loadedBatch compiler wrappingOld CounterOverlap.requests wrappingUpper
          wrappingFlags wrappingFlags_clear)
        (cohort := CounterOverlap.loadedCohort compiler wrappingOld wrappingUpper wrappingFlags)
        (ghosts := CounterOverlap.loadedGhosts compiler wrappingOld wrappingUpper wrappingFlags)
        (choices := choices) (old := wrappingOld) output 11 := by
  obtain ⟨output, useful⟩ := loaded_useful_with_cleanup compiler wrappingOld
    wrappingUpper wrappingFlags wrappingFlags_clear choices
  have wrapped : (wrappingOld.toNat + 12) % 2^64 = 11 := by
    change ((0xffffffffffffffff : BitVec 64).toNat + 12) % 2^64 = 11
    decide +kernel
  refine ⟨output, ?_⟩
  exact useful_with_current_of_total
    (file := CounterMixedGraphs.file compiler) (name := CounterMixedGraphs.name)
    (maxBytes := (CounterMixedGraphs.caps compiler).maxBytes) (image := named compiler)
    (loadedBatch compiler wrappingOld CounterOverlap.requests wrappingUpper
      wrappingFlags wrappingFlags_clear)
    (cohort := CounterOverlap.loadedCohort compiler wrappingOld wrappingUpper wrappingFlags)
    (ghosts := CounterOverlap.loadedGhosts compiler wrappingOld wrappingUpper wrappingFlags)
    (choices := choices) (old := wrappingOld) output 11 useful wrapped

/-- Exact full-file/name/cap constructors use existing checked named input
and the unrestricted independent named_claim. Only inhabited specializes the
all-input theorem. No constructor field is replaced by metadata text. -/
def certificate (compiler : Compiler) :
    Counted.CountedCertificate (CounterMixedGraphs.file compiler) CounterMixedGraphs.name
      (CounterMixedGraphs.caps compiler).maxBytes where
  named := named compiler
  claim := named_claim compiler
  inhabited := by
    obtain ⟨_output, same, _current, _cleaned⟩ :=
      wrapping_useful compiler (fun _ _ => false)
    exact ⟨{
      batch := loadedBatch compiler wrappingOld CounterOverlap.requests wrappingUpper
        wrappingFlags wrappingFlags_clear
      run := SameOutput.run
        (file := CounterMixedGraphs.file compiler) (name := CounterMixedGraphs.name)
        (maxBytes := (CounterMixedGraphs.caps compiler).maxBytes) (image := named compiler)
        (batch := loadedBatch compiler wrappingOld CounterOverlap.requests wrappingUpper
          wrappingFlags wrappingFlags_clear)
        (cohort := CounterOverlap.loadedCohort compiler wrappingOld wrappingUpper wrappingFlags)
        (ghosts := CounterOverlap.loadedGhosts compiler wrappingOld wrappingUpper wrappingFlags)
        (choices := fun _ _ => false) (old := wrappingOld) (output := _output) same }⟩

/-- Entire original 41016-byte GCC ELF; full 49-byte symbol at base 4207440,
including both RETs. The externally indexed cap remains exactly 64. -/
def gcc : Counted.CountedCertificate GCC.file CounterMixedGraphs.name 64 :=
  certificate .defaultGCC

/-- Entire original 44240-byte Clang ELF; full 86-byte symbol at base 4201344,
including NOP13 and RET. The externally indexed cap remains exactly 128. -/
def clang : Counted.CountedCertificate Clang.file CounterMixedGraphs.name 128 :=
  certificate .defaultClang

#print axioms SameOutput
#print axioms useful_of_output
#print axioms SameOutput.chosen
#print axioms SameOutput.whole_pattern
#print axioms SameOutput.returns_after_cut
#print axioms SameOutput.before_returns
#print axioms SameOutput.retained_final
#print axioms SameOutput.retained_cleanup
#print axioms SameOutput.cleanup_current
#print axioms SameOutput.cleanup_spec
#print axioms overlap_requests_cast
#print axioms loaded_useful_with_cleanup
#print axioms loaded_useful
#print axioms loaded_useful_slots
#print axioms wrappingOld
#print axioms wrappingUpper
#print axioms wrappingFlags
#print axioms wrappingFlags_clear
#print axioms useful_with_current
#print axioms useful_with_current_of_total
#print axioms wrapping_useful
#print axioms certificate
#print axioms gcc
#print axioms clang

end EDSL.Corpus.V1.CountedCertificates

#audit_edsl
