/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.ELF.FunctionInput
import EDSL.Grading.ConcurrentTask.Counted64.Contract
import EDSL.OS.TSO64.ReturnPositions
import EDSL.Audit

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Exact named-file certificates for the independent counted64 cohort contract.
The external complete file, requested name and explicit byte cap bind the
entire named extent at its real ELF address. Universal behavior and useful
loaded resources with a completed overlapping run are separate obligations.

One call requests many individual unit RMWs. Other callers may increment
between those RMWs; this interface never treats a complete void call as one
indivisible fetch-add operation. Profiles, ABI obligations, prefix safety,
exact event/RET positions and progress quantifiers are fixed by Counted64.
The modeled coherent scalar RAM, protected resources, translation/no-alias
and represented CPU/CET-off assumptions remain in force. No physical CPU/OS,
source/compiler, fairness, minimum-operation or corpus credit follows from
these types alone.
-/

namespace EDSL.Corpus.Counted
open X86 OS OS.TSO64

/-- Reporting identity for the fixed independent modeled contract. -/
def model : String := "managed-tso64-counted64-cohort-v1"

/-- The caller supplies the complete file, exact requested name and byte cap.
Checked selection binds the unique named complete function, not a short window.
The optional default preserves the existing 64-byte named-checker convention. -/
structure NamedImage (file name : List Byte) (maxBytes : Nat := 64) where
  input : ELF.FunctionInput
  checked : input.checkWith maxBytes file name = true

/-- Behavioral entry is exactly the checked symbol address and entire bytes. -/
def NamedImage.image {file name : List Byte} {maxBytes : Nat}
    (named : NamedImage file name maxBytes) : ScalarCall64.Image :=
  ⟨named.input.function.window.base, named.input.bytes⟩

/-- Current resources retain every installed file cell, including data outside
text and bytes hidden by permissions. Target freshness concerns the complete
loaded image. No schedule, annotation, rank or result enters independent Pre. -/
structure LoadedBatch {file name : List Byte} {maxBytes : Nat}
    (named : NamedImage file name maxBytes) where
  priorSpace : AddressSpace.Space
  loaded : ELF.Loaded
  admitted : named.input.admitWith maxBytes file name priorSpace = .ok loaded
  before : TSO64.State
  target : Atomics64.CellId64
  cell : Atomics64.Cell
  requests : Grading.ConcurrentTask.Counted64.Requests before
  pre : Grading.ConcurrentTask.Counted64.Pre named.image target cell before requests
  text : ELF.FunctionWindow.TextUnchanged (AddressSpace.toMemory loaded.space)
    (published before.world) named.input.function.window named.input.bytes.length
  retainedImage : ∀ address original, loaded.space.cells address = some original →
    before.world.legacy.shared.resources.space.cells address = some original
  targetFresh : ∀ address original, loaded.space.cells address = some original →
    ¬ (AddressSpace.qwordRegion cell.address).Contains address

/-- A completed overlap is indexed by its actual loaded initial batch, so an
execution from another initialization cannot supply this evidence. Every slot
is still running and below its independent requested count at the cut. The
three observations use original full-list indices, with own/peer/own issuers.
The endpoint and whole log are defined by this exact cut's successful suffix. -/
structure UsefulRun {file name : List Byte} {maxBytes : Nat}
    {named : NamedImage file name maxBytes} (batch : LoadedBatch named) where
  population : batch.before.workers.length = 2
  own : Fin batch.before.workers.length
  peer : Fin batch.before.workers.length
  distinct : own ≠ peer
  prefixActions : List Action
  prefixObservations : List Observation
  cut : TSO64.State
  prefixRun : schedule batch.before prefixActions .ownedOnly .arithmetic =
    .ok (cut, prefixObservations)
  cutRunning : ∀ slot : Fin batch.before.workers.length,
    ∃ worker, cut.workers[slot.val]? = some worker ∧ worker.phase = .running
  unfinished : ∀ slot : Fin batch.before.workers.length,
    EffectSimulation.Mixed.Counts.countRMW slot.val prefixObservations <
      (batch.requests slot).toNat
  suffixActions : List Action
  suffixObservations : List Observation
  final : TSO64.State
  suffixRun : schedule cut suffixActions .ownedOnly .arithmetic =
    .ok (final, suffixObservations)
  post : Grading.ConcurrentTask.Counted64.Post named.image batch.target batch.cell
    batch.before batch.requests (prefixActions ++ suffixActions)
    (final, prefixObservations ++ suffixObservations)
  first : Nat
  middle : Nat
  last : Nat
  firstBeforeMiddle : first < middle
  middleBeforeLast : middle < last
  beforeCut : last < prefixObservations.length
  firstEvent : Atomics64.FetchAddEvent
  peerEvent : Atomics64.FetchAddEvent
  lastEvent : Atomics64.FetchAddEvent
  firstObserved : prefixObservations[first]? = some (.rmw own.val firstEvent)
  peerObserved : prefixObservations[middle]? = some (.rmw peer.val peerEvent)
  lastObserved : prefixObservations[last]? = some (.rmw own.val lastEvent)

/-- Existential nonvacuity keeps the loaded batch and its same-run overlap. -/
structure UsefulNamed {file name : List Byte} {maxBytes : Nat}
    (named : NamedImage file name maxBytes) where
  batch : LoadedBatch named
  run : UsefulRun batch

/-- The candidate cannot choose its mathematics, execution profile or stronger
entry predicate. Claim retains every finite independently admitted population,
all requests/high RSI/actors, every successful prefix and both progress fields.
The separate two-worker witness does not restrict those universal quantifiers. -/
structure CountedCertificate (file name : List Byte) (maxBytes : Nat := 64) where
  named : NamedImage file name maxBytes
  claim : Grading.ConcurrentTask.Counted64.Claim named.image
  inhabited : Nonempty (UsefulNamed named)

/-- Exact checked metadata, complete symbol extent and executable LOAD layout
use the same caller-indexed byte cap as named checking and admission. -/
theorem NamedImage.binding {file name : List Byte} {maxBytes : Nat}
    (named : NamedImage file name maxBytes) :
    ELF.FunctionSymbol.CheckedMetadata file named.input.table.header named.input.metadata ∧
    named.input.function.Contract named.input.metadata name named.input.bytes.length ∧
    ELF.FunctionWindow.Layout file named.input.table ∧
    ELF.FunctionWindow.Selection file named.input.table.image
      named.input.function.window named.input.bytes maxBytes :=
  ELF.FunctionSymbol.checked_soundWith named.checked

theorem CountedCertificate.binding {file name : List Byte} {maxBytes : Nat}
    (certificate : CountedCertificate file name maxBytes) :
    ELF.FunctionSymbol.CheckedMetadata file certificate.named.input.table.header
      certificate.named.input.metadata ∧
    certificate.named.input.function.Contract certificate.named.input.metadata name
      certificate.named.input.bytes.length ∧
    ELF.FunctionWindow.Layout file certificate.named.input.table ∧
    ELF.FunctionWindow.Selection file certificate.named.input.table.image
      certificate.named.input.function.window certificate.named.input.bytes maxBytes :=
  certificate.named.binding

/-- Current selected code comes from actual complete-file admission and its
explicit post-installation text/execute-permission retention. -/
theorem LoadedBatch.code {file name : List Byte} {maxBytes : Nat}
    {named : NamedImage file name maxBytes} (batch : LoadedBatch named) :
    CodeAt (published batch.before.world) named.image.base named.image.bytes :=
  ELF.FunctionSymbol.admitted_current_codeWith batch.admitted batch.text

/-- Apply the unrestricted independent claim to any admitted loaded batch and
any actual successful schedule whose actual endpoint has returned. -/
theorem CountedCertificate.resource {file name : List Byte} {maxBytes : Nat}
    (certificate : CountedCertificate file name maxBytes)
    (batch : LoadedBatch certificate.named)
    {actions : List Action} {actual : TSO64.State × List Observation}
    (success : schedule batch.before actions .ownedOnly .arithmetic = .ok actual)
    (returned : Returned actual.1) :
    Nonempty (Grading.ConcurrentTask.Counted64.Post certificate.named.image
      batch.target batch.cell batch.before batch.requests actions actual) :=
  certificate.claim.completed batch.before batch.target batch.cell batch.requests
    batch.pre actions actual success returned

/-- Every original loaded cell is retained by every successful prefix. Full
optional-cell equality supplies byte and permission retention together, without
reconstructing unreadable cells from their accessible-memory projection. -/
theorem LoadedBatch.retained_image {file name : List Byte} {maxBytes : Nat}
    {named : NamedImage file name maxBytes} (batch : LoadedBatch named)
    (claim : Grading.ConcurrentTask.Counted64.Claim named.image)
    {actions : List Action} {actual : TSO64.State × List Observation}
    (success : schedule batch.before actions .ownedOnly .arithmetic = .ok actual) :
    ∀ address original, batch.loaded.space.cells address = some original →
      actual.1.world.legacy.shared.resources.space.cells address = some original := by
  have safe := claim.prefixes batch.before batch.target batch.cell batch.requests
    batch.pre actions actual success
  intro address original installed
  exact (safe.memory address (batch.targetFresh address original installed)).trans
    (batch.retainedImage address original installed)

theorem CountedCertificate.retained_image {file name : List Byte} {maxBytes : Nat}
    (certificate : CountedCertificate file name maxBytes)
    (batch : LoadedBatch certificate.named)
    {actions : List Action} {actual : TSO64.State × List Observation}
    (success : schedule batch.before actions .ownedOnly .arithmetic = .ok actual) :
    ∀ address original, batch.loaded.space.cells address = some original →
      actual.1.world.legacy.shared.resources.space.cells address = some original :=
  batch.retained_image certificate.claim success

namespace UsefulRun
variable {file name : List Byte} {maxBytes : Nat}
  {named : NamedImage file name maxBytes} {batch : LoadedBatch named}

/-- The entire original action list, with no prefix replacement. -/
def actions (run : UsefulRun batch) : List Action := run.prefixActions ++ run.suffixActions

/-- The same completed endpoint and original unfiltered observation indices. -/
def actual (run : UsefulRun batch) : TSO64.State × List Observation :=
  (run.final, run.prefixObservations ++ run.suffixObservations)

theorem scheduled (run : UsefulRun batch) :
    schedule batch.before run.actions .ownedOnly .arithmetic = .ok run.actual :=
  run.post.scheduled

/-- The useful prefix's three original RMW positions remain the same positions
in the full completed execution, including every intervening ordinary label. -/
theorem whole_pattern (run : UsefulRun batch) :
    run.actual.2[run.first]? = some (.rmw run.own.val run.firstEvent) ∧
    run.actual.2[run.middle]? = some (.rmw run.peer.val run.peerEvent) ∧
    run.actual.2[run.last]? = some (.rmw run.own.val run.lastEvent) := by
  have middleBound := Nat.lt_trans run.middleBeforeLast run.beforeCut
  have firstBound := Nat.lt_trans run.firstBeforeMiddle middleBound
  change (run.prefixObservations ++ run.suffixObservations)[run.first]? = _ ∧
    (run.prefixObservations ++ run.suffixObservations)[run.middle]? = _ ∧
    (run.prefixObservations ++ run.suffixObservations)[run.last]? = _
  rw [List.getElem?_append_left firstBound, List.getElem?_append_left middleBound,
    List.getElem?_append_left run.beforeCut]
  exact ⟨run.firstObserved, run.peerObserved, run.lastObserved⟩

/-- Every actual RET occurs at or after the real cut. A prefix RET would keep
that worker returned through the same prefix's remaining successful suffix,
contradicting the independently recorded running worker at this cut. -/
theorem returns_after_cut (run : UsefulRun batch) (slot : Fin batch.before.workers.length) :
    run.prefixObservations.length ≤ (run.post.outcomes slot).returned := by
  by_cases after : run.prefixObservations.length ≤ (run.post.outcomes slot).returned
  · exact after
  · have early : (run.post.outcomes slot).returned < run.prefixObservations.length := by
      omega
    have observed : (run.prefixObservations ++ run.suffixObservations)[(run.post.outcomes slot).returned]? = some (.returned slot.val) :=
      (run.post.outcomes slot).responseBoundary.observed.trans
        (congrArg (fun seen : Observation => some seen)
          (run.post.outcomes slot).responseObserved)
    have prefixObserved : run.prefixObservations[(run.post.outcomes slot).returned]? =
        some (.returned slot.val) := by
      simpa only [List.getElem?_append_left early] using observed
    obtain ⟨_before, _action, _after, _value, _prefix, _selected, _stepped, origin, tail⟩ :=
      ReturnPositions.returned_at batch.pre.valid run.prefixRun prefixObserved
    obtain ⟨_world, _prior, returnedWorker, _priorLive, returnedLive, _valueEq,
      returnedPhase, _resources, _pending, _counter⟩ := origin.frame
    obtain ⟨retained, retainedLive, saved⟩ :=
      ReturnPositions.schedule_saved tail returnedLive returnedPhase
    obtain ⟨runningWorker, runningLive, runningPhase⟩ := run.cutRunning slot
    have same : runningWorker = retained := Option.some.inj (runningLive.symm.trans retainedLive)
    have impossible : Phase.running = Phase.returned :=
      runningPhase.symm.trans ((congrArg Worker.phase same).trans
        (saved.phase.trans returnedPhase))
    cases impossible

/-- The entire own/peer/own prefix is before both actual RETs from this Post,
not merely before a return from some separately selected completing run. -/
theorem before_returns (run : UsefulRun batch) :
    run.last < (run.post.outcomes run.own).returned ∧
    run.last < (run.post.outcomes run.peer).returned := by
  have beforeCut := run.beforeCut
  have ownReturn := run.returns_after_cut run.own
  have peerReturn := run.returns_after_cut run.peer
  constructor <;> omega

/-- Full loaded-cell retention is obtained from this useful run's stored Post,
with no borrowing of another execution's image/frame field. -/
theorem retained_image (run : UsefulRun batch) :
    ∀ address original, batch.loaded.space.cells address = some original →
      run.actual.1.world.legacy.shared.resources.space.cells address = some original := by
  intro address original installed
  exact (run.post.safe.memory address (batch.targetFresh address original installed)).trans
    (batch.retainedImage address original installed)

end UsefulRun

/-- Extract the same completed overlapping run, its actual scheduled endpoint,
independent Post, original positions and both actual RET orderings. -/
theorem CountedCertificate.useful_interleaving {file name : List Byte} {maxBytes : Nat}
    (certificate : CountedCertificate file name maxBytes) :
    ∃ useful : UsefulNamed certificate.named,
      schedule useful.batch.before useful.run.actions .ownedOnly .arithmetic =
        .ok useful.run.actual ∧
      Nonempty (Grading.ConcurrentTask.Counted64.Post certificate.named.image useful.batch.target
        useful.batch.cell useful.batch.before useful.batch.requests
        useful.run.actions useful.run.actual) ∧
      useful.run.actual.2[useful.run.first]? =
        some (.rmw useful.run.own.val useful.run.firstEvent) ∧
      useful.run.actual.2[useful.run.middle]? =
        some (.rmw useful.run.peer.val useful.run.peerEvent) ∧
      useful.run.actual.2[useful.run.last]? =
        some (.rmw useful.run.own.val useful.run.lastEvent) ∧
      useful.run.last < (useful.run.post.outcomes useful.run.own).returned ∧
      useful.run.last < (useful.run.post.outcomes useful.run.peer).returned := by
  obtain ⟨useful⟩ := certificate.inhabited
  obtain ⟨first, middle, last⟩ := useful.run.whole_pattern
  obtain ⟨ownReturn, peerReturn⟩ := useful.run.before_returns
  exact ⟨useful, useful.run.scheduled, ⟨useful.run.post⟩, first, middle, last,
    ownReturn, peerReturn⟩

#print axioms NamedImage.binding
#print axioms CountedCertificate.binding
#print axioms LoadedBatch.code
#print axioms CountedCertificate.resource
#print axioms LoadedBatch.retained_image
#print axioms CountedCertificate.retained_image
#print axioms UsefulRun.scheduled
#print axioms UsefulRun.whole_pattern
#print axioms UsefulRun.returns_after_cut
#print axioms UsefulRun.before_returns
#print axioms UsefulRun.retained_image
#print axioms CountedCertificate.useful_interleaving

end EDSL.Corpus.Counted

#audit_edsl
