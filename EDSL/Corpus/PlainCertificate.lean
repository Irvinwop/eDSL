/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.PlainInput
import EDSL.Grading.ConcurrentTask.Plain64.Claim

/-!
Fixed independent exact-file certificate gates for managed full64 acquire loads
and release stores. Universal behavior, useful entire-loaded-image resources and
actual overlapping executions are separate required evidence. A mixed witness
also retains the real store-return/publication/acquire order and read-from edge.
These types grant no corpus credit without checked inhabitants.
-/

set_option autoImplicit false

namespace EDSL.Corpus.Plain
open X86 OS OS.TSO64 OS.TSO64.C23Projection Concurrency
open Grading.ConcurrentTask.Plain64

/-- A genuine two-worker homogeneous population over this exact named file,
with high full64 data and both accesses before either return. -/
structure UsefulNamed {file : List Byte} (named : NamedImage file) where
  batch : LoadedBatch file [named]
  population : batch.before.workers.length = 2
  sameCell : ∀ i j, (batch.inputs i).target = (batch.inputs j).target
  initialHighWord : ∃ tid value,
    loadQWord (published batch.before.world) (batch.inputs tid).cell.address = .ok value ∧
    2^32 ≤ value.toNat
  storeHighWords : ∀ tid, named.kind = .storeRelease →
    ∃ value, (batch.inputs tid).request = .storeRelease (batch.inputs tid).target value ∧
      2^32 ≤ value.toNat
  actions : List Action
  actual : TSO64.State × List Observation
  scheduled : schedule batch.before actions .sharedCell = .ok actual
  finished : Finished actual.1
  post : ClosedPost batch.before batch.inputs actions actual
  overlap : ∃ i j, i ≠ j ∧
    (post.calls.outcomes i).performed < (post.calls.outcomes j).performed ∧
    (post.calls.outcomes j).performed < (post.calls.outcomes i).returned ∧
    (post.calls.outcomes j).performed < (post.calls.outcomes j).returned

structure NamedCertificate (kind : Kind) (file : List Byte) where
  named : NamedImage file
  registeredKind : named.kind = kind
  claim : Claim [named.site]
  inhabited : Nonempty (UsefulNamed named)

/-- The writer's actual RET precedes its real publication, and the actual
acquiring reader then selects that writer's persistent source. Graph node
indices are initialized rows plus access-order slots, not scheduler tids. -/
structure UsefulMixed {file : List Byte} (named : List (NamedImage file)) where
  batch : LoadedBatch file named
  population : batch.before.workers.length = 2
  actions : List Action
  actual : TSO64.State × List Observation
  scheduled : schedule batch.before actions .sharedCell = .ok actual
  finished : Finished actual.1
  post : ClosedPost batch.before batch.inputs actions actual
  writerSlot : Fin post.calls.slots.length
  readerSlot : Fin post.calls.slots.length
  writerKind : (batch.inputs post.calls.slots[writerSlot.val]).site.kind = .storeRelease
  readerKind : (batch.inputs post.calls.slots[readerSlot.val]).site.kind = .loadAcquire
  selectedRF : C23Atomic.ReadsFrom post.table.toCandidate
    (post.initials.length + readerSlot.val) (post.initials.length + writerSlot.val)
  delayed : ∃ stamp ∈ writes 0 actual.2,
    AtomicTrace.Graph.Publication
      ((post.calls.outcomes post.calls.slots[writerSlot.val]).machineEvent
        (post.sources post.calls.slots[writerSlot.val])) stamp ∧
    (post.calls.outcomes post.calls.slots[writerSlot.val]).returned < stamp.position ∧
    stamp.position < (post.calls.outcomes post.calls.slots[readerSlot.val]).performed

/-- One complete final ELF supplies both independently registered operations,
useful homogeneous populations and a genuine mixed publication/source witness. -/
structure CohortCertificate (file : List Byte) where
  named : Kind → NamedImage file
  registeredKinds : ∀ kind, (named kind).kind = kind
  claim : Claim [(named .loadAcquire).site, (named .storeRelease).site]
  homogeneous : ∀ kind, Nonempty (UsefulNamed (named kind))
  mixed : Nonempty (UsefulMixed [named .loadAcquire, named .storeRelease])

/-- The same mixed-catalog machine proof supplies either homogeneous named
certificate; exact-file identity and useful resources remain required. -/
def CohortCertificate.namedCertificate {file : List Byte}
    (certificate : CohortCertificate file) (kind : Kind) : NamedCertificate kind file where
  named := certificate.named kind
  registeredKind := certificate.registeredKinds kind
  claim := certificate.claim.mono (by
    intro selected member
    have same : selected = (certificate.named kind).site := List.mem_singleton.mp member
    subst selected
    cases kind <;> simp)
  inhabited := certificate.homogeneous kind

/-- The independent universal completed behavior applies to every admitted
current batch of this exact checked named image, not only the stored witness. -/
theorem NamedCertificate.resource {kind : Kind} {file : List Byte}
    (certificate : NamedCertificate kind file)
    (batch : LoadedBatch file [certificate.named])
    {actions : List Action} {actual : TSO64.State × List Observation}
    (success : schedule batch.before actions .sharedCell = .ok actual)
    (returned : Returned actual.1) :
    Nonempty (Post batch.before batch.inputs actions actual) :=
  certificate.claim.completed batch.before batch.inputs batch.pre.1 actions actual success returned

end EDSL.Corpus.Plain

#audit_edsl
