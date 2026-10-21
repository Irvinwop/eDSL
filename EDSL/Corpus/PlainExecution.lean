/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.PlainCertificate

/-!
Construct an actual closed execution from a checked loaded batch and the shared
independent contract. The issue suffix follows the supplied thread-local AF
choices; publication uses the production drain plan after CPU returns. This
existence result does not impose an overlap or read-from witness and therefore
does not by itself establish the useful-population certificate gates.
-/

set_option autoImplicit false

namespace EDSL.Corpus.Plain
open OS OS.TSO64 Grading.ConcurrentTask.Plain64

structure Execution {file : List X86.Byte} {named : List (NamedImage file)}
    (batch : LoadedBatch file named) (choices : Nat → Nat → Bool) where
  issues : List Action
  issued : TSO64.State × List Observation
  chosen : ChosenIssues choices issues
  scheduledIssues : schedule batch.before issues .sharedCell = .ok issued
  returned : Returned issued.1
  drained : TSO64.State × List Observation
  scheduledDrains : DrainClosure.drainAll issued.1 .sharedCell = .ok drained
  drainCertificate : DrainClosure.Certificate issued.1 drained .sharedCell
  finished : Finished drained.1
  scheduled : schedule batch.before (issues ++ DrainClosure.actions issued.1) .sharedCell =
    .ok (drained.1, issued.2 ++ drained.2)
  post : ClosedPost batch.before batch.inputs (issues ++ DrainClosure.actions issued.1)
    (drained.1, issued.2 ++ drained.2) 0

/-- One shared theorem constructs completion and publication closure for any
actual exact-file batch. Neither future scheduler success nor a desired result,
source graph or caller-selected cutpoint is an input. -/
theorem LoadedBatch.execute {file : List X86.Byte} {named : List (NamedImage file)}
    (batch : LoadedBatch file named) (claim : Claim (named.map NamedImage.site))
    (choices : Nat → Nat → Bool) : Nonempty (Execution batch choices) := by
  obtain ⟨issues, issued, chosen, scheduledIssues, returned⟩ :=
    claim.completion batch.before batch.inputs batch.pre.1 [] (batch.before, []) rfl choices
  obtain ⟨drained, scheduledDrains, certificate, finished, scheduled, _post, whole⟩ :=
    claim.closure batch.before batch.inputs batch.pre.1 issues issued scheduledIssues returned
  obtain ⟨post⟩ := whole batch.pre.2
  exact ⟨⟨issues, issued, chosen, scheduledIssues, returned, drained, scheduledDrains,
    certificate, finished, scheduled, post⟩⟩

/-- Complete original ELF cells survive the actual finished run. Freshness is
checked against the entire loaded space, so this covers nontext contents and
permissions as well as executable code. -/
theorem Execution.retainedImage {file : List X86.Byte} {named : List (NamedImage file)}
    {batch : LoadedBatch file named} {choices : Nat → Nat → Bool}
    (execution : Execution batch choices) {address : X86.Word}
    {original : AddressSpace.Cell} (live : batch.loaded.space.cells address = some original) :
    execution.drained.1.world.legacy.shared.resources.space.cells address = some original := by
  have away : ¬Targets batch.inputs address := by
    rintro ⟨tid, inside⟩
    exact batch.targetsFresh tid address original live inside
  exact (execution.post.memory address away).trans (batch.retainedImage address original live)

end EDSL.Corpus.Plain

#audit_edsl
