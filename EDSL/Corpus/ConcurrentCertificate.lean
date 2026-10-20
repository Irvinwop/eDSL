/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.Certificate
import EDSL.Grading.ConcurrentTask

set_option warningAsError true
set_option autoImplicit false

/-!
A sibling of the scalar certificate, with a fixed independent concurrent
fetch-add contract. The existing scalar TaskID/AllExecutions registration is
unchanged. These types grant no corpus credit without actual inhabitants.
-/

namespace EDSL.Corpus.Concurrent
open X86 OS Concurrency

abbrev Image (input : FunctionInput) : FetchAddABI64.Image :=
  ⟨input.function.window.base, input.bytes⟩

/-- Useful current resources at the checked actual ELF address, including a
complete retained loaded image and a genuine overlapping two-context witness.
The new modeled ownership world does not authenticate native OS principals. -/
structure LoadedFetchAddBatch (file name : List Byte) (input : FunctionInput) where
  priorSpace : AddressSpace.Space
  loaded : ELF.Loaded
  admitted : input.admit file name priorSpace = .ok loaded
  target : Atomics64.CellId64
  cell : Atomics64.Cell
  before : FetchAddCalls64.CheckedState target cell
  deltas : List Word
  pre : Grading.ConcurrentTask.FetchAdd64.Pre (Image input) before deltas
  initialValue : Word
  initialRead : FetchAddCalls64.read before.state cell = .ok initialValue
  text : ELF.FunctionWindow.TextUnchanged (AddressSpace.toMemory loaded.space)
    (TSO64.published before.state.world) input.function.window input.bytes.length
  retainedImage : ∀ address original, loaded.space.cells address = some original →
    before.state.world.legacy.shared.resources.space.cells address = some original
  population : 2 ≤ deltas.length
  useful : ∀ tid : Fin 2, ∃ delta, deltas[tid.val]? = some delta ∧ delta ≠ 0
  privateCallers : ∀ (i j : Nat) (first second : TSO64.Worker), i ≠ j →
    before.state.workers[i]? = some first → before.state.workers[j]? = some second →
    Ownership.Disjoint first.resources.caller.loan.region second.resources.caller.loan.region
  interleaving : ∃ (actions : List TSO64.Action) (actual : TSO64.State × List TSO64.Observation)
    (i j k : Nat) (first second : Atomics64.FetchAddEvent),
    TSO64.schedule before.state actions = .ok actual ∧ TSO64.Returned actual.1 ∧
    i < j ∧ j < k ∧ actual.2[i]? = some (TSO64.Observation.rmw 0 first) ∧
    actual.2[j]? = some (TSO64.Observation.rmw 1 second) ∧
    actual.2[k]? = some (TSO64.Observation.returned 0) ∧
    first.cell = target ∧ second.cell = target

/-- The candidate cannot select its own mathematics or an unrelated entry.
The image of Claim is definitionally the checked named function's real base
and entire declared bytes. All completed admitted batches are quantified. -/
structure FetchAddCertificate (file name : List Byte) where
  input : FunctionInput
  checked : input.check file name = true
  claim : Grading.ConcurrentTask.FetchAdd64.Claim (Image input)
  inhabited : Nonempty (LoadedFetchAddBatch file name input)

theorem LoadedFetchAddBatch.code {file name : List Byte} {input : FunctionInput}
    (batch : LoadedFetchAddBatch file name input) :
    CodeAt (TSO64.published batch.before.state.world) input.function.window.base input.bytes :=
  ELF.FunctionSymbol.admitted_current_code batch.admitted batch.text

/-- Universal completed-run soundness is the fixed registered concurrent
contract, applied to the same useful loaded batch and actual schedule. -/
theorem FetchAddCertificate.resource {file name : List Byte}
    (certificate : FetchAddCertificate file name)
    (batch : LoadedFetchAddBatch file name certificate.input)
    {actions : List TSO64.Action} {actual : TSO64.State × List TSO64.Observation}
    (success : TSO64.schedule batch.before.state actions = .ok actual)
    (done : TSO64.Returned actual.1) :
    Nonempty (Grading.ConcurrentTask.FetchAdd64.Post (Image certificate.input)
      batch.before batch.deltas batch.initialValue actions actual) :=
  certificate.claim.completed batch.before batch.deltas batch.pre success done
    batch.initialValue batch.initialRead

/-- Neither useful admission nor eventual own completion is inferred from a
conditional checker. Both are proof fields of this same exact-file certificate. -/
theorem FetchAddCertificate.useful_execution {file name : List Byte}
    (certificate : FetchAddCertificate file name) :
    ∃ (batch : LoadedFetchAddBatch file name certificate.input)
      (actions : List TSO64.Action) (actual : TSO64.State × List TSO64.Observation),
      TSO64.schedule batch.before.state actions = .ok actual ∧ TSO64.Returned actual.1 ∧
      Nonempty (Grading.ConcurrentTask.FetchAdd64.Post (Image certificate.input)
        batch.before batch.deltas batch.initialValue actions actual) := by
  obtain ⟨batch⟩ := certificate.inhabited
  obtain ⟨actions, actual, success, done⟩ :=
    certificate.claim.completion batch.before batch.deltas batch.pre
  exact ⟨batch, actions, actual, success, done, certificate.resource batch success done⟩

/-- The stored overlapping witness has the same registered result and resource
contract. A separate, merely serial completing run cannot replace this trace. -/
theorem FetchAddCertificate.useful_interleaving {file name : List Byte}
    (certificate : FetchAddCertificate file name) :
    ∃ (batch : LoadedFetchAddBatch file name certificate.input)
      (actions : List TSO64.Action) (actual : TSO64.State × List TSO64.Observation)
      (i j k : Nat) (first second : Atomics64.FetchAddEvent),
      TSO64.schedule batch.before.state actions = .ok actual ∧ TSO64.Returned actual.1 ∧
      i < j ∧ j < k ∧ actual.2[i]? = some (TSO64.Observation.rmw 0 first) ∧
      actual.2[j]? = some (TSO64.Observation.rmw 1 second) ∧
      actual.2[k]? = some (TSO64.Observation.returned 0) ∧
      first.cell = batch.target ∧ second.cell = batch.target ∧
      Nonempty (Grading.ConcurrentTask.FetchAdd64.Post (Image certificate.input)
        batch.before batch.deltas batch.initialValue actions actual) := by
  obtain ⟨batch⟩ := certificate.inhabited
  obtain ⟨actions, actual, i, j, k, first, second, success, done,
    ordered, ordered', pointA, pointB, returned, targetA, targetB⟩ := batch.interleaving
  exact ⟨batch, actions, actual, i, j, k, first, second, success, done,
    ordered, ordered', pointA, pointB, returned, targetA, targetB,
    certificate.resource batch success done⟩

end EDSL.Corpus.Concurrent

#audit_edsl
