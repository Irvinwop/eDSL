/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.ConcurrentTask.Plain64.Admission
import EDSL.OS.TSO64.Stability

/-!
Independent prefix and scalar-return observations for a plain64 call cohort.
The affected addresses are fixed by the selected input cells and the complete
actual initial FIFOs, including ordinary entry widths and managed descriptors.
They contain no instruction shape, method, progress point or desired reply.

The frame compares complete RAM cells, including inaccessible contents,
mappedness and permissions. Resources and original target authority remain
current at every successful prefix. Returned calls additionally retain their
actual original scalar caller/ABI frame; a return does not require publication.
These predicates define neither the atomic-history postcondition nor a full
concurrent task Claim or corpus certificate.
-/

set_option autoImplicit false

namespace EDSL.Grading.ConcurrentTask.Plain64
open X86 OS OS.TSO64 OS.AddressSpace

/-- The target qword of every independently selected actual worker slot. -/
def Targets {before : TSO64.State}
    (inputs : Fin before.workers.length → Input) (query : Word) : Prop :=
  ∃ tid, (qwordRegion (inputs tid).cell.address).Contains query

/-- Actual initial FIFO bytes, retaining the ordinary dword/qword width or the
managed full-qword descriptor. No prior issue event is invented at admission. -/
def Incoming (before : TSO64.State) (query : Word) : Prop :=
  ∃ (tid : Nat) (worker : Worker) (entry : Pending),
    before.workers[tid]? = some worker ∧ entry ∈ worker.pending ∧
      (⟨entry.store.address, entry.store.width⟩ : Region).Contains query

def Affected (before : TSO64.State)
    (inputs : Fin before.workers.length → Input) (query : Word) : Prop :=
  Targets inputs query ∨ Incoming before query

/-- Observations at any successful finite prefix. Original resource records
are retained, with their complete current authority lists. `selected` also
retains the actual independently admitted target descriptor at each slot. -/
structure PrefixFrame (before after : TSO64.State)
    (inputs : Fin before.workers.length → Input) : Prop where
  valid : WellFormed after .sharedCell
  stable : Stable before.world after.world
  population : after.workers.length = before.workers.length
  resources : ∀ (tid : Nat) (initial : Worker),
    before.workers[tid]? = some initial →
    ∃ current, after.workers[tid]? = some current ∧ current.resources = initial.resources ∧
      ResourcesValid after.world current.resources
  selected : ∀ tid : Fin before.workers.length,
    ∃ (current : Worker) (identifier : Atomics64.HandleId64) (handle : Atomics64.Handle),
      after.workers[tid.val]? = some current ∧
      atomicFor after.world current.resources (inputs tid).cell.address =
        some (identifier, handle, (inputs tid).cell) ∧ handle.cell = (inputs tid).target
  cells : ∀ query, ¬Affected before inputs query →
    after.world.legacy.shared.resources.space.cells query =
      before.world.legacy.shared.resources.space.cells query

/-- A wholly returned cohort additionally has the scalar ABI frame at every
actual original slot. Pending stores and later drains remain separate. -/
structure ReturnFrame (before after : TSO64.State)
    (inputs : Fin before.workers.length → Input) : Prop extends PrefixFrame before after inputs where
  returned : TSO64.Returned after
  slots : ∀ (tid : Fin before.workers.length) (initial final : Worker),
    before.workers[tid.val]? = some initial → after.workers[tid.val]? = some final →
    ScalarCall64.ReturnFrame before after tid.val initial final

end EDSL.Grading.ConcurrentTask.Plain64

#audit_edsl
