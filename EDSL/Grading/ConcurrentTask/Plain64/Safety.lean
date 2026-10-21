/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.ConcurrentTask.Plain64.Frames

/-!
Independent observations at any successful prefix of a plain64 cohort.
Queue progress records allocation and actual head-drain suffixes without
exposing instruction stages. Complete code, original protected caller reads,
flags, callee-saved registers and the same selected reference remain current.

These are output predicates over actual states. They supply no instruction
shape, future execution, chosen reply or graph-legality admission premise.
Incoming FIFOs retain their original provenance boundary and may be nonempty.
The existing full-cell frame includes their actual address/width footprints.
-/

set_option autoImplicit false

namespace EDSL.Grading.ConcurrentTask.Plain64
open X86 OS OS.TSO64

def writes : Input → Nat
  | .loadAcquire .. => 0
  | .storeRelease .. => 1

/-- The one possible store allocation, retaining the complete admitted
reference, full input value and actual original machine occurrence. -/
def extra (input : Input) (reference : Queue.ManagedRef)
    (initial : Worker) : List Pending :=
  match input with
  | .loadAcquire .. => []
  | .storeRelease _ _ _ value _ => [.managed reference value initial.nextStore]

/-- Observational queue suffix/counter accounting, independent of a method
engine. The actual successful execution supplies the legitimate drain origins. -/
structure QueueFrame (expected actual : Queue.Cursor) : Prop where
  counter : actual.nextStore = expected.nextStore
  suffix : ∃ drained, expected.pending = drained ++ actual.pending

/-- A prefix has either not issued its data store or allocated exactly its
single original occurrence. A load never allocates; either stage permits drains. -/
def QueueProgress (input : Input) (reference : Queue.ManagedRef)
    (initial current : Worker) : Prop :=
  ∃ allocated : Bool,
    (input.site.kind = .loadAcquire → allocated = false) ∧
    QueueFrame
      ⟨initial.pending ++ (if allocated then extra input reference initial else []),
        initial.nextStore + (if allocated then 1 else 0)⟩
      ⟨current.pending, current.nextStore⟩

/-- Complete independently stated prefix observations. Original and current
selectors name the exact same full reference, rather than an address-only alias.
The parent frame preserves authority, population and every unaffected RAM cell. -/
structure SafePrefix (before after : TSO64.State)
    (inputs : Fin before.workers.length → Input) : Prop extends PrefixFrame before after inputs where
  frames : ∀ (tid : Fin before.workers.length) (initial : Worker),
    before.workers[tid.val]? = some initial →
    ∃ (current : Worker) (reference : Queue.ManagedRef),
      after.workers[tid.val]? = some current ∧
      current.resources = initial.resources ∧ ResourcesValid after.world current.resources ∧
      reference.cell = (inputs tid).cell ∧ reference.handle.cell = (inputs tid).target ∧
      atomicFor before.world initial.resources (inputs tid).cell.address =
        some (reference.identifier, reference.handle, reference.cell) ∧
      atomicFor after.world current.resources (inputs tid).cell.address =
        some (reference.identifier, reference.handle, reference.cell) ∧
      QueueProgress (inputs tid) reference initial current ∧
      current.context.flags = initial.context.flags ∧
      (∀ register ∈ PureCall.calleeSaved,
        current.context.registers register = initial.context.registers register) ∧
      CodeAt (published after.world) (inputs tid).site.image.base (inputs tid).site.image.bytes ∧
      (∀ continuation,
        Borrowing.loadWord64 before.world.legacy.shared initial.resources.actor
          initial.resources.caller.identifier initial.resources.callerAddress = .ok continuation →
        Borrowing.loadWord64 after.world.legacy.shared current.resources.actor
          current.resources.caller.identifier current.resources.callerAddress = .ok continuation)

end EDSL.Grading.ConcurrentTask.Plain64

#audit_edsl
