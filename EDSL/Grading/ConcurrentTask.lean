/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.FetchAddABI64
import EDSL.PureCall.Contract

set_option warningAsError true
set_option autoImplicit false

/-!
Independent registration for a closed batch of full64 fetch-add calls in the
managed scalar TSO64 model. One initial context represents one call occurrence.
This specification contains no decoder shape, VC cutpoint, desired successor
gate or accepted-history premise. Candidate proofs must establish its claims.
It registers no physical CPU, published x86-TSO, Linux or GNU atomic-order claim.
-/

namespace EDSL.Grading.ConcurrentTask.FetchAdd64
open X86 OS Concurrency

def model : String := "managed-tso64-closed-batch-v1"

/-- Admission checks only current entry arguments, scalar ABI and resources.
The entire context population is covered, including every possible peer writer.
Initial words and deltas are arbitrary; success and results are not admissions. -/
structure Pre {target : Atomics64.CellId64} {cell : Atomics64.Cell}
    (image : FetchAddABI64.Image) (before : FetchAddCalls64.CheckedState target cell)
    (deltas : List Word) : Prop where
  length : before.state.workers.length = deltas.length
  entry : ∀ tid : Fin deltas.length,
    FetchAddABI64.gate image before tid.val tid.val deltas[tid] = true

/-- Counts attempted own issues independently of any candidate's instruction
family. The bound is proved by the candidate, never supplied by admission. -/
def issues (tid : Nat) (actions : List TSO64.Action) : Nat :=
  (actions.filter fun action => match action with
    | .issue thread _ => decide (thread = tid)
    | .drain _ => false).length

def response (after : TSO64.State) (tid : Nat) : Word :=
  (after.workers[tid]?.map fun worker => worker.context.registers .rax).getD 0

/-- Default values only totalize the view. Post additionally requires the real
returned worker at each index; a missing context cannot meet that obligation. -/
def cohort (deltas : List Word) (after : TSO64.State) : List (FetchAddCalls64.Call Nat) :=
  (List.range deltas.length).map fun tid =>
    ⟨tid, tid, deltas[tid]?.getD 0, response after tid⟩

def selectedCall (target : Atomics64.CellId64) : TSO64.Observation →
    Option (FetchAddCalls64.Call Nat)
  | .rmw tid event => if event.cell = target then
      some ⟨tid, tid, event.arithmetic.delta, event.arithmetic.event.before⟩ else none
  | _ => none

/-- Independent represented SysV return/resource contract. Collection observes
completion without releasing original loans, tickets or handles. -/
structure ReturnFrame (before after : TSO64.State) (tid : Nat)
    (initial final : TSO64.Worker) : Prop where
  live : after.workers[tid]? = some final
  phase : final.phase = .returned
  empty : final.pending = []
  resources : final.resources = initial.resources
  current : TSO64.ResourcesValid after.world final.resources
  registers : ∀ register ∈ PureCall.calleeSaved,
    final.context.registers register = initial.context.registers register
  stack : final.context.registers .rsp = initial.context.registers .rsp + 8
  stackCanonical : canonical (final.context.registers .rsp) = true
  direction : final.context.flags.getLsbD 10 = false
  continuation : ∃ address,
    Borrowing.loadWord64 before.world.legacy.shared initial.resources.actor
      initial.resources.caller.identifier initial.resources.callerAddress = .ok address ∧
    final.context.rip = address
  collect : TSO64.collect after tid = .ok (final.context.registers .rax)

/-- Exact finite call histories, complete occurrence coverage, original caller
frames, and no unrelated atomic or externally retained memory effects. All
arithmetic is the independently defined ModuloCounter relation inside Complete. -/
structure Post {target : Atomics64.CellId64} {cell : Atomics64.Cell}
    (image : FetchAddABI64.Image) (before : FetchAddCalls64.CheckedState target cell)
    (deltas : List Word) (prior : Word) (actions : List TSO64.Action)
    (actual : TSO64.State × List TSO64.Observation) where
  entries : List (FetchAddCalls64.Entry Nat)
  result : FetchAddCalls64.Result Nat target cell
  final : Word
  actions_eq : CallTrace.actions entries = actions
  state_eq : result.state.state = actual.1
  observations_eq : result.observations = actual.2
  history : FetchAddABI64.Complete image before entries prior result final
  points : result.events.filterMap Linearizability.Event.call? =
    actual.2.filterMap (selectedCall target)
  calls : (Linearizability.calls result.events).Perm (cohort deltas actual.1)
  noForeignRMW : ∀ tid event, TSO64.Observation.rmw tid event ∈ actual.2 → event.cell = target
  returns : ∀ tid initial, before.state.workers[tid]? = some initial →
    ∃ returned, ReturnFrame before.state actual.1 tid initial returned
  stable : TSO64.Stable before.state.world actual.1.world
  memory : ∀ address, ¬ (AddressSpace.qwordRegion cell.address).Contains address →
    (TSO64.published actual.1.world).read address =
      (TSO64.published before.state.world).read address

/-- Every reachable prefix retains the original contexts and authority.
Internal scratch values need not remain unchanged at every prefix. -/
structure SafePrefix (before after : TSO64.State) : Prop where
  valid : TSO64.WellFormed after
  stable : TSO64.Stable before.world after.world
  length : after.workers.length = before.workers.length
  resources : ∀ (tid : Nat) (initial : TSO64.Worker), before.workers[tid]? = some initial →
    ∃ current : TSO64.Worker, after.workers[tid]? = some current ∧ current.resources = initial.resources ∧
      TSO64.ResourcesValid after.world current.resources

/-- Fixed semantic, safety and own-progress requirements for a candidate image.
No successful checker result, body invariant or future-success oracle is a
premise. The progress bound is existential proof output, not an ISA/hardware
minimum or a scheduling-fairness assertion. -/
structure Claim (image : FetchAddABI64.Image) : Prop where
  completed : ∀ {target cell} (before : FetchAddCalls64.CheckedState target cell) deltas,
    Pre image before deltas → ∀ {actions actual},
    TSO64.schedule before.state actions = .ok actual → TSO64.Returned actual.1 →
    ∀ prior, FetchAddCalls64.read before.state cell = .ok prior →
      Nonempty (Post image before deltas prior actions actual)
  prefixes : ∀ {target cell} (before : FetchAddCalls64.CheckedState target cell) deltas,
    Pre image before deltas → ∀ {actions actual},
    TSO64.schedule before.state actions = .ok actual → SafePrefix before.state actual.1
  enabled : ∀ {target cell} (before : FetchAddCalls64.CheckedState target cell) deltas,
    Pre image before deltas → ∀ {actions actual},
    TSO64.schedule before.state actions = .ok actual → ∀ tid worker,
    actual.1.workers[tid]? = some worker → worker.phase = .running → ∀ af,
    ∃ result, TSO64.step actual.1 (.issue tid af) = .ok result ∧ result.2.retired = 1
  completion : ∀ {target cell} (before : FetchAddCalls64.CheckedState target cell) deltas,
    Pre image before deltas → ∃ actions actual,
      TSO64.schedule before.state actions = .ok actual ∧ TSO64.Returned actual.1
  bounded : ∃ bound : Nat, 0 < bound ∧
    ∀ {target cell} (before : FetchAddCalls64.CheckedState target cell) deltas,
    Pre image before deltas → ∀ {actions actual},
    TSO64.schedule before.state actions = .ok actual → ∀ tid,
    bound ≤ issues tid actions → ∀ worker, actual.1.workers[tid]? = some worker →
      worker.phase = .returned ∧ worker.pending = []

end EDSL.Grading.ConcurrentTask.FetchAdd64

#audit_edsl
