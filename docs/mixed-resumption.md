# Mixed instruction resumption

Mixed blocks connect checked machine-code graphs containing ordinary instructions
and locked read-modify-write (RMW) instructions to the production TSO64 scheduler.
Clients supply independent behavior contracts and current resource admission.

Import `EDSL.OS.TSO64.EffectSimulation` for the public interface. Direct imports
and their main APIs are listed below; the namespace is
`EDSL.OS.TSO64.EffectSimulation.Mixed`.

| Direct import | Main APIs |
| --- | --- |
| `EDSL.OS.TSO64.EffectSimulation.Mixed.Head` | `Descriptor`, `Admission`, `Frame`, `Binding`, `One`, `OrdinaryIssued`, `AtomicIssued` |
| `EDSL.OS.TSO64.EffectSimulation.Mixed.Idle` | `IdleStep`, `Idle`, `IdleBox` |
| `EDSL.OS.TSO64.EffectSimulation.Mixed.Block` | `rwp`, `Residual`, `Residual.resume`, `Residual.resume_of_step` |
| `EDSL.OS.TSO64.EffectSimulation.Mixed.Simulation` | `Annotations`, `Entry`, `Response`, `Done`, `Annotations.simulation`, `Annotations.schedule`, `Annotations.schedule_cut`, `Annotations.returned_at` |
| `EDSL.OS.TSO64.EffectSimulation.Mixed.Authority` | `Idle.stable`, `Idle.authorize`, `Idle.atomicFor`, `Idle.atomic_selection` |

## Client workflow

1. State the mathematical result independently as `Post : Assertion`, a predicate
   on scheduler state and history.
2. Build a `Descriptor` fixing exact bytes/base, a `MixedCFG.Graph` with its
   `MixedCFG.Valid` evidence and caps, RMW family, authority profile, worker index,
   original worker/resources, code-loan containment, caller value and current-state
   effect policy. [Mixed instruction graphs](mixed-cfg.md) explains validation.
   Select `.arithmetic` for supported locked ADD/INC as well as XADD;
   the default scheduler family remains `.xaddOnly`. Prove `Admission d initial`
   from the actual well-formed state, installed running worker, exact executable
   bytes and authorized protected caller-word read.
3. Supply independent cutpoint invariants in `Annotations.Inv`. Prove
   `Annotations.blocks`: at each current cutpoint, its frame, running binding and
   invariant establish `rwp` with that node's `depth + 1` fuel. These generated
   obligations cover current instruction effects and admissible idle extensions.
4. Establish `Entry` at a real cutpoint using admission, binding and the invariant
   at the empty history. It has no future-run premise. `Entry.enabled` derives
   current own-issue enabledness for either Bool flag choice. Apply
   `Annotations.schedule`, `schedule_cut` or `returned_at` to an actual successful
   finite schedule when the corresponding execution evidence is available.

The shared effect checker, graph transport, resumption rules and checked schedule
folds are reused across programs. Each new program still needs independent
contracts, invariants and generated block proofs; it reuses the instruction rules.
Graph discovery supplies structural evidence, without automatic invariant synthesis.

## Current execution and resumption

`One` uses the current ordinary `Effects.oneStep` obligations, `OrdinaryReady`
read/queue gates and current `d.policy state`. `OrdinaryIssued` retains the fresh
`Effects.Head`, actual queue/finish effects and full `EffectSimulation.Reifies`
CPU equality, including reconstructed memory. A resumed head uses the current
queue and read policy; saved registers alone do not authenticate stale RAM.

At a locked head with an empty own FIFO, `One` requires the exact current
`TSO64.atomicFor` first matching selector at the current operand address.
`AtomicIssued` retains that selection, current `sharedCPU`, actual primitive and
machine executions and their joint family `MachineEffect`. `AtomicIssued.of_effect`
connects such a checked effect and its current admissions to the actual issue.
A nonempty whole own
FIFO blocks before selector lookup or atomic effect, even for unrelated addresses.

`Idle` authenticates connected peer issues, every drain and exact own blocked
attempts. A blocked attempt must retain the whole state. Every blocked and drain
position remains in the log and schedule, including a prefix containing only
blocked attempts. `Residual.idle` and blocked resumption retain the same node and
positive fuel. An ordinary or locked retirement consumes one unit; RET also
consumes a unit and records the response. `Annotations.arrival` eagerly starts a
reached cutpoint's `depth + 1` block before further interference. Zero fuel fails
closed. The existing ordinary `Resumable` interface retains its ordinary domain.

Authority transport preserves stable metadata, permissions and the ordered
selector at a fixed address with retained resources (`Idle.atomic_selection`).
It never establishes preservation of shared RAM contents. Current operand reads,
pending FIFOs and reconstructed memory remain separate execution facts.

## Return and scope

`Response.post` establishes `Post response.after response.history` at the exact
ordinary RET. `Annotations.returned_at` identifies that actual return position
and its complete prefix. `Done` and `Done.idle` retain the historical response
prefix and current returned-worker frame through later publication or peer work.
A memory-dependent `Post` at return does not become `Post` of the later state;
pending stores may remain at RET.

These results inherit CET-off long mode, aligned non-crossing scalar accesses,
coherent write-back (WB) RAM, stable translation/permissions, injective physical
backing and compatible line/page placement. Unmanaged aliases, mixed-width RMW
overlaps, MMIO, DMA and non-temporal interference remain excluded. Ownership,
code/caller loans, synchronization and resource lifetimes remain explicit
obligations; see the [bridge scope](effect-scheduler-bridge.md#scope). These results
add no fairness, global termination, physical CPU or Linux/kernel refinement,
whole-program instruction counts, lifecycle or ABI guarantees, or corpus coverage.
