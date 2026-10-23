# Arithmetic RMW origin prerequisite

Import the common origin interface with:

```lean
import EDSL.OS.ArithmeticRMWOrigin64
```

The current TSO64 dispatcher accepts XADD. The interface below provides the
shared arithmetic and resource facts needed to extend it to ADD and INC.

`EDSL.OS.ArithmeticRMWOrigin64` separates the input to the modular-counter
contract from XADD's register destination. `AddRMW64.Instruction.delta` is the captured
input for all three existing `AddRMW64` tags: XADD reads its prestate source,
ADD sign-extends its immediate, and INC contributes one. The complete typed
event retains that input even when the resulting word is unchanged.

`Evidence` requires the selected scheduler worker, running phase, current
code/caller leases, instruction-sized code bounds, an empty own FIFO, membership
of the actual handle in that worker's atomic grants, the full current
`AddRMWMachineEffect`, the selected cell, and the exact installed CPU context.
Its `input` field binds the point to `instruction.delta (sharedCPU before worker)`.
Current decode, exact `CodeAt`, checked OS authorization, memory projections,
primitive response and singleton RMW8 access remain in the joint effect.

The worker's list index comes from `point.thread`. The effect's actor comes
from `worker.resources.actor`; `actor_handle` derives the event's actual actor
and handle. These identities are never equated. Occurrence identifiers remain
annotations on the actual indexed call boundary, so equal zero events do not
identify occurrences.

`Evidence.authorized` extracts successful current authorization for the
selected descriptor. `Evidence.arithmetic` states the independent full-width
`ModuloCounter.Step`. `Evidence.projection` binds both supplied endpoint reads
to the actual selected descriptor using the primitive old read and readback.
These facts require no old-value register destination and no scheduler-history
projection. They do require the checked joint effect and actual endpoint reads.

`Origin` existentially packages `Evidence`. It is a reusable prerequisite for
an installed arithmetic RMW. `of_step` lifts actual successful steps of the existing XADD dispatcher; it does
not derive ADD/INC scheduler execution. Its profile is explicit in the step
premise. A future generic dispatcher must prove its own guarded dispatch and
produce this evidence from the resulting real step.

`Evidence.register_frame` uses `oldDestination`; `all_registers` applies when
that destination is absent. XADD-only consequences have explicit names and
require the `.xadd` tag: `xadd_effect`, `xadd_source_input`, `xadd_source_old`, and
`xadd_rax`. The last also requires the destination to be RAX. None of these
facts certifies a RET or supplies an ABI certificate for ADD/INC. In particular,
a source-RSP XADD retains its existing changed-RSP limitations.

`FetchAddCalls64.RMWOrigin`, `rmw_origin`, `point_at`, and all existing public
theorem statements retain their XADD contracts. `RMWOrigin.arithmetic` also
requires the actual successful step: the legacy predicate alone does not
expose the current code/caller leases, bounds and grant membership. The new
`arithmetic_origin` and `point_at_arithmetic` expose common evidence at the
same real step and indexed prefix. Call arithmetic in `Emission.sequential`
now uses this evidence. The call constructor retains its original record form, preserving existing
projection simplification.

`Origin.observed` retains a selected event and one retired instruction for
every origin, including zero updates. `blocked` separately retains the whole
input scheduler state, zero retirement and absence of an RMW observation.
No passive-interference classification changes, and no locked operation is
reclassified as quiet because its arithmetic result happens to be unchanged.

## Remaining dependent changes before dispatcher widening

The following work is outside this prerequisite and has not been performed:

1. Change `TSO64.Decoded.locked`, `decode` and `locked` in `TSO64/Model.lean` to the generic
   instruction/decoder/step, capture `instruction.delta initial`, and preserve
   guarded current code fetch, original leases, code bounds, decode agreement,
   current `atomicFor` authorization and own-FIFO blocking order.
2. Generalize `TSO64.LockedEffect`, `locked_effect`, `locked_coupled`
   and `issue_effect`, then `TSO64.LockedEffect.wellFormed` and
   `TSO64.Origin.rmw`/`step_origin`, to `AddRMWMachineEffect`. Preserve exact
   installation, grant membership, resource frames and blocked-state equality.
3. Generalize `TSO64History.step_event_origin` and its consumers. The checked
   arithmetic event/history format can remain unchanged. The current
   `ArithmeticRMWOrigin64.of_step` must then lift the widened actual origin
   without tagging every event as XADD.
4. Lift `WordProjection.rmw_path_of_effect` from `FetchAddMachineEffect` to
   `AddRMWMachineEffect`, keeping its real-step premise and explicit
   lock/read/write/publication/unlock path. Review the corresponding
   `StepTrace` and label-extraction cases. Zero/unchanged updates still require
   that path; peer-FIFO behavior and blocked zero-event behavior must survive.
5. Choose a generic call adapter/emission contract before admitting ADD/INC
   scheduler observations. The present `FetchAddCalls64.Emission.point`
   requires the legacy XADD origin. Replacing that contract would require
   explicit XADD compatibility APIs for the existing `point_at` and
   `FetchAddABI64.Complete.point_at` clients. The `(cell, delta)` SysV entry and
   RAX/RET claims must retain their own entry/return premises.
6. Validate the widened dispatcher against the existing call, arithmetic and
   ABI regressions, then run the full-project audit and fresh kernel replay.
   Existing tests exercise full-width/zero deltas, aliases, source RSP,
   same-actor workers, authority failures and FIFO blocking. The common
   arithmetic contract also requires universal proofs over actual effects
   and endpoint reads.

## Validation

```sh
lake build EDSL.OS.ArithmeticRMWOrigin64 ManagedFetchAdd64Tests AddRMW64Tests
```

The two origin/call modules use warnings as errors, `autoImplicit=false`,
300000 heartbeats and recursion depth 128. Building these targets compiles
the contracts and existing regressions. The repository audit and fresh-kernel
procedure are described in [build and validation](validation.md).

The environmental model remains the existing abstract coherent WB RAM model,
with its long-mode, CET-disabled, stable-translation/no-alias and protected
resource assumptions. No physical CPU, Linux, source preservation, fairness,
progress or corpus-credit result is added.
