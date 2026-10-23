# Arithmetic RMW event origins

Import the common origin interface with:

```lean
import EDSL.OS.ArithmeticRMWOrigin64
```

The TSO64 scheduler defaults to XADD-only dispatch. Its explicit arithmetic
family also accepts ADD and INC. Both use the common event-origin interface
below; see [scheduler families](arithmetic-rmw-scheduler.md) for selection and
blocking behavior.

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

`Origin` existentially packages `Evidence` for an installed arithmetic RMW.
`of_step` lifts actual successful steps from either instruction family and
either authority profile. Its step premise includes the selected family and
profile and supplies the guarded dispatch evidence. An origin alone is not a
converse enabledness theorem.

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

## Call and loop contracts

The scheduler family is independent of a function's calling convention.
Existing fetch-add calls, returns and batch certificates still use the default
XADD family and retain their original RAX and ABI contracts. ADD and INC have
no old-value register destination, so they require their own entry/return
contracts before they can produce function or loop certificates.

The ordinary Resumable adapter does not yet compose atomic heads with ordinary
instructions. Whole-loop event counts, resource release and joins also need
separate proofs. Arithmetic origins and reference paths do not establish
those results or add frozen-corpus coverage.

## Validation

```sh
lake build EDSL.OS.ArithmeticRMWOrigin64 ManagedFetchAdd64Tests AddRMW64Tests
```

The origin and scheduler modules use warnings as errors, `autoImplicit=false`,
300000 heartbeats and recursion depth 128. Building these targets compiles
the contracts and existing regressions. The repository audit and fresh-kernel
procedure are described in [build and validation](validation.md).

The environmental model remains the existing abstract coherent WB RAM model,
with its long-mode, CET-disabled, stable-translation/no-alias and protected
resource assumptions. No physical CPU, Linux, source preservation, fairness,
progress or corpus-credit result is added.
