# Worker resource cleanup

The TSO64 lifecycle API removes completed worker records and releases their
logical atomic handles and code/caller loans. It operates on the current world
at each removal, preserving the memory left by the execution.

This API is administrative post-processing after instruction execution. The
scheduler still uses its existing issue/drain actions. Native Linux thread
joining, actor authentication, allocation deallocation and physical machine
refinement remain outside this contract.

## Reusable API

Import `EDSL.OS.TSO64.LifecycleCohort` for finite cleanup, or
`EDSL.OS.TSO64.LifecycleSchedule` to transport resource separation across
an actual successful schedule. Both modules expose their underlying lifecycle
operations and proofs through imports.

- `Lifecycle.release` checks a returned worker with an empty FIFO, closes its
  single atomic handle, and finishes its original code and caller loans.
- `Lifecycle.retireLast` performs that release and removes the last record.
  Earlier worker slot indices remain fixed.
- `Lifecycle.retireN` repeats the operation a specified number of times.
- `Lifecycle.retireAll` removes the number of workers present at entry.

Errors return `Except.error` without exposing a partially updated world.
A missing worker, running worker, pending store, unsupported handle-list shape
or failed current resource check can reject cleanup.

## Admission and guarantees

`Lifecycle.Ready` describes current returned phase, an empty FIFO, exactly one
atomic handle, current resource validity and different code/caller loan IDs.
`Lifecycle.Separate` requires that a retained peer names none of the capabilities
being released. Actor labels need not differ; they are logical principals,
not authenticated native identities.

`retireAll_ready` takes current well-formedness, Ready for each worker and
pairwise separation in last-to-first retirement order. It constructs successful
cleanup, an empty worker list and a well-formed resulting state. The result
contains the workers' actual private contexts in removal order. The proof
preserves the entire current ownership world, including RAM, permissions,
allocation registry, ownership epochs and allocation frontier, and preserves
the atomic-cell registry. Every removed worker's original handle and both
loans are revoked in the final world through a checked OS history.

Persistent cells, allocations, allocation tickets and ordinary ownership grants
remain. A record with several atomic handles needs a broader release contract
before it can use this cleanup API.

## Apply cleanup to compiler-produced counters

Import `EDSL.Corpus.V1.CounterRetirement`. Clients supply their existing checked
counter cohort, original cleanup shapes and pairwise separation, initially
empty queues and an actual successful schedule whose workers have returned.
`counterCohort_retireAll` derives current Ready, empty queues, resource validity
and separation from that execution, then constructs the cleanup operations.
There is no assumed future resource manifest or future cleanup success.

`two_completed_retired_total` additionally retains the independent two-counter
admissions, exact initial slots and worker universe, registered common target
and initial RAM read. It derives the modular sum in the actual cleanup world:

`final.toNat = (initial.toNat + left.iterations.toNat + right.iterations.toNat) % 2^64`.

The instruction schedule is a premise of these counter theorems. Cleanup
completion does not establish that the programs terminate. The modeled
long-mode/CET-off, coherent scalar WB RAM, stable translation/no-alias,
ownership and protected-loan assumptions remain explicit. Coverage scores do
not increase from these support results alone.

Build the reusable layer with `lake build TSO64LifecycleSupport` and the counter
adapter with `lake build CounterContractSupport`. Both belong to the full
catalogue, dependency audit and fresh certificate gate.
