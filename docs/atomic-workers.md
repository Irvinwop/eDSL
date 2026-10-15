# Mutable atomic-worker lifecycle

`EDSL.OS.AtomicThreads` executes the exact `89 f0 87 07 c3` exchange routine
under an abstract spawn, scheduling and join contract. Workers share current OS
memory and keep registers, RIP and flags private. One dispatch executes one
actual decoded MOV, XCHG or RET. Peers may run between any two instructions.
The old word returned by XCHG is captured at that instruction, rather than at
spawn, and remains the worker's private result while peers change the cell.

This extends [shared atomic handles](atomic-handles.md) to mutable workers. The
separate [read-worker module](threads.md) retains its existing load/RET profile.
Neither lifecycle is a proof of native pthreads, clone or CPU context switching.

## Operations and resource ownership

`State` contains an `Atomics.State`, a monotone `nextThread` frontier and stored
workers. A worker retains its parent, immutable input context, return target,
atomic handle, code loan, stack loan and current phase. Logical worker principal
`identifier + 1` is distinct from root principal 0.

| Operation | Checked behavior |
| --- | --- |
| `spawn` | Require root parent 0, available creation resources, a fresh ID, exact executable code and a readable canonical return target; acquire two ordinary read loans and one actor-specific atomic handle; publish a preparing worker |
| `dispatch` | Decode and execute one expected instruction against a snapshot of current shared cells; return an actual RMW event only for XCHG |
| `join` | Require the stored parent and completed phase; return retained machine RAX, close that worker's handle, finish its two loans and remove its record |
| `mutate` | Apply an independently checked ownership mutation through atomic reservation and ordinary-loan guards |
| `schedule` | Execute a supplied list of thread selections and retain emitted `(thread ID, AtomicEvent)` pairs in execution order |

The four phases are preparing, exchanging, returning and completed. MOV copies
low32 RSI into zero-extended RAX; XCHG swaps that replacement with the current
four-byte cell; RET uses the protected return stack and captured old word. Flags
and unrelated registers are preserved. Completion retains the handle and both
loans until join, so a completed but unjoined peer still pins the data allocation.

Code and stack loans freeze their entire allocations under the existing read
discipline. Each data handle reserves its entire allocation against ordinary
stores, permission changes, transfers, release and new read loans. Multiple
workers may hold handles for the same supported word, with their distinct actor
identities. The existing aligned coherent-WB-RAM profile and handle compatibility
checks apply. There is no data read loan and no invariant fixing the shared
data value.

All operations are pure checked transformations. A failed spawn exposes no
partially acquired loans or handle; the explicit creation-failure flag also
returns an error. This does not model native resource acquisition or prove a
native rollback implementation. Dispatch rejects missing or completed workers;
join rejects missing workers, wrong parents and incomplete phases. The admitted
worker history contains only successful spawn, dispatch, join, guarded mutation
and idle steps. It excludes arbitrary raw atomic exchanges, issuance, closure
and loan operations, including operations on any nonworker handles in the
initial world. Internal resource release belongs to the lifecycle.

## Checked results

`WellFormed` combines the atomic-world invariant with fresh live worker IDs and
`WorkerValid` for each worker. Each valid worker has matching stored authority,
two distinct live loans, exact executable bytes, a stable readable canonical
return target and the private context appropriate to its phase. The invariant
does not require the original data word to survive peer exchanges.

Named proof entry points:

- `spawn_wellFormed`, `dispatch_wellFormed`, `join_wellFormed`,
  `mutate_wellFormed` and `History.wellFormed` preserve the invariant.
- `preparing_step`, `returning_step` and the reused `Atomics.exchange_step`
  connect all three phases to actual machine semantics. `dispatch_atomic_spec`
  binds the emitted event to the original current cells, projected OS update
  and selected worker's captured old word.
- `dispatch_frame` preserves peer private contexts. `History.atomics` projects
  every admitted mixed worker history into the underlying atomic history,
  retaining its handle and loan guarantees.
- `dispatched_join_value` proves every successful later join returns the actual
  XCHG event's old word, zero-extended to 64 bits, despite arbitrary intervening
  admitted peer, lifecycle and resource actions. `joined_captured_value` states
  the retained-result rule directly from a captured word.
- `joined_for_history` and `joined_resources_for_history` permanently revoke the
  joined thread ID, its atomic handle and both loan IDs across every later
  admitted finite history, including fresh creation.
- `dispatch_enabled` admits another instruction for each well-formed unfinished
  worker; `join_enabled` admits root collection of each well-formed completed
  worker. `schedule_own_enabled` supplies a successful finite schedule for the
  worker's remaining instructions; `three_dispatches_join` supplies three own
  dispatches and a successful join from every well-formed preparing worker.
  `three_dispatches_spec` binds that path to an independently observed initial
  word: its singleton event records the old word and replacement, join returns
  the zero-extended old word, and the final shared cell holds the replacement.
  `schedule_remaining` counts actual selections, and
  `schedule_three_completes` proves three selections of a preparing worker
  suffice in any successful supplied instruction schedule with peer preemption.
  `idle_trace` witnesses an admitted infinite schedule without progress.

`schedule_chain` covers arbitrary successful **dispatch-only** schedules when
`AllAt` says every live worker targets one specified address. An independent
initial-memory observation starts a `ValueChain` of actual emitted events:
each event reads the preceding event's replacement. MOV and RET leave the
shared cells unchanged. `schedule_conservation` proves the permutation

```text
initial cell :: all event replacements
    ~ final cell :: all event old returns
```

This counts duplicates and quantifies over supplied schedule lists without a
fixed worker count or instruction bound. It is a value-flow theorem, not a
counter algorithm, lock protocol or minimum-operation theorem.

The mixed-history result and resource proofs have broader scope than this
final-memory chain. Joining the last handle can permit an ordinary store before
later creation, so arbitrary mixed histories cannot inherit the chain without
a continuously surviving reservation or explicit framing of intervening actions.

## Evidence and boundary

```sh
lake build EDSL edsl-certify edsl-certify-process
lake env lean -DwarningAsError=true tests/AtomicThreads.lean
bash scripts/check-audit.sh
lake env leanchecker --fresh EDSL
```

Owned regressions cover all twenty order-preserving interleavings of two real
three-instruction routines. Independent expected results check both possible
exchange orders, old returns, final word, neighboring guard word, return stacks,
RIP, flags and exact actor-labeled events. Further cases cover premature joins
at every phase, extra dispatch, wrong parent, stale IDs after respawn, creation
failure, failure after loan acquisition, protected code/stack/data, unrelated
allocation and store between instructions, changed code and a denied final
data byte. Existing compiler integration still generates 32 certificates;
this lifecycle adds no new native runtime certificate.

Symbolic witnesses build a well-formed owned world through checked adoption
for every initial and replacement 32-bit word, successfully spawn the worker
and observe the independent initial word. `all_words_join` uses the general
specification theorem to exhibit three successful actual instructions, the exact
singleton event, a checked join returning the old word, the final replacement
and preserved well-formedness for every such pair.

The resource identities and actor numbers are constructible proof data. Raw
machine stores or exchanges, unmanaged aliases, raw internal resource release
and arbitrary outside interference bypass the admitted history. Finite registry
scans rely on explicit well-formedness; this is not a global validator of arbitrary
manually constructed states. The certificate CLI does not infer worker
registries or certify a native start/join implementation.

Native argument publication, creation/join failure behavior, context switching,
TLS, cancellation, nested spawn, authentication and concrete runtime/kernel
refinement remain obligations. General x86 ordering and C/C++ memory-model
preservation are not established by these instruction interleavings. Operation
enabledness and selection counts provide no fairness, elapsed-time, reclamation
or unconditional completion guarantee. Protected invariants, shared-counter
algorithms, locks and wait/wake protocols remain later work.
