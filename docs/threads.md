# Managed read workers and instruction scheduling

`EDSL.OS.Threads` implements a first thread lifecycle contract over the existing
shared borrowing/ownership world. Workers run the actual checked `8b 07 c3`
load/RET profile, one machine instruction per scheduler selection. Spawn
publishes a supplied entry context and obtains internal loans for data, code
and return stack. Join returns retained machine RAX after RET and releases the
worker's three loans.

This is an abstract managed read-worker profile. It does not implement or verify
Linux `clone`, pthreads, context switching, locks, atomics or the roadmap's
shared-increment workload. Those remain required work. All implementation and
proof infrastructure here is Lean 4.

## State and API

`Context` holds private registers, RIP and flags. It has **no memory field**.
`Context.snapshot` constructs a machine state from the current shared OS space
at each dispatch. Worker phases are load pending, return pending and completed;
each stores the actual private context. Worker metadata records the parent,
entry, initially observed word/return address and three loan IDs.

`State` holds shared `Borrowing.State`, a monotone `nextThread` frontier and
optional worker records. Thread IDs are never reused. The manager principal is
0 and worker `id` uses the logical borrower name `id+1`. Freshness concerns this
thread registry; these Nat names do not authenticate callers, establish native
thread identities or prove freshness relative to arbitrary external principals.
The wrapper does not give read workers an API to mutate arbitrary allocations.

| API | Contract |
| --- | --- |
| `spawn state parent start available` | Require parent 0; check exact executable code, input word and return stack/target; acquire three readable contained loans; issue a fresh thread ID |
| `dispatch state id` | Execute exactly one `X86.step` using current shared memory; retain actual resulting registers/flags/RIP |
| `join state parent id` | Require stored parent and completed phase; return actual retained RAX and revoke only that worker's three loans |
| `mutate state operation` | Run an existing guarded borrowing mutation, retaining all worker loans |
| `schedule state selections` | Execute the supplied thread selections in order; missing/completed selections fail explicitly |

`Start` supplies the entry context and owner tickets for the data, code and
return-stack allocations. The loan windows contain respectively four, three
and eight bytes. The existing borrowing policy freezes each entire allocation,
even for subregion loans. Different workers may share code and overlap data
loans. Their return stacks may be separate; these read workers do not push or
write stack memory. Allocation ownership remains with the lender.

`available = false` models explicit resource failure before creation. This is
separate from invalid contracts and unsupported code. All operations return
`Except`; failed spawn exposes no partial thread or intermediate loan state,
including failure at the third loan. This is a functional contract, not a proof
of native allocation rollback or OS transactionality. No detach, cancellation,
nested spawn, worker-side syscalls, mutable workers or thread-ID recycling is
silently approximated.

## Invariant and machine correspondence

`WellFormed` requires borrowing well-formedness, every live worker ID below the
frontier and `WorkerValid` for each record. Validity requires three distinct
stored loan IDs with the worker's borrower name and the exact data/code/stack
windows. Current executable bytes, initial word and return target must still
match. Each phase's private context matches the corresponding instruction
boundary of the independent load contract.

Dispatch checks the current decoded operation as well as the outcome kind,
rejecting out-of-profile instructions even in manually constructed states.
`loading_step` and `returning_step` prove the two actual machine transitions.
`dispatch_loading` and `dispatch_returning` connect the executable scheduler to
those transitions; it neither invents the result nor reads from a birth-time
memory snapshot. `join_result` connects actual retained RAX to the published
word through the invariant. Code/stack/data protection is retained until join,
including after the worker completes but before its parent collects the result.

Every operation has well-formedness preservation. `dispatch_frame` proves peer
private contexts and shared resources unchanged by a worker's instruction.
`join_retains_peer` proves a join leaves every peer's internal loans intact;
shared allocations remain frozen while any peer loan remains. `join_loan_frame`
retains all other loan IDs, not only those owned by other workers.

The invariant's finite-registry assumptions are explicit. Raw constructors,
unmanaged `Borrowing.finishLoan`, direct world replacement and arbitrary
external machine accesses bypass this discipline. `Threads.Step` admits only
spawn, dispatch, join, guarded mutation and idle; its histories cannot terminate
a running worker's loans independently. The certificate CLI does not infer or
validate thread registries automatically.

## All histories and scheduling progress

`History.wellFormed` covers every admitted finite interleaving of workers and
managed environment operations. `spawned_join_value` starts from an independently
stated input-word read and proves that every later successful join returns that
word zero-extended into RAX. It allows intervening peer creation, instructions,
joins, unrelated mutations and idle delays. `two_spawn_join_values` composes
two independent input-word specifications through both spawns, arbitrary
interleavings and both joins. `History.borrowing` connects this
system to the existing resource-history proofs.

`joined_for_history` proves a joined thread ID stays absent permanently.
`joined_loans_for_history` proves its three loan IDs stay revoked across every
later admitted finite history. Joining one worker does not revoke another
worker's overlapping read authority.

`dispatch_enabled` and `join_enabled` provide positive enabled-operation results
under their invariant/phase premises. `two_dispatches_complete` exhibits a path
through both instructions and join. `schedule_remaining` counts each worker's
actual instruction selections independently of peers; `schedule_two_completes`
proves two selections of a load-pending worker suffice in any successful supplied
instruction schedule. These counts exclude spawn/join/kernel overhead and do
not establish a physical timing or optimality bound.

Safety does not imply an arbitrary scheduler completes a worker. `idle_trace`
exhibits an admitted infinite idle schedule. No scheduler fairness, OS progress
or unconditional termination is inferred. Schedules that select a missing or
already completed worker report failure; unsuccessful schedules are not silently
filtered into a completion theorem.

The shared memory projection is still the sequential ordinary-RAM model. The
new scheduler permits preemption between the load and RET; admitted mutations
cannot change any protected byte during that interval. This does not prove a
hardware atomic MOV rule, SC lowering, weak-memory consistency or native
publication barriers. Concrete thread creation/publication/join and CPU context
switch conformance remain environmental refinement obligations. General stack
lifetimes, TLS, reclamation after failures, mutable workers and synchronization
need their own semantics and proofs.

## Evidence

```sh
lake build EDSL
lake env lean -DwarningAsError=true tests/Threads.lean
bash scripts/check-audit.sh
```

Owned synthetic cases exercise all six instruction interleavings of two workers
reading different words in one shared allocation, separate return stacks,
shared code, joining one while the other remains protective, and successful
mutation only after both joins. Other cases cover premature/wrong/repeated
join, completed dispatch, stale IDs after later spawn, code/stack/data mutation
rejection, unrelated allocation/store between instructions, explicit resource
failure and failure after two internal loans were prepared. A malformed-state
case rejects an actual memory-writing instruction that the raw machine model
successfully executes, keeping unsupported dispatch effects explicit.

A symbolic adopted caller-space witness admits every 32-bit input through
checked spawn, both actual instructions and join. Another theorem preserves its
result across every admitted intervening finite history. These checks add no
new compiler encoding or native threading claim. Existing exact-byte compiler,
ELF, process and loop integrations remain separate evidence for their profiles.
