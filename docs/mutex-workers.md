# Complete mutex worker execution

`EDSL.OS.MutexReplay` proves finite instruction interleavings of an owned
37-byte x86-64 worker. The lock address is in RDI, the protected payload address
in RSI, and each worker requests a modular 32-bit increase of two:

```asm
retry:
    mov eax, 1
    xchg DWORD PTR [rdi], eax
    cmp eax, 0
    jne retry
    mov eax, DWORD PTR [rsi]
    lea eax, [rax + 1]
    mov DWORD PTR [rsi], eax
    lea eax, [rax + 1]
    mov DWORD PTR [rsi], eax
    mov eax, 0
    xchg DWORD PTR [rdi], eax
    mov eax, 0
    ret
```

The two stores deliberately allow an even payload invariant to be open while
the holder runs. A peer can attempt acquisition during that interval. Its
actual busy XCHG writes 1 over 1, returns the old word, changes CMP flags, and
branches back. The holder's guard is recorded at the successful XCHG, before
CMP or the branch. Release checks the actual payload invariant and revokes it.

## Implemented guarantee

`perform_refines` connects every successful admitted operation to one complete
`X86.step` result, including registers, flags, RIP, the RMW event, and the
entire memory projected from the resulting OS cells. It has no assumed machine
result premise. `dispatch_refines` also retains executable-byte binding and
unchanged peer contexts. `schedule_trace` composes those steps in the supplied
order; every dispatch projects current shared memory afresh.

`completed_post` proves an independent endpoint for every successful supplied
schedule that completes all workers from an admitted entry cohort:

- Every original worker has completed its actual RET with RAX zero and no guard.
- The original lock address contains zero and the registration is unheld.
- The original payload address contains `initial + 2 * workers` modulo 2^32.
- The original payload invariant holds on that final value.

The theorem uses an initial `Invariant` and `ClosedUnderTwo`: the chosen payload
predicate must be preserved by modular addition of two. Even values form one
nontrivial example; the fixture also admits every initial 32-bit word with the
unrestricted predicate. The worker invariant records private control, guard
authority, the saved payload in EAX, and whether the first or second protected
store has run. It does not encode the final result.

`dispatch_invariant` and `schedule_invariant` prove preservation. Peer stores
and releases are excluded by guard exclusivity and distinct immutable principals.
Busy exchanges preserve the holder's observed payload. A credit of 0, 1 or 2
counts each worker's actual protected stores; `schedule_accounted` relates their
sum to current payload cells. Every completed worker contributes two, yielding
`completed_total`. `release_admitted` discharges the closing-payload condition
before release from the program invariant and actual guarded store results.
There is no final-value checker premise in these results.

The executable `verify`/`checkPost` route remains available for individual
finite executions. `verify_sound` proves its trace and endpoint. The generic
theorems independently establish the endpoint from program invariants, and the
architectural coverage below removes successful checked replay as a premise.
A rejected schedule or failing invariant is not a security finding.

Every accepted trace also projects to `Mutex.History`. From an initially
well-formed mutex/resource state, its final mutex/resource state is well formed.
The existing history theorems preserve live read loans and permanently revoke
released guards. The replay layer has no transitions for raw stores, external
guard release, unregister, arbitrary loan completion, or replacement OS state.

## Architectural coverage and completion

`OS.MachineThreads` contains full shared machine memory, each worker's private
registers/flags/RIP, and an actual-RET marker. Its dispatcher selects an existing
worker that has not returned, calls only `X86.step` on that context and current
memory, and installs the entire resulting memory and context. It has no mutex,
phase, guard, loan, expected-opcode or code-check gates. Missing/already-returned
selections, architectural faults and syscall boundaries are explicit errors.

`dispatch_enabled` constructs the next checked operation from `Invariant` and
`ExecutionReady` for every existing unfinished worker. `dispatch_erases` maps
that operation to exactly the instruction-only dispatcher. Determinism then
gives `dispatch_lifts` and `schedule_lifts`: every finite architectural execution
from an admitted state has the same checked replay, contexts, memory and RMW
events. `machine_prefix` retains the invariant and readiness at every prefix.
Every subsequent existing unreturned selection is enabled; it cannot fault or
reach a syscall boundary. The coverage theorem does not filter architectural
executions through assumed checked-replay success.

`machine_completed_observations` exposes the independent modular total,
unlocked word, zero returns, cohort size and exact cost directly on the bare
machine result for an initial entry cohort. Completion observes actual RET
markers. Admission still requires the initial invariant, execution readiness
and `ClosedUnderTwo`.

`cohort_completion` constructs a completing schedule from any admitted
intermediate state: finish the tracked holder first, then the remaining workers.
It makes no new busy exchanges and takes exactly the current `potentialSum`,
at most `15 * workers` future instructions. `entry_cohort_completion` constructs
a zero-busy schedule of exactly `13 * workers` instructions for an entry cohort.
`machine_completion` and `machine_entry_completion` carry those witnesses to
the instruction-only scheduler. These are existence proofs; arbitrary schedulers
can continue choosing a busy peer forever. No fairness or elapsed-time bound
is inferred.

## Cohort and resources

`spawn` appends an immutable logical worker index, with principal `index + 1`.
It checks exact code, RDI/RSI operands, actual readable return stack and canonical
return address, then borrows executable code and stack allocations through the
mutex protocol. Workers can share read-only code and return-stack storage.
Creation is restricted to the pre-execution phase; nested spawn, detach and
individual join are unsupported.

`empty_invariant` and `spawn_invariant` establish the invariant from actual
successful setup operations. They preserve existing workers and payload cells,
and each new worker starts with zero credit and no guard.

`LoanReady` records actual stored code/stack loans under each worker's principal,
with distinct identifiers for its two loans. `empty_loanReady` and
`spawn_loanReady` establish it through checked creation; `schedule_loanReady`
preserves it. One stored loan cannot have two different borrowers, so loans of
different worker indices cannot alias. No separate assumed global disjointness
oracle is used.

`ExecutionReady` strengthens loan provenance with the actual executable bytes,
the readable saved return word and its canonical target. Checked spawn establishes
these facts. `WorkerExecutionReady.frame` uses the retained current loan records
and actual borrowing history to preserve both bytes and permissions;
`dispatch_executionReady` and `schedule_executionReady` retain them throughout
execution. Readiness is an initial/current execution contract, without a premise
about a future step succeeding.

`collect_enabled` constructs checked collection for every completed ready
cohort. `completed_collection_exists` combines that existence result with the
program invariant and total theorem. It proves zero retained machine returns,
unchanged resource cells, final payload/lock contracts, revocation of exactly
the original code/stack loan identifiers, and preservation of every unrelated
loan record. The concrete validation also checks that code mutation is denied
before collection and enabled afterward.

The symbolic fixture proves actual checked adoption, registration and both
spawns for every initial 32-bit word under the unrestricted predicate.
`admitted_valid` establishes the program invariant, `admitted_loanReady` derives
loan provenance through those actual operations, and `admitted_total` applies
the generic total theorem. `Examples.MutexExecution` derives
`admitted_executionReady` from checked creation and constructs architectural
completion for every initial word, including completion after any admitted
architectural prefix.

The logical actor mapping is not authenticated pthread/kernel identity.
External users must supply initial ownership/registration and cannot interpret
an arbitrary hand-constructed state as a proved setup. The Lean fixture uses
actual checked adoption, registration and spawn operations.

## Artifacts and validation

`edsl-certify-mutex-worker [--elf] INPUT CERTIFICATE.lean` admits exactly this
worker. Generated certificates embed observed bytes and apply `machine_sound`
to establish `MachineSpecification` under the initial invariant, execution
readiness, entry-cohort, initial-observation and predicate-closure contracts.
Every architectural prefix lifts and retains readiness/enabledness. Every
completed execution has the direct memory/return/cost observations and admits
checked collection with precise original-loan revocation. A zero-busy entry
completion schedule exists. Certificates retain `universal_sound` and the
individual checked-replay theorem, and run the axiom audit. ELF certificates
additionally embed the full file, prove parsing, check the executable entry
window, and expose fresh-loading/code-binding theorems. The CLI certifies the artifact profile;
executions need the stated OS admission contracts. It does not claim that the
linked ELF is a standalone process or verify its start/runtime code.

```sh
lake build edsl-certify-mutex-worker
lake env lean -DwarningAsError=true tests/MutexISA.lean
lake env lean -DwarningAsError=true tests/MutexReplay.lean
lake env lean -DwarningAsError=true tests/MutexInvariant.lean
lake env lean -DwarningAsError=true tests/MutexExecution.lean
bash scripts/verify-mutex-workers.sh
```

The owned assembly is assembled independently by Clang and GCC. Raw and full-ELF
certificates add four distinct artifacts. Native C observers execute both raw
artifacts across sequential wraparound cases and eight-thread workloads, checking
the public +2 contract, zero returns, unlocked final lock and adjacent guards.
They do not reconstruct or certify the observed native scheduler trace.
Four safe terminating semantic mutants independently fail those observations;
byte-profile checks also reject changed control flow, release and truncation.

The two-worker Lean regression executes 30 actual instructions, including one
busy retry and five RMW events. It observes the intermediate odd protected word,
the busy peer's retry, wraparound from `0xfffffffe` to 2, real stack returns,
loan pinning and reclamation. The endpoint checker rejects incomplete schedules;
architectural prefix coverage still applies to them.

The generic-invariant suite also forces two busy retries, including one after
the payload load and another between stores. It covers odd inputs under the
unrestricted predicate, the even invariant's open/restored phases, different
cohort sizes, actual RET completion, and costs derived from real busy events.
`tests/MutexExecution.lean` adds symbolic architectural completion, independent
contended memory/return/event observations, completion from a paused busy CMP,
and explicit missing/returned-worker errors. Removing execute permission from
RET or readability from the last return-stack byte produces the precise
architectural fault, demonstrating that the bare dispatcher performs real
instruction fetch and stack access.

`completed_cost` and architectural lifting prove exactly
`13 * workers + 4 * busy exchanges` user instructions for every completing
admitted architectural schedule from an entry cohort. A potential decreases at
ordinary steps and accounts for four additional instructions at each actual
busy exchange. `machine_entry_minimum` proves that every completed entry
execution takes at least `13 * workers` instructions, and the constructed
zero-busy schedule attains that
bound. This is a matching instruction-count lower bound for this fixed routine
across schedules. It does not compare alternative implementations or bound
cycles, micro-ops, blocking/futex behavior or waiting.

## Physical boundary

The separate [buffered proof](store-buffers.md) now covers every successful
`OS.TSO` issue/drain trace through `OS.MutexTSO`. Its additional admission
requires aligned payload and non-executable lock/payload destinations. A separate
generated `TSOSpecification` provides prefix lifting, direct completed physical
observations, positive resource collection, publication and constructive
continuation. The immediate-visibility `MachineSpecification` above retains its
original meaning. Busy exchanges are real retired instructions; blocked release
and drains stutter on the entire logical state. Completion observes actual
return markers and derives empty queues for this byte profile.

Both are coherent-RAM model contracts. They do not establish arbitrary native client
compliance, pthread start/join, the Linux kernel, interrupts or exceptions. XCHG's physical
interpretation requires the [atomic profile](atomic-exchange.md). The guarded
invariant and ownership checks are admission conditions; these bytes do not
execute those checks. CMP/JNZ semantics follow the
[Intel instruction reference](https://cdrdv2-public.intel.com/868140/253666-089-sdm-vol-2a.pdf).
