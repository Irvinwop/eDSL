# Counted atomic workers and collection

`OS.CounterThreads` models a finite registry of workers executing an exact
nineteen-byte assembly routine against current shared OS cells:

```asm
jrcxz done
body:
  mov eax, 1
  lock xadd DWORD PTR [rdi], eax
  loop body
done:
  mov eax, 0
  ret
```

The bytes are `e3 0b b8 01 00 00 00 f0 0f c1 07 e2 f5 b8 00 00 00 00 c3`.
RDI supplies one shared 32-bit counter address; full 64-bit RCX supplies that
worker's independently published iteration count. Every completed worker
returns zero. Zero count takes the guard directly to the return path, avoiding
the unsigned LOOP underflow that would otherwise execute 2^64 iterations.

This extends the [locked fetch-add](fetch-add.md) and
[shared-handle](atomic-handles.md) contracts to mutable worker contexts,
instruction scheduling, whole-workload counting and checked collection. It
verifies this assembly profile directly; no C/C++ source-loop preservation
theorem is inferred.

## Resources and actual machine steps

Checked `spawn` validates the executable bytes, readable return stack and
canonical return target. It acquires separate code/stack read loans and an
actor-specific atomic handle. The root parent is principal zero. Creation
unavailability, wrong parents, identity collisions, unsupported code and
resource failures are explicit rejected outcomes.

Each worker stores its immutable entry context, current private context, return
target, phase and resource IDs. The seven phases distinguish the entry guard,
MOV preparation, locked addition, backedge, final MOV, RET and completion.
`PrivateValid` relates the current PC, RDI, RCX, RSP and relevant RAX value to
that phase. Arithmetic flags come from the actual executed addition; the
invariant does not replace them with a fixed value or cache spawn-time data.

`dispatch` decodes and executes one actual `X86.step` against the then-current
shared cells. The addition also passes checked handle authorization and
`Atomics.fetchAdd ... 1`. `AdvanceEffect.machine` and `dispatch_machine` prove
that the full resulting projected machine state, including flags and memory,
is the actual decoded step. `AdvanceEffect.memory` proves that only a recorded
addition event changes shared cells, with actual old/new words and
`new = old + 1` modulo 2^32.

All admitted spawn, dispatch, join, guarded resource mutation and idle steps
preserve `WellFormed`; peer private contexts and protected code/stack authority
are framed. Completion keeps the handle and both loans live until a successful
join. Join requires the recorded parent and completed phase, returns zero,
closes the handle, finishes both loans and removes the worker. Joined thread,
handle and loan IDs remain revoked through every later admitted history.

These are logical resource authorities. Nat principal labels do not authenticate
native threads, and unchecked raw accesses are outside the guarded history.
Even a zero-count worker requires valid counter authority under this uniform
lifecycle contract.

## Counter, cost and progress theorems

`schedule` consumes a supplied finite list of worker selections and retains
the actual labeled RMW events. It rejects selections of missing or already
completed workers. Peers may preempt between any two instructions.

| Theorem | Guarantee under its explicit premises |
| --- | --- |
| `schedule_remaining`, `completed_selection_count` | Each successful own selection consumes one remaining instruction; an entry-phase worker requires exactly `3*count.toNat+3` selections through RET |
| `schedule_completes`, `run_and_join` | Sufficient successful own selections complete a worker; a finite own schedule and checked zero-valued join exist for every well-formed live worker |
| `completed_event_count` | A worker started at entry that completes emits exactly its published full-RCX iteration count |
| `schedule_counter` | For workers sharing one address, any successful supplied dispatch schedule leaves the counter at independently observed initial value plus actual event count modulo 2^32 |
| `completed_total_events`, `completed_counter` | A schedule completing every initially entry-phase worker emits the sum of their published requests and leaves the counter at initial plus that sum modulo 2^32 |
| `collect_values`, `collect_resources`, `collect_revokes` | Successful batch joins return zeros, preserve OS cells and revoke selected workers' handles and loans |
| `collect_all` | Every finite well-formed registry of completed workers can be fully collected, leaving no worker records |
| `finish_all`, `finish_collect_counter` | Every finite admitted entry-phase workload has a constructive completing schedule and complete checked collection with the specified counter result |

The registry's `nextThread : Nat` bounds all live IDs under `WellFormed`.
`requested` sums full 64-bit iteration requests over this finite registry;
there is no fixed two-worker or bounded-count theorem restriction. The proofs
use induction and a decreasing natural variant rather than unrolling every
possible count.

The exact cost counts modeled user instructions, including the guard, final
MOV and RET. It excludes spawn/join, scheduling, kernel work, contention delay,
cache effects and elapsed time. It proves no minimum instruction count.

Constructive finite progress is separate from arbitrary scheduler behavior.
An admitted infinite idle trace shows why the model cannot promise completion
without sufficient worker scheduling. No wall-clock or fairness-delay bound
is supplied.

The aggregate result covers dispatch-only schedules followed by checked
collection. Mixed histories preserve resources and private contexts, but the
counter sum does not silently extend across arbitrary stores after all handles
close. Unrecorded interference, general weak-memory outcomes and unmanaged
aliases remain outside its hypotheses. The result is explicitly modular;
natural-number counting additionally needs a separate no-overflow bound.

## Exact artifact certificates

`EDSL.CounterCertificate.sound` packages two independent obligations for a
prepared entry-phase workload targeting one independently observed counter:

- `Execution` provides a constructive actual instruction schedule and full
  collection yielding the specified counter, zero results and empty registry.
- `CompletedSpecification` proves that every successful supplied schedule that
  completes the workers, followed by checked full collection, has that outcome.

`Prepared` supplies the atomic-world invariant, live-ID bounds and resource/
private-context prerequisites. Code binding supplies the remaining executable
premise. The certificate does not infer ownership, create native threads or
verify argument publication.

```sh
lake build EDSL edsl-certify-counter
lake exe edsl-certify-counter WORKER.bin artifacts/CounterRaw.lean
lake exe edsl-certify-counter --elf WORKER.elf artifacts/CounterELF.lean
```

Raw mode embeds every observed byte and retains explicit per-worker `CodeAt`
premises. ELF mode embeds the complete file, checks the restricted parser and
exact entry window, derives code binding through modeled installation and
requires freshness, the actual shared loaded-space equality and worker entry
addresses. The caller still supplies its data/stack/resource contracts.

Both modes run Lean with warnings as errors and transitive axiom auditing.
Exit zero means the generated theorem checked; exit three means unsupported,
two means invalid arguments and one means checking failed. A file left by a
failed check is not a certificate of success. Other correct encodings reject.

## Evidence and remaining platform work

The owned Lean regressions enumerate all 924 instruction interleavings of two
one-increment workers. Independent expectations derive each worker's addition
position from its third schedule selection, rather than using emitted events
as their own oracle. They check wraparound, event order, worker-specific flags,
guard bytes, final registers, separate return stacks and checked collection.
Zero and unequal iteration workloads exercise the guard and repeated backedge.
Lifecycle checks reject joins in every incomplete phase, stale IDs, unavailable
creation, invalid authority, missing/non-executable RET and a denied final data
byte. Paused workers block conflicting code/stack/data changes while allowing
unrelated allocations and stores.
Lifecycle cases reject premature joins at every incomplete phase, extra
dispatch, wrong parents, stale IDs after respawn, explicit creation failure and
invalid authority after loan acquisition. Conflicting code/stack/data mutations
are blocked while unrelated checked allocation/store remains usable between
instructions. Wrong backedges, missing/nonexecutable RET and denied final
operand bytes also reject.
`CounterThreadsWitness.all_words_and_counts_finish` independently constructs
checked adoption and two successful spawns for every initial 32-bit word and
every pair of full 64-bit counts, then obtains actual completion and collection
with the independent initial-plus-requested-sum result. This provides symbolic
nonvacuity beyond the finite interleaving cases.

```sh
lake env lean -DwarningAsError=true tests/CounterThreads.lean
lake env lean -DwarningAsError=true tests/CounterThreadsWitness.lean
bash scripts/verify-counter-workers.sh
bash scripts/check-audit.sh
lake env leanchecker --fresh EDSL
```

The owned integration assembles and links the routine with Clang and GCC,
producing four raw/full-ELF certificates before native execution. Each compiler
artifact is observed across 42 sequential initial/count pairs and four
eight-thread workloads with distinct requests, including zero and modular
wraparound. The observer checks both adjacent guard words, exhausted RCX and
zero returns against the independently published sum. Provenance retains
compiler/linker versions, arguments, disassembly and artifact hashes.

Synthetic guard/backedge, missing-LOCK, wrong-width, wrong-operation, wrong-addend,
wrong-return and truncated candidates must reject, as must a changed full ELF.
Four terminating semantic mutants additionally fail the independent native
observer. Unsafe control-flow mutants are never executed. Only owned synthetic
artifacts enter the CI output directory.

The implementation uses the existing restricted x86-64 canonical-address,
aligned coherent-WB-RAM and stable-translation profile. Native start/join,
publication, context switching, runtime cleanup, the Linux implementation and
general x86/C++ weak-memory refinement remain external contracts. A native
stress test or successful assembly certificate does not discharge them.
Protected invariants, locks and wait/wake remain separate implementation work.
