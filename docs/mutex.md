# Protected payloads and a checked mutex protocol

`EDSL.OS.Mutex` implements a checked mutual-exclusion protocol over current OS
cells. This first profile registers one mutex at a time: an aligned 32-bit lock
word and a protected 32-bit payload in a distinct allocation. It combines
existing exact XCHG/load/store binary theorems with a resource and invariant
protocol. A complete native critical-section worker, weak-memory publication
and pthread/kernel implementation refinement remain separate work.

## Registration and resource discipline

`Config` records the owner, current lock/payload allocation tickets, both operand
addresses and an independently chosen local invariant `BitVec 32 → Bool`.
Registration checks current authority, complete contained writable operands,
atomic-address support, different allocation IDs, absence of read loans on both
allocations, lock value zero and the invariant on the actual initial payload.
`register_enabled` and `register_wellFormed` establish positive admission and
preservation of the resource invariant.

Both entire allocations remain reserved throughout registration, including
unlocked intervals. Checked ordinary mutations cannot store, release, transfer
or change permissions on either allocation. New read loans on either allocation
also reject, including loans on a disjoint subregion. Existing unrelated loans,
mappings and resources remain usable. `unregister` requires the recorded owner
and an unlocked mutex; it preserves cells and the guard-ID frontier and makes
the resources available to ordinary checked operations again.

`State` wraps `Borrowing.State` directly. The admitted transition surface is
register, acquire, protected store, release, unregister, guarded mutation,
guarded read borrowing, loan completion and idle. Raw lower-layer mutations,
outside atomic operations, fabricated states and resetting `empty` are not
history transitions. Existing `Atomics.State`/worker histories are not silently
merged with this separate mutex profile.

## Guards and the closed invariant

A `Lease` records an actor label and a fresh natural-number identifier. Only
an actual zero observed by `tryAcquire` grants a guard. Every attempt executes
its checked XCHG of the lock with one and retains its event: acquisition gives
0→1; contention and reentrant attempts give 1→1 with no additional guard.

Authorization compares the entire guard to the stored holder and checks its
actor. `exclusive` proves separately authorized guards have the same identity
and actor. Guard IDs never recycle across admitted histories, including
same-actor reacquisition and unregister/register cycles. `release_revokes` and
`released_for_history` prove permanent revocation of released copied guards.
These are logical authorities; actor labels do not authenticate native threads
and machine pointers do not carry guard IDs.
Guards are copyable proof values: exclusivity establishes one authorized
principal/guard identity, rather than a linear-token logic. Native mutual
exclusion additionally needs the client/runtime mapping from distinct workers
to distinct principals. The guard namespace belongs to one state history;
independent state roots and multiple simultaneous mutexes are not combined here.

`ValidMutex` relates the actual lock word to the recorded holder:

- Unheld: lock word zero and the invariant holds on the actual payload.
- Held: lock word one and the current guard is below the fresh-ID frontier.

`guardLoad` reads the current payload under exact guard authority. `guardStore`
may temporarily open the invariant. `release` requires the invariant on the
current payload, executes XCHG lock→zero and removes the holder. An invalid
closing value rejects. `History.closed` proves the invariant for every admitted
mixed history ending with an unlocked registration. `History.loan_stable`
retains the actual bytes and permissions of surviving unrelated read loans.

The invariant check is protocol admission, not an instruction implemented by
the XCHG routine. A program proof must establish the invariant before invoking
the release bridge. The implementation does not infer an invariant, prove an
arbitrary client respects guards, or prove a native runtime performs these
logical checks.

## Actual machine-code bridges and finite behavior

| Theorem | Exact supported operation |
| --- | --- |
| `tryAcquire_exchange32` | `89 f0 87 07 c3`, low32 RSI=1, full projected state and actual acquisition/busy event |
| `release_exchange32` | The same bytes, low32 RSI=0, with successful checked release and its current payload contract |
| `guardLoad_load32` | `8b 07 c3`, protected current word and two-instruction return |
| `guardStore_store32` | `89 37 c3`, protected word update and two-instruction return |

The exchange routines execute three user instructions with one RMW event.
Every bridge retains executable-byte binding, an accessible return stack and a
canonical return target; modifying operations also require code/stack separation.
The physical aligned coherent-WB-RAM and architectural restrictions from
[atomic exchange](atomic-exchange.md) still apply. There is no new memory-order
mapping. A separate [complete-worker replay layer](mutex-workers.md) now checks
finite instruction interleavings and proves preservation, completed modular
totals and retry costs from independent worker invariants. Dispatch enabledness,
constructive completion and native runtime correspondence remain further work.

`tryAcquire_enabled`, `guardLoad_enabled`, `guardStore_enabled` and
`release_enabled` provide positive behavior under their stated contracts.
`acquire_free` opens the invariant of an admitted unlocked registration.
`critical_cycle` constructs a real finite acquire, temporary store, restoring
store and checked release for every invariant-satisfying final value. The
temporary value is unrestricted; the final payload equals the independent
requested value and the guard is revoked. No whole-worker instruction count or
minimum-cost claim follows from composing these logical operations.

An admitted infinite idle trace shows that scheduling, eventual release,
starvation freedom and bounded waiting are not established. There is no futex,
blocking wait, cancellation, owner-death recovery, priority policy, multiple-lock
registry or deadlock-ordering proof in this profile.

## Evidence

`tests/Mutex.lean` checks two-actor handoff, real busy/reentrant RMW events,
modular values, temporarily invalid payloads, invalid release, wrong actors,
double release, same-actor stale guards, stale guards across re-registration,
whole-allocation reservations, unrelated allocation/store/borrowing, existing
readers, wrong ownership/epochs, aliased allocation identities and a denied
final payload byte. Its symbolic section constructs checked allocation adoption
and registration for every initial word satisfying any supplied local invariant,
then applies `critical_cycle` for arbitrary temporary/final values.

`scripts/verify-mutex.sh` re-certifies the existing Clang C/C++, GCC C exchange,
load and store artifacts before executing them in a native observer. First run
`scripts/verify-compilers.sh` to produce those owned artifacts. This reuses nine
existing certificate paths and adds no distinct artifacts. The subsequent
[complete worker replay](mutex-workers.md) adds four raw/full-ELF certificates.

Each compiler mode runs four eight-thread workloads with distinct published
request counts, adjacent payload guards, modular wraparound, exclusive-occupancy
observations and even-valued closed payloads. The observer yields while the even
invariant is temporarily open. A project-owned load-instead-of-store mutant
both fails certification and fails the independently calculated native total.
These observations do not prove the C observer, client loop, pthread lifecycle,
physical publication or general C/C++/x86 weak-memory correspondence.

```sh
lake build EDSL.All edsl-certify edsl-certify-process edsl-certify-counter
lake env lean -DwarningAsError=true tests/Mutex.lean
bash scripts/check-audit.sh
lake env leanchecker --fresh EDSL.All
bash scripts/verify-compilers.sh
bash scripts/verify-mutex.sh
```
