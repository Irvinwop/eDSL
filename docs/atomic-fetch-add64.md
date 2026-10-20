# Full64 fetch-add foundations

These Lean APIs establish full64 arithmetic, exact instruction dispatch and
current OS authority as reusable pieces. They also supply an independent modular
counter checker and exact names/windows for the two frozen compiler files.
Their [complete concurrent composition](concurrent-fetch-add-certificates.md)
now certifies the two frozen fetch-add windows under the explicit managed
closed-batch profile. Conditional corpus coverage is **5/40 functions,
10/80 compiler artifacts and one distinct concurrent function**.

`X86.fetchAddQWord` returns the entire current old word and writes the sum modulo
2^64. Even a zero input requires all eight operand bytes to be present and
writable. Theorems establish natural-number modular arithmetic, exact failure
classification, readback, permission retention and outside-byte/code frames.
Failure exposes neither a replacement state nor an event.

## Exact instruction family

`X86.LockedAdd64` admits `F0 REX.W 0F C1 /r`, with one REX byte `48`–`4f` and
mod=00 direct GPR addressing. Low r/m fields 0, 1, 2, 3, 6 and 7 provide twelve
low/high-bank bases. All sixteen source registers are supported. REX.R and B
select source/base independently; X is retained in exact bytes and has no SIB
index to extend. SIB, displacement, RIP-relative, other-width and other-prefix
forms fail closed.

The decoder fetches actual current executable bytes. Its bidirectional code
binding, no-wrap/canonical gates and machine step are proved. Address and input
come from the prestate, including source/base aliases and source RSP. The actual
source receives the full old word; ADD updates all six arithmetic flags; RIP
advances by five. Other registers, permissions and outside bytes are framed.
The operand footprint is exactly one `.rmw8`; decoder fetches and validation
queries remain separate. This is a separate dispatch API, outside Sequential.

The implementation eagerly fetches five bytes before validating the encoding.
Its error theorems describe that explicit policy, not Intel exception-priority
equivalence. Unsupported address profiles and executable operands are denied.

## Current OS resources

`OS.Atomics64.fetchAdd` authorizes a current actor/handle/cell, then performs the
checked full64 mutation. The handle stores identity rather than a value snapshot.
Authorization rechecks owner, epoch, whole-eight-byte containment, every required
permission and nonexecutable data, also for zero input. Allocation reservations
exclude ordinary writes, loan readers and legacy32 atomic use on the allocation.
The response retains actor, handle, persistent cell and the typed arithmetic
event. There is no conversion to a discarded-old or DWORD event.

`fetchAdd_step` and `FetchAddMachineEffect` in
`OS.AtomicFetchAddMachine64` couple the OS operation to actual LockedAdd64
decode/step. They establish equality of the entire current and final RAM
projections and complete events, plus the actual source write, flags, RIP,
footprint and resource frames. Enabledness derives both successes from present
well-formedness, authorization, operand binding and actual code. It assumes no
future successful mutation or desired successor invariant. The converse still
requires OS authorization: raw readable/writable CPU memory creates no authority.

All allocation and loan records, registries and frontiers are retained. Original
caller-slot reads survive. A source-RSP write preserves the original caller loan
at its original address; it supplies no replacement-slot loan, unchanged RSP or
RET-enabledness claim. Arbitrary sources also carry no general ABI promise.

## Independent object contract

`Concurrency.ModuloCounter` defines, for arbitrary width, initial value and
invocation input:

```
response = prior
next.toNat = (prior.toNat + input.toNat) % 2^width
```

Its separate executable evaluator is proved sound and complete for an inductive
sequential relation. Fold, deterministic-final-state and unbounded-input-sum
modulo laws follow. `checkComplete` composes it with the existing complete-call
protocol: identity/actor/input/output matching, unique points, complete strict
invocation/point/response intervals and extension of real-time order. It checks
the supplied chronological point order, rather than searching for another order.

These are logical labels. No machine, OS or TSO origins are inferred from them.
Actual issue events and invocation/RET boundaries must be connected separately
before a complete binary method can claim linearizability.

The [managed full64 scheduler and history adapter](managed-fetch-add64.md)
now connect current instruction/OS effects to buffered scheduling and selected-cell
arithmetic. The separate batch/certificate layer supplies complete methods and
frozen-function acceptance; the foundation APIs alone do not imply it.

## Frozen file identity

`Corpus.V1.FetchAddWindows` reuses the existing complete literal files, metadata
and load-layout proofs. Its kernel-checked adapter binds the exact unique global
FUNC name `c_atomic_fetch_add64`, complete declared extent and executable bytes.

| Profile | Address | File offset | Bytes | Symbol table / row |
| --- | --- | --- | --- | --- |
| Default GCC | `0x403280` | 12928 | 13 | 27 / 78 |
| Default Clang | `0x401ab0` | 6832 | 9 | 26 / 54 |

The bodies are respectively `f30f1efa4889f0f0480fc107c3` and
`4889f0f0480fc107c3`. GCC's original ENDBR64 is retained. The complete-file
SHA-256 identities remain
`3accb2f86b13dfac93c717aa1ac825b6cdf106de09bb2efa7cc5519fcf4646b3` and
`d74c7b71cdcc3107c870b7765d589b28f51bd5d451ef1f4e5e07425f05f53b61`.
This adapter establishes data identity, without behavior or score credit.

## Evidence and limits

Meaningful Lean suites cover high-half carry, full64 wrap, current peer values,
extended/aliased registers, source RSP, flags and byte/resource frames. Negative
cases distinguish raw CPU permission from actor/epoch/owner/loan/reservation
authority, require upper operand bytes even for zero input and reject malformed
complete histories even when their arithmetic would be harmless. A fresh replay
aggregate importing `OS.AtomicFetchAddMachine64` and `Concurrency.ModuloCounter`
passed kernel replay and the allowed-axiom audit. It covers their declaration
closure, including LockedAdd64 Machine/Decode/Model; the declaration-free
LockedAdd64 umbrella and the later frozen-window adapter were compiled separately.
Test compilation remains distinct from that production replay.

The target remains abstract long mode with CET/IBT/shadow stacks disabled and
the restricted aligned/non-crossing `atomicAddressable64` profile. Coherent WB
RAM, stable translation and permissions, suitable physical backing and aliases,
and access discipline through managed resources remain environmental obligations.
No physical LOCK/published x86-TSO refinement, native Linux enforcement, GNU
source-order preservation, fairness, eventual completion or minimum hardware
operation count follows from these foundations.
