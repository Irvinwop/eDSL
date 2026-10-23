# Arithmetic RMW scheduling

The TSO64 scheduler models interleaved ordinary instructions, per-worker store
buffers and indivisible qword arithmetic operations under checked OS authority.
Select an instruction family separately from the ordinary-memory authority
profile:

| Selection | Locked instructions |
| --- | --- |
| `RMWFamily.xaddOnly` (default) | Existing XADD decoder and executor, including their fetch and error boundaries. |
| `RMWFamily.arithmetic` | XADD, sign-extended imm8 ADD, and INC through the qword arithmetic decoder and executor. |

Import `EDSL.OS.TSO64.Run` for execution and invariant preservation, or
`EDSL.OS.TSO64.WordProjection` for word-level reference paths. The final
argument selects the family:

```lean
-- For an already installed scheduler state and a chosen action list:
-- schedule initial actions .ownedOnly .arithmetic
-- schedule initial actions .sharedCell .arithmetic
```

Omitting that argument retains the existing XADD contract. The legacy
`locked` executor is an abbreviation for `lockedFor .xaddOnly`; both
families share one scheduling kernel. The family index is retained through
decoded instructions, step origins, schedules, trace labels and projection
proofs. Authority `Profile` continues to control ordinary accesses.

## Proof API compatibility

`LockedEffect` is the default-family type abbreviation. Qualified constructor
and eliminator applications use `LockedEffectFor` with `.xaddOnly`; the old
`LockedEffect.blocked`, `.rmw` and recursor declarations are not aliases. Case
patterns still use `blocked` and `rmw`. The generic `rmw_path_of_effect` helper
takes an arithmetic effect; legacy callers embed the instruction as `.xadd`
and use the existing effect conversion. The raw XADD call, ABI and batch
contracts keep their original conclusions.

## Current state and blocking

An issue rechecks the installed running worker, original code and caller
leases, guarded executable fetch and instruction bounds. After the own FIFO
is empty, the locked operation checks actual current decode and the current
atomic handle. Its arithmetic input comes from the prestate:
XADD's source register, ADD's sign-extended immediate, or one for INC. The
checked OS operation uses the current published word. ADD and INC preserve
all GPRs; INC preserves incoming CF, while ADD computes CF from the sum.

A nonempty issuing FIFO blocks the locked operation, including ordinary
stores omitted by the selected-cell projection. The result retains the whole
input state, retires no instruction and emits no RMW event or reference label.
Peer FIFOs do not gate the issuing worker. Blocking does not drain either FIFO.

For an actual successful RMW, the projection retains
`lock; read; write; tau; unlock` even when the delta is zero or the modular
word does not change. `schedule_labels_sound` connects the actual schedule
and extracted labels to the word-level path under their invariant premises.
The [origin interface](arithmetic-rmw-origin.md) exposes the captured delta,
current authority and installed context without assuming an old-value register.

## Validation and limits

`tests.ArithmeticRMWScheduler` checks real mixed ADD/INC interleavings, a
zero-delta occurrence, full-state own-FIFO blocking, a pending peer FIFO,
carry behavior and exact four/five-byte fetch boundaries. It also constructs
reference-path witnesses using production schedule and annotation theorems.
Existing raw XADD call, ABI and batch contracts remain independently covered.
Run `lake build ManagedFetchAdd64Tests AddRMW64Tests`; full catalogue and
fresh-kernel validation are described in [validation](validation.md).

This uses the abstract coherent-WB-RAM model with long-mode, CET-off,
stable translations and permissions, injective physical backing, no hidden
aliases and protected resources. It does not establish physical LOCK or Linux
refinement, compiler preservation, global fairness or termination. The
ordinary Resumable adapter still requires a separate atomic composition rule;
ADD/INC function ABI certificates and whole-loop counts remain future work.
