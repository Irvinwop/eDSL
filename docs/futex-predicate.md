# Predicate-rechecking private WAIT loop

The predicate client repeatedly reads a private signal word W and returns the
loaded value only after testing it nonzero. Under the declared 0/1 signal
protocol, its independent result is return1 with current W=1. A successful or
spurious WAIT return of zero does not satisfy the program's predicate.

The new `EDSL.OS.Futex.Predicate` layer is additive. The existing 13-byte WAIT
client, 32-byte publisher and their certificates retain their meanings. The
new heterogeneous cohort contains one designated loop and supported legacy
publishers or payload peers; it never admits these new bytes as the old WAIT.

## Exact code and current resources

The exact 30-byte loop uses instructions already supported by the decoder and
TSO/suspension model:

```asm
retry: mov eax,[rdi]       # 0
       cmp eax,0          # 2
       jne done           # 5, displacement +22
       mov eax,202        # 7, Linux x86-64 futex number
       mov esi,128        # 12, FUTEX_WAIT_PRIVATE
       syscall            # 17, expected value RDX=0
       mov eax,1          # 19
       cmp eax,0          # 24, overwrites resume ZF
       jne retry          # 27, displacement -29
done:  ret                # 29
```

Entry RDI names W; RDX/R10/R8/R9 are zero. Current admission retains exact
code loans, every byte of the original eight-byte return slot, actual worker
control, current authority and physical/resource RAM agreement. The keeper
pins mutable W's lifetime without freezing it through an ordinary read loan.
Each actual capture obtains a fresh invocation identity and individual pin;
resume consumes that invocation and revokes its pin. Fixed handles and the
original pin floor remain unchanged across iterations.

Canonical entry and entry+29 are explicit static guards. Current readiness
derives instruction reads, aligned W access, branch targets and the protected
RET from present resources. Admission contains no future execution, resource
replay or successful-return promise.

Snapshot knowledge explicitly permits LOAD0 before publication followed by
current W1. A loaded/tested one implies current W1 through monotone supported
effects. Outside the 0/1 protocol, these bytes can return another nonzero word;
the exact byte check alone does not establish return1.

## Safety and constructive completion

`Predicate.admitted_step`, `Admitted.trace` and `Admitted.infinite` preserve
current admission through accepted mixed issue, drain and typed service
execution. `issue_lift`, `drain_lift` and `MachineTrace.lift` construct managed
execution from actual raw physical behavior, with identical suspended outputs
and observations. Typed current service guards positively enable service steps.
An issue that parks a pending worker is enabled but need not make progress.

`Predicate.Notification.exchange_wake_trace` binds an actual publisher XCHG to
that same publisher's saved WAKE1 request. An arbitrary mixed prefix may occur
between them, including a previously queued WAIT. The wake clears the sole
waiter, and every later accepted mixed suffix preserves no-queue safety,
current W1, the publisher's payload and admission. Retries, spurious readiness,
full resume clobbers and returned peers' FIFO drains are included. Separate
infinite safety makes no fairness claim.

`Predicate.Returns` independently observes a selected returned worker, RAX1,
current W1, original return target and RSP+8, cleared pending record, empty own
FIFO, ZF=false and stable general registers. RSI is its entry value or 128;
RCX/R11 and other flags follow actual private resume history.

`constructive_completion_with` constructs a suffix of at most 14 runtime
actions from every currently admitted cut after notification. This includes
stale LOAD0/CMP0/body, entered and ready calls, already resumed code and RET.
An already returned worker admits an empty suffix. Future resumes may choose
arbitrary full flags/RCX/R11; historical resumed contexts are retained. The
completion relation includes final admission, identical whole RAM and every
peer's full worker record, FIFO and pending invocation.

`constructive_completion_selected_with` additionally exposes a checked trace
whose actions issue only this loop or compare/resume its own current WAIT0
call. It selects no peer issue or drain.

These bounds count modeled instruction/service actions. They are upper bounds
for an enabled finite suffix, not minimum operation counts, hardware cycles or
a guarantee that an arbitrary scheduler selects that suffix. Blocking-mutex
acquisition, multiple waiters and whole-kernel refinement need separate proofs.

`Predicate.Accounting.load_to_returns_lower_bound` proves a separate lower
bound for the actual LOAD cut with current W1: every accepted returning mixed
trace retires at least four of this worker's user instructions.
`load_fastpath_attains` constructs LOAD/CMP/JNZ/RET with exactly four retirements,
the independent return, current admission and whole RAM/peer frames. Thus four
is the minimum for this program and starting state. It is not an optimum among
other programs or algorithms. The metric includes an entered SYSCALL as one
user instruction and excludes service, waiting, propagation and peer work.
`Specification.fastpath_lower_bound` and `fastpath_attains` retain the literal
artifact binding for both directions. See [cost definitions](cost-model.md).

## Validation and target boundaries

Build and use the exact-profile certifier with:

```sh
lake build edsl-certify-futex-predicate
lake exe edsl-certify-futex-predicate wait-recheck function.bin certificate.lean
lake exe edsl-certify-futex-predicate --elf wait-recheck function.elf certificate-elf.lean
```

Generated certificates retain the literal input, exact 30-byte acceptance and
conditional model contract. Full ELF input uses the existing restricted loader
and checks its selected file-backed executable entry window, without searching
for matching bytes elsewhere. Loading and current memory/entry agreement remain
explicit. Loading supplies no runtime resources or process-startup proof.
Unsupported input exits with `UNVERIFIED` and makes no defect conclusion.

`EDSL.Examples.FutexPredicate` constructs genuine resource admission for the
new loop, a publisher and a buffered peer. `tests/FutexPredicate.lean` executes
the actual decoder, FIFO, suspension and service paths through repeated calls,
spurious zero, full-width EAGAIN, stale snapshots, high private clobbers and
returned-peer drain. Universal theorems are instantiated from initial admission;
later admission is a conclusion.

`scripts/verify-futex-predicate-native.sh` checks exact assembled and final
linked windows, SysV register/return frames and project-owned Linux observations.
It observes repeated wake/re-entry, publication races and real traced EAGAIN.
An owned missing-backedge mutant must fail the independent predicate contract.
The traced stopped-child reset is an observer intervention, not an admitted
signal-protocol transition. Multiple native contenders exercise the observer
outside the formal sole-waiter policy and establish no multi-waiter theorem.

`scripts/verify-futex-predicate.sh` runs both compiler observers and checks eight
raw/full-ELF certificates for their identical object and final windows, plus
four owned mutant rejections. The Linux CI job caches the pinned toolchain and
Lake outputs; it still executes tests and certificate checks. The main proof
workflow separately runs the full transitive audit and fresh kernel replay.

Native execution requires Linux x86-64, available futex/pthread/ptrace and
stable aligned storage. A watchdog, timeout or unsupported target is inconclusive.
ARM Mac checks establish portable Lean proofs and cross-assembly only. Model
proofs do not establish installed Linux, hardware memory-order correspondence,
fairness or safety of an entire distribution. Dependency audits allow only
`propext`, `Classical.choice` and `Quot.sound`; Lean remains pinned to 4.35.0 with
warnings as errors.
