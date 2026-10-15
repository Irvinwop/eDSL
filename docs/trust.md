# Trust, assumptions, and evidence

Status: required reporting policy plus the current implementation's boundary.
The general end-to-end compiler/OS pipeline is not implemented.

## Current boundary

The Lean library includes a restricted x86-64 decoder/machine model, unbounded
execution proofs, all-input increment/load/store theorems for actual compiler-output
bytes, mapped-memory permissions and framing proofs, and a narrow certificate CLI.
It also retains generic refinement lemmas
and the original toy example. See [coverage](coverage.md) for assumptions and
supported encodings. These results do not prove the model's conformance to
physical hardware, source-language preservation or a complete OS implementation.

The counted assembly-loop profile additionally proves a loop invariant,
termination and exact `2*initial_RCX+3` instruction cost for every 64-bit count.
It preserves memory/flags and retains executable-code/return-stack hypotheses.
Its LOOP/JRCXZ semantics uses full RCX, signed relative offsets and taken-target
canonicality checks; prefixes and other loop forms reject. This remains a
sequential userspace result, without environmental scheduling or timing claims.
Native bounded-count observations supplement the all-count theorem. The owned
assembly artifact is not evidence of C/C++ loop-lowering preservation. See
[control-flow scope](control-flow.md).

The abstract sequential address-space contract is projected into machine memory,
with checked protection/binary-load composition. It does not verify Linux syscall
bytes, page-table updates, resource exhaustion or concurrent permission changes.
Native VM probes are independent conformance observations for selected successful
operations and denied accesses. Their exact boundary is in the
[address-space report](address-space.md).

The sequential ownership layer adds a live allocation registry with natural
IDs/epochs, well-formedness preservation and permanent ticket revocation through
managed histories. Owned stores project to the existing machine bytes and OS
cell update under explicit authority, range, permission and code/stack premises;
all old/source values have admitted symbolic witnesses. No extra axioms or
hardware checks establish these contracts.

The registry is a logical resource discipline. Its principal/ticket fields do
not authenticate callers or prevent unchecked machine accesses. The histories
exclude unmanaged changes and arbitrary interference. The finite adoption scan
is complete under `WellFormed`; manually constructed malformed worlds are not
globally validated. Linear permissions, language provenance, concurrent
adequacy and real allocation/kernel refinement remain unproved. The certificate
generator retains its existing machine contracts and does not automatically
infer resource ownership. See [ownership boundary](ownership.md).

The shared-read borrowing wrapper checks stored lender/borrower authority and
readable contained subregions, freezing the entire allocation while any loan
remains. Its managed-history proofs preserve every surviving loan's record,
bytes and permissions, and permanently revoke finished IDs. Authorized reads
compose with actual load/RET bytes; independent initial buffers can be carried
through the same histories. Every 32-bit read value has an admitted binary
witness. These proofs require initial well-formedness and the guarded history;
arbitrary raw writes, aliases and outside interference are excluded. Copyable
IDs do not authenticate callers. No runtime enforcement or concurrent adequacy
is inferred. See [borrowing contracts](borrowing.md).

The managed read-worker layer adds actual per-instruction load/RET scheduling
against current shared memory, with spawn and join resource contracts. Internal
data/code/stack loans survive until successful join. Arbitrary finite managed
histories preserve each completed result against an independent initial word
specification and permanently revoke joined thread/loan IDs. Positive paths
cover every 32-bit word; two selections suffice in successful instruction
schedules, while an admitted infinite idle trace excludes unconditional progress.

The scheduler is an abstract OS contract. Native creation/publication/join,
context switching, hardware atomicity, weak memory and authenticated thread
identity remain unproved. Its root/worker Nat labels do not establish freshness
relative to external principal registries. Raw accesses and unmanaged internal
loan release bypass the protocol. This read-only profile does not complete the
roadmap's mutable shared-counter/atomic workload. See [thread scope](threads.md).

The atomic-exchange foundation adds exact `MOV EAX,ESI; XCHG [RDI],EAX; RET`
bytes, an indivisible abstract RMW event, three-instruction execution and an
exact singleton event trace. Every labeled machine atomic step projects to
`ExchangeTransition`. The guarded OS-cell exchange checks current exclusive
owner/ticket authority and rejects live read-loan conflicts. Same-cell exchange
histories prove actual old/new chaining and surviving loan stability.

`OS.Atomics` adds stored actor handles and whole-allocation reservations over
that primitive. Its guarded histories preserve current authority, supported
operands, read-loan exclusion and exact surviving handle records; closed IDs
stay revoked permanently. Other allocations and ordinary loans retain their
existing contracts. Checked exchanges admit every replacement, project to the
actual XCHG step and compose with the three-instruction compiler routine.
Exchange-only schedules prove value chaining and multiset conservation;
symbolic witnesses cover every old/new 32-bit pair.

These are logical authority labels and guarded histories, without runtime
authentication/enforcement or native handle management. Raw updates bypass the
wrapper; finite scans assume `WellFormed`. A mixed history may contain an
ordinary store after all handles close, so its value-flow theorem needs a continuously surviving
reservation or explicit framing. No unconditional progress or reclamation
follows from operation enabledness. See [shared-handle scope](atomic-handles.md).

`OS.AtomicThreads` adds private mutable-worker contexts, checked root spawn and
join, and actual MOV/XCHG/RET instruction scheduling against current shared
cells. Each worker holds an atomic handle plus code/stack read loans until
join. The old word is captured by its actual XCHG instruction, with no cached
spawn-time value. Every successful later join returns that event's old word
despite arbitrary admitted mixed histories. Those histories preserve the
invariant and permanently revoke joined thread, handle and loan IDs.

Arbitrary successful dispatch-only schedules at one shared address prove
actual event chaining and multiset conservation from an independently observed
initial cell. This final-memory result does not cover mixed histories with
zero-handle gaps and permitted intervening stores. Three own selections of a
preparing worker suffice in a successful supplied instruction schedule;
unfinished dispatch and completed join are enabled under the invariant.
Every well-formed preparing worker also has a successful three-dispatch
schedule and checked join. Symbolic witnesses establish admitted owned worlds,
spawn and that finite path for every initial/replacement 32-bit pair. Infinite
idling still excludes unconditional progress.

These are abstract lifecycle and scheduling contracts. Nat actor labels do not
authenticate native threads; unmanaged raw accesses/exchanges and raw resource
operations remain excluded. The admitted steps are spawn, dispatch, join,
guarded mutation and idle. Creation failure is an explicit pure-operation result,
not a proved native cleanup routine. Native pthread/clone/publication/join,
context switching and general memory ordering remain unproved. The separate
mutex protocol below adds protected invariants; the CLI does not infer worker registries. See
[mutable-worker scope](atomic-workers.md).

The `fetch-add32` profile adds exact MOV/LOCK-XADD/RET certificates with one
modular-add event and correct addition status flags. Kernel-checked flag proofs
state arithmetic carry/overflow and preserved nonstatus bits. The OS checked
handle operation preserves existing resource contracts, has actual-instruction
and complete-routine bridges, and proves finite same-cell counter traces equal
the observed initial value plus all deltas modulo 2^32. Symbolic witnesses cover
every initial word/delta. Native flag observations and unique-old counter stress
checks supplement these proofs. No unrestricted interference, natural-number
no-overflow, general memory-ordering or physical
conformance claim follows. See [the fetch-add boundary](fetch-add.md).

`OS.CounterThreads` separately schedules the exact nineteen-byte locked-add
loop against current shared cells. Every dispatch refines one actual decoded
machine step, including flags and projected memory. Its managed mixed histories
preserve worker/resource invariants and permanent joined-ID revocation.
For dispatch-only schedules from a prepared finite entry-phase registry, every
completed worker emits its independently published full-RCX increment count;
all completed workers establish the initial-plus-requested modular counter sum.
Checked full collection returns zeros, removes all worker records and preserves
the counter cells. A constructive finite completion/collection exists for every
admitted registry, but infinite idling remains possible.

`CounterCertificate.sound` binds those independent workload contracts to exact
raw bytes or a complete checked ELF. Prepared resources, initial observation,
one shared address and entry-phase workers remain explicit premises. Raw mode
also requires executable-code binding; ELF mode derives it from modeled loading
with shared-space/entry-address equalities. The CLI does not infer a registry
or establish native publication. The counter theorem excludes mixed-history
ordinary writes across zero-handle gaps and arbitrary unmanaged interference.
Its `3*count+3` per-worker instruction cost excludes lifecycle and kernel work.
Batch collection is a pure functional construction, without a native atomic
batch-cleanup claim. Native pthread/clone, context switching, runtime cleanup,
native locks and general weak-memory refinement remain external.
See [counter-worker scope](counter-workers.md).

`OS.Mutex` adds a distinct checked protocol over `Borrowing.State`: one lock
and one protected payload in separate owned allocations, reserved throughout
registration. Actual XCHG observations grant exclusive fresh guards or retain
busy events; guarded stores can open a local independent invariant, and
successful release closes it on the current payload and revokes the guard.
Managed mixed histories preserve well-formedness, permanent revocation across
re-registration and surviving unrelated read loans. Positive admission and
finite critical-section cycles have symbolic nonempty witnesses.

The acquire/release/load/store bridges use existing exact compiler bytes, with
full projected states and explicit code/return-stack contracts. Guards and
invariant checking are logical admission, not instructions implemented by those
routines or authenticated runtime identities. No arbitrary client compliance,
linear-token ownership or injective native worker/principal mapping is inferred.
The fixed complete-worker layer below adds dispatch enabledness, architectural
coverage and constructive completion. General weak-memory publication, native
C observer and pthread/kernel refinement, blocking/wakeup and universal
scheduler progress remain unproved. Atomic-handle and mutex histories are
separate wrappers, with no implicit cross-model composition. Native contended payload observations
and an independently failing no-store mutant supplement the proofs; they do
not discharge these contracts. See [mutex scope](mutex.md).

Physical interpretation requires the explicit aligned coherent-WB-RAM profile,
stable translation/permissions, excluded aliases/mixed-size overlaps and stable
code/stack. Locked-instruction ordering, general x86-TSO, C/C++ memory-model
preservation and concrete thread/runtime/kernel refinement remain unproved.
Native old/new/guard and eight-thread token-conservation observations supplement
the model proofs. See [the exact atomic-exchange boundary](atomic-exchange.md).

The restricted ELF path checks complete observed bytes, parser/validation results
and entry-code binding through a modeled loader. It removes the raw path's
unverified extraction dependency for those artifacts, while retaining explicit
caller mappings/stack/data conditions. This does not prove Linux page-padding,
relocation, startup, dynamic linking or loader implementation behavior; see the
[ELF boundary](elf.md).

The standalone process path checks the complete observed static ELF and derives
its entry code through the same modeled loader. It proves that every modeled
initial register/flags state reaches the raw exit60/status42 request in exactly
three user instructions, without a caller stack, startup data or runtime. The
request is a userspace ABI snapshot before privileged execution, not a model of
kernel entry, RCX/R11 clobbering or return to userspace.

Its explicit OS contract admits a single-thread, unintercepted raw exit request,
waiting and a status-completion transition. Every completed trace has
status42; eventual completion requires the separate `LinuxExit.Fair` assumption
of abstract completion progress. This is not a theorem that scheduler fairness
completes Linux cleanup. An admitted infinite wait demonstrates the need for
progress, and a terminating fair trace makes the conditional guarantee
nonvacuous. Linux loader behavior, privileged instruction execution, the kernel
implementation and resource cleanup remain unproved. Signals, interception,
multithreaded exit, libc wrappers and `exit_group` are outside this profile.
See the [process contract and reproduction commands](process-exit.md).

`scripts/verify-process.sh` checks owned Clang/GCC assembly ELFs through
`edsl-certify-process`, then observes native status42 and rejects wrong-status
and wrong-syscall mutations. This independently checks selected native behavior;
it does not establish universal conformance of Linux or hardware to the model.
The exact three-user-instruction count excludes loading and kernel work. Its
matching lower bound requires zero initial RAX/RDI and quantifies only over
supported first-syscall candidates, as stated in [the cost model](cost-model.md).

The write-exit42 path adds five user instructions before a bounded stream write
and the three-instruction exit suffix after any admitted return. The contract
allows partial counts, zero and raw errors; only full transfer establishes exact
`OK\n` output. Its explicit return boundary preserves userspace memory and
ordinary registers while leaving flags/RCX/R11 unconstrained. Kernel entry,
return and write implementation remain external. Buffer bytes are derived from
the loaded ELF rather than assumed from a source fixture.

The eight-user-instruction result requires write completion. Stable stream and
buffer identity, no concurrent writers or asynchronous interference, and the
restricted error-with-no-accepted-bytes behavior are assumptions. Regular files,
direct I/O, devices, durability and descriptor lifecycle are excluded. Native
fresh/full nonblocking-pipe observations supplement the proof; the three-byte
fixture does not demonstrate native partial success. See [write scope](process-write.md).

`lake build` checks the declarations with Lean 4.35.0. The audit traverses
transitive axiom dependencies of declarations under `EDSL` and permits only
Lean's standard `propext`, `Quot.sound`, and `Classical.choice`. It rejects
`sorryAx` and any additional axiom. No third-party Lean package is currently
required. Review of theorem statements and definitions is still essential.
Byte-reassembly proofs use ordinary bit extensionality and checked arithmetic;
solver/native-evaluation axioms are not whitelisted by the audit.
The audit's negative check requires rejection of an injected external axiom
used by a project theorem. The pinned toolchain's `leanchecker --fresh EDSL`
also replays stored declarations in a fresh kernel environment. This remains
the same kernel implementation, not an independent physical-world validation.

Standard foundational axioms are distinct from an unproved claim that a compiler
or operating system is correct. Environmental assumptions should be visible
parameters in theorem statements and reports, never hidden global axioms.

## Planned trust ledger

The complete [mutex worker execution](mutex-workers.md) adds actual CMP/JNE and
RSI-addressed MOV semantics. Every admitted dispatch is proved equal to a full
machine instruction over current shared cells. Generic control/guard/payload
preservation now proves the independent modular total and zero returns for every
completed admitted architectural schedule from an entry cohort, without its
endpoint checker. The initial invariant includes tracked guard ownership and phase-specific saved EAX
relations; `ClosedUnderTwo` is an explicit local predicate-preservation contract.
The first store may open that predicate, and the second restores it before
`release_admitted`. A separate potential proves actual instruction costs.
`ExecutionReady` comes from checked spawn and records actual code/return-stack
facts and current loans. Preserved borrowing histories retain bytes and
permissions. Every existing unfinished selection is enabled from the current
invariant and readiness, without an assumed future replay result.

`OS.MachineThreads` executes only `X86.step` against full current memory and
private contexts after checking that the selected call exists and has not
returned. It contains no mutex admission checks. Erasure and lifting cover
every finite architectural prefix from the admitted fixed profile and retain
`Invariant` and `ExecutionReady`. Completed executions admit checked collection,
which revokes exactly their original loan IDs and retains unrelated records.
Generated `MachineSpecification` certificates include these prefix,
enabledness, direct result/resource and constructive entry-completion contracts.
The older checked-replay route remains available.

A completing schedule exists from any admitted intermediate state with no new
busy exchanges and at most `15*n` future instructions. Entry completion takes
`13*n`, attaining the fixed routine's instruction-count lower bound across
schedules. Neither existence proof establishes completion for all schedulers,
latency or optimality among alternative implementations. Public constructors
alone supply neither program validity nor execution readiness. Initial resource
well-formedness and payload closure remain explicit contracts. Native pthread
observations remain separate evidence; runtime identity/authentication,
physical memory-order adequacy and kernel behavior remain environmental
obligations.

Every artifact report must distinguish:

| Item | Planned treatment |
| --- | --- |
| Specification and admitted-input definition | Human-reviewed; needs examples, counterexamples and nonvacuity checks |
| Formal source/ISA/OS definitions | Reviewed models; adequacy to language specifications and real platforms is a separate obligation |
| Lean kernel and logical foundations | Proof-checking trust base; pin toolchain and report accepted axioms |
| Lean elaborator, tactics and proof search | Produce terms checked by the kernel; reject holes and unsupported axioms |
| Native evaluation, FFI, external solvers | Untrusted unless reconstructed/checked through a proved route; any deliberate additional trust must be separately labeled |
| Compiler, optimizer, assembler, linker | Untrusted producers in translation validation; certify their particular final output |
| Parsers, decoders, printers and importers | Proved correspondence or explicit trusted boundary; test success alone is insufficient |
| Libraries and runtime shims | Validate concrete reachable implementations or show their contracts as assumptions |
| Loader and OS implementation | Contract assumptions until a concrete conformance/refinement proof exists |
| CPU, devices, hypervisor, firmware and deployment | Physical/environmental conformance and integrity assumptions; outside a pure Lean theorem unless modeled and justified separately |
| Build, storage and certificate cache | Pin dependencies and check artifact equality; names and hashes alone do not prove semantic correspondence |

Lean's [proof-validation documentation](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)
explains the distinction between checking proofs and trusting additional
execution mechanisms. Pin the reference to the selected toolchain when adopting
new proof-generation routes.

## Avoid vacuous or overstated claims

- Prove or exhibit admitted initial states; an impossible precondition makes
  many theorems trivially true.
- Separate source definedness, target behavior inclusion, target behavior
  existence, and total correctness. Nonempty behavior does not establish
  termination if divergence is an allowed observation.
- Cover all relevant target behaviors and coupled environments. One successful
  run or one favorable schedule is not the desired theorem.
- Record the treatment of source UB, machine faults, deadlock, divergence,
  resource exhaustion, interruption and partial I/O.
- Never describe a finite unrolling bound as a proof about arbitrary loops or
  arbitrary thread counts. Report exact bounds and coverage.
- Keep conformance evidence, testing, model checking, solver search, and
  kernel-checked proofs as distinct evidence categories.
- Review dependencies and hypotheses after every abstraction/lowering change.
  An axiom-free proof can still prove the wrong proposition about the wrong model.

## Release evidence required later

A certified artifact needs exact final bytes, available build provenance,
supported-feature/profile checks and named machine-property proofs. Add source
identity, frontend evidence and refinement proofs for source-preservation claims.
Every route also needs link/load and runtime obligations, the specification,
explicit environmental assumptions, tool/library/model revisions, proof audit
results, and reproduction commands. Cost/security/termination claims each need
their own named theorem and scope. Changed dependencies invalidate cached
certificates until checked again.

The first releases should say **proved under a stated Linux/ISA contract**.
Reducing that boundary means proving more of the concrete runtime, loader,
OS, or hardware relationship; renaming an assumption does not reduce trust.

Direct [binary-first proofs](binary-first.md) can avoid a trusted frontend by
stating the desired behavior directly over final machine-code execution. They
do not thereby prove source equivalence. [OS implementation proofs](os-implementation.md)
can discharge particular kernel/runtime contracts, including the required
caller/interference and hardware assumptions. A failed proof is not evidence
of unsafe code: use the [findings workflow](findings.md) to distinguish missing
analysis support from a checked violation of a justified property.
