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

The ordinary [sum32 milestone](sum32.md) uses one independent natural list-sum
modulo 2^32 contract for compiler-produced pointer/count and indexed loops.
`EDSL.Sum32.sound` constructs actual terminating execution for every undefined-AF
stream from current code, full-width count, nonwrapping current array and actual
eight-byte return-stack premises. It proves full RAX zero extension, full Memory
equality, the register/return frame, nonarithmetic-flag preservation and exact
operand reads and instruction cost. `safe` and `no_divergence` cover reachable
prefixes and all streams. Empty input needs no input loan/readability/canonical
pointer; its only operand read is the real stack8 slot, with fetches outside
that observation.

The separate `X86.Sequential` ISA supplies bit-precise arithmetic helpers and
independent AF choices for XOR/TEST. Both AF outcomes exhaust the logical-flags
contract; universal choice coverage is a conservative model, without asserting
that every stream occurs on hardware. Its generic ordinary MOV forms preserve
all flags and evaluate addresses/source operands before updating the destination.
Register copies distinguish zero-extended MOV32 from full-width MOV64. MOV64
supports all 16 GPRs; its memory forms use separately checked eight-byte access
and ownership contracts. LEA64 computes addresses without a data access or a
canonicality check on the result, preserving all flags. Register ADD64 uses
the full64 six-flag arithmetic contract. Their
[conformance evidence](sequential-arithmetic64.md) remains finite; it does not
establish the physical adequacy of the ISA model.
Register-only CMOV64 preserves full destination words on false, uses incoming
flags and pre-source values, and preserves every flag and RAM field. Its
sixteen conditions include proved signed/unsigned CMP order adequacy;
[native CMOV checks](sequential-cmov64.md) remain finite conformance evidence.
Memory-source CMOV stays unsupported because even a false condition performs
the architectural source read. Pure-call resource contracts couple the same
world and original caller slot; changed RSP does not grant a new binding.
The [current-resource bridge](sequential-moves.md) derives actual stores and loads
from present authority, retaining complete RAM coupling and original code/stack
loans through the actual instruction length. The full-pointer-copy/store/RET integration uses
the actual preserved RSP binding; a copy into RSP retains the original stack
authority and requires a separate binding before RET. The deterministic/TSO decoders
retain their original subset and their exact-flags and restricted
minimality theorems. Physical exception, control-state, translation and ordinary
RAM assumptions remain those of the [machine profile](coverage.md#supported-machine-profile).

The [pointer-returning store certificates](store-return32.md) strengthen the
independent store post with full64 RAX equality to the target. Actual raw and
current-resource executions cover both compiler orderings. Typed literal raw
and ELF certificates recompute acceptance and compose the existing loader with
explicit current caller premises; native observations remain separate. They
add no source-preservation or concurrent-backend claim, and do not alter the
existing registered void-store grading contract. A separate `storeReturn32`
registration requires that stronger post with the same present domains, current
policies and actual returned resource history. Its fresh RCX implementation
is a client-only proof packet; the trusted snapshot excludes its module and
checks the packet against independently selected task/artifact literals.

Sum32 acceptance checks actual decoding, contiguous CFG layout, branch links
and supported operations within 64 bytes/32 static instructions. Zeroing
prologue variants and commuted pointer/count updates use the same structural
checker. `Valid.decoded` derives real instruction selection through `CodeAt`;
an expected-code table or a successful future run is no semantic premise.
Other correct shapes may reject. This does not implement general C or source/IR
ingestion, arbitrary-program grading, full x86 or a new concurrent backend.

`OS.ArrayResources.Admission` couples full current machine RAM to the OS
projection and binds current code, complete stack8 and nonempty-input loans.
Current observations and retained-loan history frames supply the resource
bridge; no snapshot or future-execution callback is assumed. The checked
`Artifact.resource_sound` concludes the shared semantic contract, retained
admission and current permission for every actual operand read. Native loan
enforcement and unguarded interference remain outside the contract.

The sum32 CLI emits literal semantic certificates with conditional typed
resource binders. Full-ELF certificates check parsing/loading and prove the same
execution at the installed function entry, with current caller input/stack/RAM
and page freshness still explicit. Neither file bytes nor the CLI manufacture
native OS admission, process startup or whole-ELF safety. Exact instruction
costs come from execution proofs; 19/18-byte size comparisons and bounded native
ABI/guard-page observations establish no timing, optimality, source-preservation
or kernel-conformance theorem. See [artifact details and commands](sum32.md#artifact-and-native-boundary).

The [reusable CFG layer](cfg.md) checks complete finite instruction partitions,
actual decoder agreement, successor closure and static depths. Local Lean VCs
separately prove current code/PC binding, current operand-read permission,
independent postconditions and decreasing dynamic ranks. Their composition
constructs actual all-AF execution; successful future evaluation is no premise.
Read-origin theorems retain a real prefix and its current RAM, including the
complete RET operand. Optional accounting derives exact instruction/read totals
from local equations after totality is proved.
The stride-two instance discharges those equations for `6*count+4`
instructions and even-index reads followed by stack8. Its OS bridge retains
full current RAM coupling and loan authority at actual read origins; physical
kernel enforcement remains outside the model.
The [two-array instance](pair32.md) composes both loop phases through the same
interface and proves `6*(lengthA+lengthB)+6` instructions, ordered A/B/stack
reads, and an independent concatenated-list sum. Its OS bridge keeps both
current admissions and uses each input's own loan authority. Inputs may alias
when their current contracts agree. Resource tests exhibit separate and
overlapping admissions, empty exceptions and current-B/authority failures;
none of these results verifies native kernel enforcement or interference.

`edsl-cfg-import` checks static literals and exposes conditional functional
obligations. Its explicit ELF span includes code after an early RET and is bound
to the full modeled container, but file acceptance does not create caller or OS
admission. The separate [proof grader](grading.md) now fixes those specifications
and theorem types for registered pair/stride sums and an owned-word store. It checks fresh safe
proof helpers as data, the exact artifact and current reachable OS/effect
obligations; candidate source/modules/options are excluded. Its runtime
controller and trusted build provisioning remain explicit trust boundaries.
Version 2 shares expression syntax within each field with backward references,
scope/depth checks and packet-wide work accounting. It caches no inferred
typing judgment; the kernel checks complete terms in their actual contexts.
The separate client MOV-stride proof supplies fresh declarations through this
boundary, and the trusted registry does not import the candidate module.
The separate two-store client proof follows that same boundary: fresh helpers
certify eleven assembled bytes and two checked owned-resource mutations, while
the grading service retains its fixed imports and independent task contract.
The seven-byte MOV client also proves that unchanged claim: its target read
uses current owner/ticket authorization after the actual checked store in the
same evolved OS world. An explicit preserved-RSP binding supplies the actual
RET step. No target loan, snapshot substitution or future-step premise is added.
Neither user-supplied `Post := True` nor successful static import establishes
an intended task result. The grading profiles remain sequential callable RAM.
Pair/stride exclude stores; write32 permits ordinary fixed-target stores through
current ownership, with OS states chained to actual machine steps and retained
loans, allocation records, permissions and outside-target cells. Registration
owns these policy hooks and the returned-history requirement. No future
execution or favorable policy is an admission premise. Native pointers do not
enforce the logical tickets. Atomics and syscalls remain excluded; bounded model
instruction counts establish no timing or global minimality theorem.
The separate owned-word cost proof compares arbitrary actual candidates in the
current sequential ISA: useful inputs require at least two modeled instructions,
and the checked store/RET attains two with its current resource-return history.
It assumes the independent task Pre/Post, and the useful old/new inequality is
essential. It does not constrain grader acceptance to an optimal implementation
or establish a complete-x86, micro-op or CPU-time bound.

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

The separate `OS.TSO` scheduler models delayed aligned ordinary stores, FIFO
drains, local forwarding and locked operations after an empty local buffer.
It decodes shared code and uses the same decoded execution definition as
`X86.step`; non-writing memory effects and complete atomic/store outcomes are
proved explicitly. `OS.MutexTSO` proves the separate fixed-worker simulation:
the logical memory equals physical RAM overlaid by actual pending payload
writes, with exclusive guards deriving queue authority. Every physical prefix
lifts to canonical checked replay; drains and stalls retain the whole logical
state, while busy exchanges remain real retired events. Admission additionally
requires aligned payload and non-executable lock/payload destinations.

Actual returns imply publication for this routine and establish total, full
return-register, lock and retired-cost contracts. Positive collection retains
the entire physical memory and revokes exactly the original cohort's loans.
Publication and completion suffixes are constructed from current invariants,
without assuming future replay or collection success. A paused prefix has a
continuation with no new busy exchanges or stalls; this asserts an available
path, not inevitable completion or fairness. Generated `TSOSpecification` is
distinct from the immediate-visibility specification. The physical interpretation excludes aliases,
mixed-size overlapping accesses, mutable code, devices and translation changes;
it is not a hardware refinement theorem. See [the buffered profile](store-buffers.md).

`OS.Suspend` additionally admits an actual syscall request to remain pending
while peers run. Its additive `ReturnsAt` contract uses current shared memory,
so returning does not restore an old snapshot. Full pending-context, fresh-ID,
memory-frame and peer-FIFO properties survive actual traces. A consumed ID
cannot resume again, even after later invocations. The old synchronous return
contract is unchanged. A caller's nonempty FIFO is explicitly unsupported at
entry; no syscall flush effect is assumed, and peer FIFOs may remain nonempty.

Completion choices supply a raw result and private clobbers only; they cannot
replace shared memory. The mechanism proves no Linux service outcome, kernel
transition or scheduling progress. It has no automatic ownership authorization
for peer stores; service/resource composition requires a further relation.
Infinite parked/idle traces remain possible. See
[concurrent syscall boundaries](concurrent-syscalls.md).

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

The [private futex adapter](futex.md) adds actual-call pins and an explicit
abstract compare/enqueue/wake/retry/spurious service over current RAM. Accepted
adapter traces retain full managed/physical memory equality and initial loans;
these are Lean model safety proofs, not native enforcement of allocation lifetime.
Capture checks the configured complete lower-userspace interval and excludes
executable W. The interval's correspondence to deployed Linux access checks,
private-key resolution and kernel linearization remain target obligations.

The original standalone exact-byte certificate proves request invocation and
conditional current-RAM RET. The separate publishing-client certificate binds
an exact 32-byte routine to a selected current admitted member. Admission is a
present-state contract: exact code/control, current ordinary-write grants and
all actual FIFO entries, complete eight-byte return-stack loans, live fixed
handles, and service/resource consistency. It assumes no future replay or
return success. Actual issue/drain steps positively lift to managed execution,
preserve admission and extend to every finite physical issue/drain prefix.
Typed current service guards and ready calls enable actual service and protected
RET; they do not establish eventual readiness or progress.

The current publisher's actual XCHG establishes prior payload publication and
W=1. Supported later instructions and authority for all buffered stores exclude
resets, including stores owned by returned peers; service bookkeeping stutters
RAM. These proofs concern the declared fixed client profiles and abstract
service. Their artifact theorem still requires current admission, membership
and code binding; its specification exposes same-member publication, actual
physical prefix lifting and W=1 persistence as conditional model guarantees.
Full-ELF loading additionally requires agreement with the current loaded memory
and entry. A CLI byte match does not construct that
runtime admission or verify native mapping/resource enforcement.

A broad no-lost-wake or blocking-acquisition theorem, installed-kernel/runtime
correspondence and safety of a whole Linux kernel or distribution remain outside
the claim. Native fault cases and positive/inconclusive wake or publication
observations remain empirical evidence, not kernel proofs or progress claims.
