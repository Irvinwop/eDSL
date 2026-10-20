# Trust, assumptions, and evidence

eDieSeL proves properties of modeled executions under explicit contracts.
Exact-byte certificates connect those executions to particular artifacts.
Interpreting a result on a deployed system additionally requires the stated
ISA, ABI, memory, loader, runtime and environment assumptions. No physical CPU,
Linux implementation or general source-preservation theorem is implemented.

## Current boundary

The [coverage index](coverage.md) identifies each execution profile and its
contracts. The common proof chain is: independent specification and admitted
inputs → exact code binding → actual modeled execution → result, safety and
resource conclusions. Parsing, decoding, functional proof and current-resource
admission are distinct obligations. A static import or byte match supplies
only the obligations its theorem states.

### Proof checking

[`lean-toolchain`](../lean-toolchain) pins Lean 4.35.0;
[`lakefile.lean`](../lakefile.lean) enables warnings as errors. The
[axiom audit](../EDSL/Audit.lean) traverses transitive dependencies of declarations
under `EDSL` and permits only `propext`, `Quot.sound` and `Classical.choice`.
It rejects `sorryAx` and additional axioms. No third-party Lean package is
currently required, and unchecked solver/native-evaluation axioms are not
whitelisted. Environmental contracts belong in theorem hypotheses rather than
project axioms.

Elaboration, tactics and external search must produce kernel-checked terms.
Fresh replay through `leanchecker --fresh EDSL.All` uses a fresh environment
with the same kernel implementation. It checks stored declarations again;
it does not independently validate the kernel or physical model. Human review
of specifications, definitions and hypotheses remains essential.

Fixed-task [proof-packet checking](grading.md) checks data-only terms and fresh
safe helpers against the selected task and exact artifact. Candidate modules,
options and a candidate-chosen postcondition do not define the task. Its
controller, trusted imports and build provisioning remain a separate boundary;
client proofs do not become trusted merely by being examples.

### Machine and artifact assumptions

The common [userspace profile](coverage.md#supported-machine-profile) assumes
x86-64 long mode, flat addressing, 48-bit canonical addresses, valid control
state, disabled alignment checking and CET, no debug interference, stable code
and translation/permissions, and no asynchronous changes outside the admitted
model. Ordinary memory is RAM, excluding MMIO and device/DMA effects. The model's
errors are not a classification of native exceptions or security defects.

Callable contracts bind current executable bytes, the original readable
stack8 return slot and canonical return continuation. Data ranges and
permissions must satisfy the selected contract, including nonwrapping spans
and separation from mutable destinations. Changing RSP does not grant a new
caller-slot binding. Input-resource exceptions for empty arrays/buffers apply
only where the theorem explicitly permits them.

Sequential undefined-AF choices are universally quantified where supported.
This conservatively covers both values without asserting that every stream
occurs on hardware. Instruction coverage differs between the legacy,
`X86.Sequential`, call/return and concurrent engines; support does not transfer
implicitly. Memory CMOV remains unsupported: a false condition still requires
its architectural source read.

Raw certificates retain `CodeAt` as the connection to executed memory.
[Restricted ELF](elf.md) certificates derive code from exact complete file
bytes and checked modeled loading, retaining page freshness and caller facts.
[Named-window certificates](elf-function-symbol.md) additionally check symbol
identity and extents. These routes have different supported container profiles.
The corpus extractor is executable tooling, not a proved extraction theorem;
final certificates must recheck the literal file/code correspondence.

Modeled loading does not establish Linux page-padding behavior, relocation,
dynamic linking, startup stack/auxv/TLS, runtime dependency closure or deployed
image integrity. A callable ELF entry does not establish process startup or
safety of other image segments. Hashes and build provenance identify artifacts;
the checked theorem must still bind the actual bytes.

### Resources and concurrency

[Address spaces](address-space.md), [ownership](ownership.md) and
[borrowing](borrowing.md) are logical contracts coupled to current machine RAM.
Initial `WellFormed` premises matter: finite scans do not validate every
manually constructed malformed world. Allocation IDs/epochs revoke stale
managed authority; loans freeze their whole allocation and retain records,
bytes and permissions through guarded histories. Copyable principals, tickets,
loans and handles do not authenticate actors, enforce raw accesses or establish
a linear-token/provenance discipline. Unmanaged writes, mapping changes and
aliases are outside those histories.

Atomic profiles assume aligned coherent write-back RAM, stable physical backing
and translation, compatible cache-line/page placement, stable code/stack, and
no unmanaged aliases, mixed-size overlaps or device interference. The
[exchange profile](atomic-exchange.md#supported-physical-profile-and-remaining-obligations)
further restricts operands to aligned canonical nonwrapping four-byte ranges
within a virtual 64-byte line and 4-KiB page. Other widths have their own
contracts. A functional ordinary write proves no concurrent atomicity.

Managed worker results concern their declared spawn/dispatch/join and guarded
resource operations. Native pthread/clone, argument publication, context
switching, failure cleanup, authentication and reclamation remain external.
Same-cell value chains need the specified dispatch-only history or continuous
reservation; mixed histories can permit ordinary stores across zero-handle gaps.
Separate atomic and mutex wrappers require explicit composition.

FIFO buffers model own-store forwarding, delayed publication, drains and
locked-operation stalls. They are not a proved refinement to published x86-TSO,
physical processors or GNU C/C++ atomic orders. The full64 corpus fetch-add
contract additionally uses a finite closed cohort, excludes foreign RMWs and
requires current managed resources. Pending calls, arbitrary peers and general
pending stores are outside that certificate profile.

Mutex results require the fixed worker's current `Invariant`/`ExecutionReady`,
separate lock/payload resources and the `ClosedUnderTwo` payload-closure contract.
The buffered profile additionally requires aligned payload and non-executable
lock/payload destinations. Protocol checks are logical admission conditions;
the lock bytes do not implement them. Architectural
and buffered prefix-lifting proofs establish compliance for their fixed routine;
they do not establish compliance of arbitrary clients or native locks.

### Syscalls, futexes and progress

A modeled SYSCALL captures a userspace ABI request before privileged entry.
Kernel entry/return and service implementation remain external.
[Concurrent suspension](concurrent-syscalls.md) resumes against current shared
RAM, with fresh one-use IDs and peer frames. Entry rejects a nonempty caller
FIFO and assumes no syscall flush; the wrapper alone grants no peer-store
ownership authority.

The [private futex model](futex.md) supports a pinned one-word
WAIT_PRIVATE/null-timeout and WAKE_PRIVATE/1 service with atomic compare/enqueue,
eligible wake choices, retry and spurious readiness. Its configured lower-userspace
interval, non-executable word and private-key/service correspondence are explicit
assumptions. Native bad-input observations have no matching general error-service
model. Fixed clients require current code/control, complete stack loans, keeper
handles and authority for every queued store, including returned peers' stores.
The artifact checker does not construct that runtime admission.

Publication and W=1 persistence concern the admitted client profiles.
[Notification](futex-notification.md) uses one designated WAIT client expecting
a value other than one. The [predicate loop](futex-predicate.md) needs a 0/1
signal protocol for return1/currentW1; its postnotification completion suffix
uses at most 14 modeled runtime actions. These are safety and available-path
results, without a general no-lost-wake, blocking-acquisition or fairness theorem.

The [exit contract](process-exit.md) assumes a single thread, an unintercepted
raw exit60 request and no asynchronous interference. Completed traces have the
proved status; eventual completion requires `LinuxExit.Fair`, an abstract
completion-progress assumption. Scheduler fairness alone does not prove native
cleanup. Signals, multithreaded exit and libc/`exit_group` remain outside it.
The [write contract](process-write.md) permits partial counts, zero, errors and
waiting. Full output requires full transfer; error outcomes assume no accepted
bytes. Stable stream/buffer identity and no concurrent writers are required;
regular files, devices, direct I/O, durability and descriptor lifecycle are
excluded. Return-register/memory frames are explicit external contracts.

Enabled next actions, bounded own selections and a constructed completing
schedule are different from inevitable completion. Infinite idle/parked traces
remain possible in the relevant models. Instruction/action counts exclude
unmodeled lifecycle/kernel work and establish no CPU timing or unrestricted
optimality result.

## Trust ledger

| Boundary | Required evidence or remaining trust |
| --- | --- |
| Specification and input domain | Independent review, feasible admitted states and a precise fault/divergence policy |
| ISA/resource/OS definitions | Reviewed semantics; adequacy to native specifications remains separate |
| Lean kernel and foundations | Pinned checker and the accepted standard axioms |
| Compiler, assembler and linker | Untrusted producers; prove the particular final output |
| Parser, decoder and importer | Checked correspondence for the selected route; extraction/test success alone is insufficient |
| Runtime, loader and kernel | Concrete proofs or visible implementation-contract assumptions |
| CPU, firmware, hypervisor and devices | Physical conformance and deployment assumptions |
| Build and certificate storage | Exact identities, artifact equality and successful current checking |

## Avoid vacuous or overstated claims

Admitted initial states need witnesses independent of future execution success.
Separate behavior inclusion, existence, termination, safety and progress. State
bounds, permitted interference, failure outcomes and every observation relevant
to the claimed property. Finite native tests and model checking supplement
universal proofs; they do not establish model adequacy. An audited theorem can
still state the wrong property.

Security claims additionally need an explicit attacker, feasible environment
and justified security property. Current resource/framing/protocol proofs do
not establish general noninterference, speculative/timing security, or
whole-kernel safety. A proof failure, timeout or
unsupported input is not a defect verdict. Keep real findings and evidence out
of the public repository and CI; see [findings](findings.md).

## Release evidence required later

Each certified artifact needs exact bytes, build/model/tool identities,
independent contracts, named proofs, admitted-state witnesses, environmental
hypotheses, dependency audits and reproduction commands. Source-preservation,
security, termination and cost claims each need their own theorem and scope.
Changed artifacts or dependencies require rechecking affected certificates.

Report results as **proved under the stated ISA/OS contracts**. Direct
[binary proofs](binary-first.md) remove a frontend dependency from that claim;
they do not prove source equivalence. [Concrete OS proofs](os-implementation.md)
can discharge specific runtime/kernel assumptions only by meeting the same
client contracts under a justified shared execution model.
