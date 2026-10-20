# Platform model and the boundary of the guarantee

eDieSeL's current platform models cover restricted x86-64 userspace execution,
ELF loading and selected OS resource and concurrency contracts. A theorem
establishes behavior in its named model. Applying it to native execution also
requires the loader, runtime, kernel and hardware assumptions recorded for that
profile. [Coverage](coverage.md) and [trust](trust.md) give the current boundary.

The [OS implementation track](os-implementation.md) aims to verify concrete
kernel, runtime and driver components. A privileged kernel target is future
work; the userspace model alone cannot execute or verify a complete kernel.

## The intended claim

The [binary-first route](binary-first.md) proves an independent property of
exact executable bytes under admitted inputs, current resources and a stated
environment. A function theorem may establish total return and a resource
frame; a process theorem may depend on a completed OS action; a concurrent
theorem specifies which schedules and progress conditions it covers.

Source-language preservation is an optional extra requiring source semantics
and a checked relation to those same bytes. The general machine/OS composition
is a design obligation, not an existing universal `MachineOS` API.

Observations must retain relevant results, faults, failures, resource effects
and termination behavior. If external termination is admitted, it is an abort
outcome with a stated prefix-safety property, not permission to return arbitrary
successful output. The [verification requirements](verification.md) make these
quantifiers explicit.

## Layers that must compose

| Layer | What it establishes |
| --- | --- |
| ISA | Meaning of supported decoded instructions and memory operations |
| ABI | Entry, return, register and stack obligations for a selected interface |
| Resources | Current mappings, ownership, lifetimes, loans and permitted effects |
| Concurrency and OS | Allowed interference, memory ordering, service outcomes and progress |
| Artifact and loading | Binding of file bytes, selected code, mappings and initial state |
| Native platform | External correspondence of physical execution to those formal models |

An instruction semantics does not establish a syscall's contract. A syscall
contract does not establish ordering between ordinary memory operations.
Separate models compose only when their state, resource and environment
assumptions agree. The [architecture diagram](architecture.md#the-proof-boundary)
shows the current proof path and optional future source layer.

## Initial target profile and reproducibility manifest

The sequential callable profile assumes:

- x86-64 long-mode userspace, little-endian flat addressing and four-level,
  48-bit canonical addresses, with valid architectural control state.
- Stable ordinary RAM and translation/permissions, disabled alignment checking,
  and no asynchronous state changes, signal handlers or debug/single-step
  interference during the modeled call.
- CET indirect-branch tracking and shadow stacks disabled. Admitting the exact
  ENDBR64 encoding does not prove CET behavior.
- Current executable bytes, the original readable eight-byte caller return
  slot, nonwrapping relevant ranges, and the required current ownership/loans.
  Modeled access checks and resource authority are separate obligations.

Some physical assumptions are limitations of the semantics, rather than fields
encoded in every Lean precondition. Arbitrary modeled flags do not justify
execution with incompatible hardware controls. The represented scalar System V
interface also does not cover the full native ABI, vector state or unwinding.

Concurrent atomic profiles additionally require suitable alignment and physical
backing/aliases, coherent write-back RAM, stable resources and the interference
restrictions of their particular managed model. For example, the
[full64 closed-batch certificates](concurrent-fetch-add-certificates.md) exclude
foreign RMW events and external peers. They supply no general native-thread,
scheduler-fairness or Linux-enforcement theorem.

The restricted loader accepts a bounded static ELF64 x86-64 executable profile.
General relocation, dynamic linking, JIT/self-modifying code, device memory and
privileged execution are outside that profile. The [ELF reference](elf.md) and
[function selection rules](elf-function-window.md) define its exact limits.

A consolidated deployment manifest is a broader design requirement. Current
certificates bind their exact file/function/specification and resource premises;
they do not automatically provide every field below.

| Field group | Information required for a deployment claim |
| --- | --- |
| Formalization | Pinned Lean and dependency revisions, semantic profile, theorem identifiers and axiom report |
| Artifact | Exact checked bytes, function/entry selection, segments, permissions, relocations and dependency identities |
| Build provenance | Available source inputs, compiler/assembler/linker identities and options; source/IR revision when preservation is claimed |
| Machine and runtime | ISA features, memory types, relevant errata/control-state assumptions, ABI, library and loader contracts |
| Process and OS | Mappings, stack/TLS, arguments, descriptors/capabilities, signals, limits and relevant kernel configuration |
| Environment | Allowed peers/writers, failures, termination, fairness, resource bounds and virtualization assumptions |

Hashes and versions identify evidence; they do not prove implementation
correctness or that checked bytes are the bytes later executed. A deployment
using hashes needs an integrity/collision assumption and an artifact-binding
mechanism. ASLR needs an allowed-address/relocation theorem or a stated profile
restriction. See [artifact binding](verification.md#4-bind-the-theorem-to-the-real-build).

## Machine semantics and native boundaries

### Instruction and memory semantics

Exact-byte decoding connects instruction lengths, operands and address
calculations to execution. Supported semantics distinguish register widths and
aliases, flags and undefined flag choices, accessible memory, permissions and
control transfers. Decode failure and unsupported operations cannot silently
become successful no-ops. Modeled errors do not prove a particular physical
exception or vulnerability.

Ordinary sequential RAM writes supply no concurrent atomicity theorem. The
separate store-buffer and atomic models have explicit issue, forwarding,
publication and RMW rules. Their relation to published x86-TSO models and
physical hardware remains a separate obligation. See [store buffers](mixed-store-buffer.md),
[atomic exchange](atomic-exchange.md) and [managed full64 execution](managed-fetch-add64.md).

### Calling conventions and syscalls

The scalar call contract binds up to six integer arguments, actual return/RSP
behavior, callee-saved registers and nonarithmetic flags. Current code and
original stack authority remain required throughout execution. Specialized
writable-call profiles add private stack and data-region effects.

The Linux syscall interface is separate: argument registers are RDI, RSI, RDX,
R10, R8 and R9. Existing syscall models expose a request and contracted service
behavior/resumption; they do not execute privileged entry, SYSRET or Linux
implementation bytes. A libc wrapper's error conversion, `errno` and TLS are
additional library behavior. [Concurrent syscall boundaries](concurrent-syscalls.md)
state their queue and lifecycle restrictions.

A syscall does not automatically supply a source-language synchronization edge.
Failure, partial effects, interruption, restart and blocking require the
selected service contract and a corresponding progress argument.

### ELF, linking, loading, and startup

The checked ELF layer validates its restricted file structure, loadable ranges,
permissions, entry and selected function bytes. A named-function certificate
binds the complete file and name, including a function away from the entry.
Its callable theorem still needs current text, fresh loading/caller premises
and original resource authority. It establishes no blanket property of the
rest of the image or the native startup path.

Broader static deployment requires reachable callees, startup/runtime objects,
stack, auxiliary data and TLS contracts. Dynamic loading additionally needs
actual dependency selection, relocations, GOT/PLT, symbol interposition and
versioning, constructors, TLS and later-loaded code. Freezing a library version
alone does not control which image a native loader selects.

### Library and runtime choice

A foreign call needs functional behavior, a memory footprint, ownership transfer,
threading effects and failure/progress contracts. A runtime contract remains an
assumption until the relevant implementation and its composition are proved.
Thread creation includes stack/TLS setup and lifecycle bookkeeping; allocation,
buffered I/O and exception handling likewise exceed a raw syscall boundary.
Unknown calls must expose conservative effects or be rejected by the profile.

## Trust and claim levels

The [trust ledger](trust.md) separates Lean proofs, explicit external contracts
and empirical evidence. The main boundaries are:

| Boundary | Required basis |
| --- | --- |
| Logic and proof checking | Pinned Lean kernel, reported foundational axioms and audited proof terms |
| Specification adequacy | Review of the independent requirement, observations and useful input domain |
| Compiler, assembler and linker | Checked final-byte proofs; separate preservation evidence for source claims |
| ABI, loader and runtime | Proved modeled relations plus explicit native implementation/start-state assumptions |
| Linux and hardware | Stated syscall, scheduling, architecture, memory-model and physical-conformance assumptions |
| External world | Permitted interference, signals, resource exhaustion, termination and progress conditions |

Logical principals and ownership tickets do not authenticate native OS authority.
A physical execution claim must account for debugger/ptrace mutation, DMA,
hardware faults or hostile privileged code when admitted; ordinary functional
profiles exclude those actions. Interrupts can still affect scheduling even
without user signal handlers. Cache timing and speculation require additional
models for timing or side-channel claims.

## Existing work: reuse candidates and limits

The [research map](research-map.md) records ISA, concurrency, program-logic and
verified-kernel references. Reuse needs a pinned revision, scope/license review
and audited proof dependencies. Results in another prover require a checked
bridge; a formal model or a verified kernel elsewhere supplies no automatic
Lean theorem about Linux or this program.

## Platform completion gates

An added profile needs reviewed semantics and assumptions, independent behavior
and rejection checks, sound decode/load/call composition, exact artifact binding,
and a reproducible proof/assumption report. Native conformance observations can
reveal model disagreements but do not prove physical correspondence. Commands
and maintained gates belong in [validation](validation.md); future scope belongs
in the [roadmap](roadmap.md).

Cost claims use a named metric in the selected model. Retired userspace
instructions, OS steps, hardware micro-operations and wall-clock time are
different quantities. An external syscall contract supplies no kernel
instruction bound. See [cost models](cost-model.md) for the additional
obligations behind lower bounds and optimality.
