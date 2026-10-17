# eDSL

**Lean 4 eDSLs and proofs for GNU C23, GNU C++26, LLVM IR, assembly, and the
operating-system behavior of programs.**

The goal is to prove that a particular compiler-produced executable satisfies
an independently stated specification on a particular architecture and OS
profile. Threads, locks, atomicity, memory ordering, allocation, mappings,
resource lifetimes, and failures are central parts of that statement.

The implementation and proof language is **Lean 4**. C/C++, LLVM IR, and
assembly are the languages being modeled and generated. Native fixtures and
necessary runtime shims can use C/C++/assembly.

The repository is **public**. Any actual security findings, metadata and
reproducers stay in ignored local storage and are never committed or uploaded
to CI. The [findings policy](findings/README.md) keeps them separate from the
owned synthetic fixtures used to test the verifier.

## What the eventual guarantee means

Given an independent specification, final executable bytes, build identity,
and platform profile, produce a Lean-checked proof that every admitted
execution satisfies the specification, under its explicit input and environment
assumptions. Termination and progress require their own proofs and scheduler
assumptions. Unsupported code, invalid certificates, and timeouts are reported;
they do not count as proofs.

The main strategy is **direct binary verification**: any supported source
language/compiler produces candidate code, and Lean checks that the final bytes
meet the specification. One machine-code semantics serves those inputs.
Source/IR semantics and translation validation add optional source-preservation
guarantees; they are not prerequisites for a direct binary-property theorem.
We can also prove small lowering passes correct in Lean. These routes do not
make an arbitrary Linux kernel, physical CPU, library, or dynamic loader
verified by assumption. Their contracts
and remaining trust must appear in the result.

## Current status

Implemented and checked:

- A pinned Lean 4 / Lake project, with warnings treated as errors.
- A [fixed-contract proof grader](docs/grading.md) for pair/stride sums and owned-word
  stores, with data-only proof packets, fresh checked helper declarations,
  exact-artifact binding, useful input witnesses and required current OS
  authority and registered effects. The store evolves checked OS resources
  along actual machine steps and retains all outside-target memory and loans.
  Shared expression packets carry fresh proofs for different stride, two-store,
  and MOV store/readback implementations; legacy packets remain accepted.
  The registry and platform profile are limited.
  A separate instruction-count proof shows the word-store task needs at least
  two modeled instructions on useful inputs; the checked store/RET attains two.
  This is a bound within the current ISA model, with no CPU-time claim.
- A generic behavior-refinement interface, composition, and safety transfer.
- A restricted x86-64 byte decoder, instruction/stack/memory semantics, and an
  unbounded execution relation with evaluator soundness and completeness.
- All-input theorems for actual Clang/GCC increment, 32-bit load and 32-bit store
  bytes, including register/memory framing, return behavior and termination.
- An exact atomic-exchange byte profile with a labeled indivisible RMW event,
  OS-cell projection, guarded resource authority and same-cell value-flow histories.
- Shared atomic handles with per-actor authorization, allocation reservations,
  permanent revocation, read-loan stability and exchange-trace value conservation.
- Locked fetch-add with arithmetic flags, exact compiler certificates, guarded
  OS-handle composition and all-finite-trace modular counter results.
- Mutable atomic workers with actual MOV/XCHG/RET instruction scheduling,
  retained old results through join, resource revocation and schedule value-flow proofs.
- Counted locked-add workers with actual instruction dispatch, per-worker
  `3*count+3` cost, modular sums for every completing schedule and constructive full collection.
- A checked mutex protocol with exclusive fresh guards, protected payload
  invariants, permanent revocation and exact exchange/load/store binary bridges.
- Complete mutex-worker architectural execution with generic control/payload
  preservation, modular totals, zero returns and exact retry costs for every
  completed admitted interleaving. Every existing unfinished selection is
  enabled, and a completing schedule is constructed from any admitted prefix.
  See [contracts and remaining proofs](docs/mutex-workers.md).
- Checked mutex-worker code/return-stack readiness, positive cohort collection
  and exact code/stack loan revocation, with unrelated loan records preserved.
- A separate buffered x86 scheduler with FIFO publication, own-store
  forwarding, locked-operation stalls, and explicit drain/retirement events.
- Universal mutex execution over those buffers: arbitrary finite traces lift
  to checked OS replay, completed runs meet total/return/resource contracts,
  and every admitted paused prefix has a constructive completing continuation.
  See [buffered execution and its current limits](docs/store-buffers.md).
- Concurrent syscall suspension with fresh invocation IDs, current-memory
  return contracts, peer-state preservation and proved rejection of reused IDs.
  See [concurrent syscall boundaries](docs/concurrent-syscalls.md).
- A one-word private futex service with actual syscall capture, mutable-word
  pins, current-RAM comparison, eligible wake selection, typed resumption and
  checked quiescent cleanup. Exact WAIT/WAKE1 stub certificates and owned native
  observations have separate contracts. See [scope and remaining proofs](docs/futex.md).
- Preserved current admission for fixed futex clients: WAIT, a payload
  STORE/XCHG-one/WAKE1/RET publisher, and a separate buffered producer. Every
  actual physical issue/drain prefix has an exact managed lift; current typed
  ready calls enable protected RET with full raw results and arbitrary private
  clobbers. Publication and persistent W=1 follow from actual code and FIFO
  authority. The new exact client artifact contract remains conditional on
  current cohort admission and code binding; it proves no scheduling progress
  or safety of a whole kernel or distribution. See [client coverage](docs/futex.md).
- Private-word notification across mixed client traces: with one WAIT client
  expecting a value different from one, the publisher's actual XCHG and
  associated WAKE1 leave no queued WAIT, and later admitted execution preserves
  that fact. Every supported WAIT stage has a bounded continuation through RET;
  scheduler fairness and predicate acquisition remain separate.
  See [notification contracts](docs/futex-notification.md).
- A predicate-rechecking private WAIT loop with fresh invocation/pin lifetimes,
  persistent notification safety and constructive completion within 14 modeled
  runtime actions after notification. The independent contract requires actual
  return1/current W1 and RAM/peer frames under a declared 0/1 signal protocol.
  See [predicate-loop contracts](docs/futex-predicate.md).
- A counted assembly loop with a proved invariant and termination for every
  64-bit count, modular arithmetic result and exact `2*count+3` user-instruction cost.
- Ordinary C `sum32` pointer/count and indexed loops share an independent
  list-sum contract modulo 2^32. A structural decoded-CFG checker proves
  termination for every undefined-AF choice stream, full RAX zero extension,
  memory/register frames, exact operand reads and derived instruction costs.
  Current code/stack/input read loans compose with the same theorem; empty
  input needs no input loan or readable/canonical input pointer. See
  [the checked sum32 scope](docs/sum32.md).
- A reusable read-only CFG checker with sparse cutpoints and local Lean proof
  obligations, actual-byte binding, all-AF termination/safety and optional exact
  accounting. `edsl-cfg-import` checks raw or explicit-span ELF graphs; imported
  code still needs independent functional and current-read-permission proofs.
  See [local control-flow proofs](docs/cfg.md).
- A two-loop compiler-output instance proves the independent sum of two lists,
  exact `6*(lengthA+lengthB)+6` instructions and ordered reads. Its OS bridge
  retains both current input admissions, including compatible readonly aliases.
  See [two-array sums](docs/pair32.md).
- Little-endian mapped-memory reads and guarded writes with per-byte permissions,
  read-after-write and disjoint code/stack preservation proofs.
- Ordinary MOV32 register copies, loads and stores, plus MOV64 copies and XCHG64 across
  all 16 GPRs, in the separate sequential backend. Memory operands use full 64-bit
  base/SIB addressing and pre-state aliasing. Current owner resources compose
  full-pointer copies with actual loads/stores and retain the code, stack and
  outside memory frames through the decoded instruction length. See
  [MOV and OS resource scope](docs/sequential-moves.md).
- LEA64 address arithmetic and register ADD64 in that sequential backend.
  LEA preserves all flags and computes without a data access, including
  noncanonical values; ADD defines all six arithmetic flags. Both retain
  complete RAM and current OS authority under register aliasing. See
  [arithmetic scope](docs/sequential-arithmetic64.md).
- Memory-source ADD64 in the sequential backend reads a complete qword at the
  old full64 base/SIB address, defines all six arithmetic flags and retains
  the complete memory frame. Named current read loans and array resources
  enable actual steps, including destination/address aliases and RSP changes
  with the original caller slot retained. See
  [memory-source addition](docs/sequential-add-memory64.md).
- Register-only CMOV64 with all sixteen flag conditions and all 16 GPRs.
  Signed/unsigned CMP conditions are proved against mathematical order.
  A pure-call OS resource bridge retains the same code/caller-slot loans
  and complete RAM, including conditional RSP changes and actual RET.
  See [conditional moves](docs/sequential-cmov64.md).
- Direct nested CALL/RET with current OS-owned private stack frames, checked
  full64 PUSH/POP and signed-displacement LEA. Four whole GCC/Clang outputs
  prove the same modular `x + 2` result, ABI frame and reusable resources;
  exact costs are five/seven instructions. A separate sibling engine retains
  actual RAM-derived return targets. See [owned calls](docs/call-stack.md).
- A separate [call-stack proof grader](docs/call-stack-grading.md) fixes that
  full64 result and current-resource contract for arbitrary admitted code
  windows and selected entries. Fresh proof packets certify all four nested
  compiler outputs and a different LEA/RET implementation in raw and full-ELF
  form, under the existing packet limits. Complete instruction encodings must
  stay within the selected window. A separate lower-bound theorem requires two
  modeled instructions when RAX must change; LEA/RET attains two. Acceptance
  requires neither a CALL nor a particular count or compiler profile.
- [Callable DATA8 and private-stack composition](docs/call-memory64.md) in a
  sibling verification library. Actual GCC/Clang store/reload helpers meet one
  independent target/result contract through current DATA and stack ownership,
  complete fetch coverage and a union RAM frame. Both complete 18-byte texts
  take eight modeled instructions. Existing fixed grader tasks retain their scope.
- A separate [callable DATA8 grader](docs/call-memory64-grading.md) checks that
  independent contract on exact raw/ELF windows and selected entries. Nested
  compiler clients and a three-instruction store/LEA/RET client pass the same
  task under existing proof budgets. A separate theorem proves a minimum of
  three modeled instructions when both incoming outputs need to change.
- [Counted helper calls](docs/call-memory-loop64.md) with complete 45-byte GCC
  and 52-byte Clang texts prove `RAX = x+n mod 2^64`, old DATA retention at zero
  and `DATA = x+n-1 mod 2^64` otherwise. Both universal claims cover arbitrary
  current admitted resources, old DATA words, all full64 values/counts and AF
  streams, with a 32-byte private-stack requirement and reusable DATA/stack
  ownership. The default gate binds fresh complete text to the universal
  proofs and requires native observations, dependency audits, fresh kernel
  replay and source stability. Exact model instruction costs are separate.
- All sixteen short conditional branches in the sequential backend, with
  signed displacements, taken-target checks, checked CFG edges and preservation
  of the same current OS resource world. See [branch scope](docs/sequential-short-jcc.md).
- Six complete GCC/Clang comparison outputs prove full64 unsigned maximum,
  unsigned minimum and signed maximum against independent mathematical order.
  The three grading tasks retain current code/caller-slot authority and the
  full memory/ABI frame; separate proofs count four instructions including RET.
  See [comparison clients](docs/comparison64.md).
- Full64 unsigned array maximum with zero for empty input, independent current
  array loans, compatible read-only aliases and no unused-base requirement.
  Complete 26-byte GCC and 32-byte Clang client proofs retain the full RAM,
  register and return frame. Separate costs are `7*n+5` and four/`6*n+5` for
  empty/nonempty Clang input. See [array maximum](docs/array-maximum64.md).
- Full64 modular array sum against an independent natural-sum specification,
  with current array/caller loans, empty-input exceptions and compatible
  read-only aliases. Complete 22-byte GCC and 25-byte Clang client proofs cover
  wrapping sums, all AF choices and the full memory/register/return frame.
  Separate costs are `5*n+6` and four/`4*n+5` for empty/nonempty Clang input;
  default integration requires model, proof-packet and finite native gates.
  See [array sum](docs/array-sum64.md).
- Fresh proofs for complete 13-byte GCC and 15-byte Clang direct-add outputs
  against the same counted-store task, including all full64 counts, actual
  checked OS writes and reusable returned authority. Exact costs are 4/5 and
  5/6 for zero/positive count. See [direct-add clients](docs/counted-store-direct64.md).
- Full 64-bit memory loads/stores with complete eight-byte checks and extended
  base/SIB addressing. Owner/epoch authority, read-only borrowing and checked
  histories retain outside cells, permissions and live loans. Direct raw/ELF
  certificates bind GNU23/GNU++26 store/load/RET output to a full 64-bit result
  and the same evolved current OS world. The existing 32-bit task effects keep
  their width. See [eight-byte memory contracts](docs/memory64.md).
- A distinct [`storeReturnValue64` grading task](docs/store-return-value64.md)
  requires full64 storage and return with current eight-byte ownership.
  Fresh clients prove mixed32/64 writes without a data load and an upper-half
  DATA4 read before the store, retaining actual effect widths, checked histories
  and returned authority. Neither shape nor accounting constrains acceptance.
- Direct raw/ELF certificates for GNU23 compiler outputs that store a low32
  argument and return the full target pointer. Both store/copy orderings carry
  the actual checked OS update, memory/ABI frames and exact three-instruction
  accounting. A distinct `storeReturn32` grader also accepts a fresh
  four-instruction client proof outside those direct certificate shapes.
  A five-byte GCC13 `-Oz` exchange/store/RET client carries the same independent
  contract, actual current OS effects and three-instruction accounting.
  A separate three-instruction lower bound covers useful inputs requiring a
  changed RAX under the registered policy.
  See [pointer-returning stores](docs/store-return32.md) and [grading](docs/grading.md).
- Separate GCC13 and Clang18 counted-store profiles prove the same independent
  full64 result and complete frames for every full64 count, with actual evolving
  OS ownership. Exact instruction costs are `6*N+4` and `4*N+4`, including RET.
  The distinct [`countedStore64` grading task](docs/counted-store64-grading.md)
  accepts both proofs under one fixed contract, with accounting kept separate.
  A [fresh final-store loop client](docs/counted-store-final64.md) proves the
  same task outside the trusted registry, retaining old target contents through
  the register loop before one checked positive-count store.
  See [counted stores](docs/counted-store64.md) and the [Clang profile](docs/counted-store64-clang.md).
- A sequential OS address-space model with checked mapping, protection and
  unmapping, permission-revocation proofs and composition with a binary contract.
- A checked OS word store whose cell update projects exactly to the machine
  store, with all-input compiler-binary composition and retained permissions.
- A sequential allocation registry with fresh lifetime IDs, revoking transfer
  epochs, managed-history invariants and owned-store composition with exact bytes.
- Shared read loans with whole-allocation freezing, permanent loan-ID revocation,
  managed-history byte/permission stability and actual binary-load composition.
- Managed read workers with checked spawn/join, current-shared-memory instruction
  scheduling, arbitrary-history result proofs and permanent thread/loan revocation.
- A restricted ELF64 loader with bounds, permissions, BSS and page-collision
  checks; full-file certificates derive executable entry-code binding.
- A standalone exit 42 ELF certificate, first-syscall execution proofs and an
  explicit single-thread Linux exit contract separating status from progress.
- A bounded stream-write/exit certificate covering short transfers, raw errors
  and an explicit return contract; complete output is conditional on full transfer.
- A Lean certificate CLI and live C/C++ compile→link→byte extraction→proof→native
  integration checks, with fail-closed rejection cases.
- Matching two-instruction function and three-instruction syscall lower bounds
  within the supported ISA subset, under stated initial-register conditions.
- Transitive axiom auditing, including generated certificates.
- Optional native GNU23/GNU++26 compiler probes retained from the bootstrap.

The function certifier accepts three two-instruction profiles, the three-instruction
`exchange32` and `fetch-add32` profiles and the counted `increment-loop` profile. The process certifier
accepts exit 42 (three user instructions) and write-exit 42 (eight across a completed write). Other correct
encodings remain unsupported. The separate counter certifier binds the exact
nineteen-byte locked-add loop to prepared OS-worker workload contracts.
The separate futex client certifier recognizes the exact 32-byte publishing
routine, with current admission and member/code binding left as explicit
semantic premises. The separate `edsl-certify-sum32` checks restricted decoded
pointer/count and index shapes, including supported zeroing-prologue variations
and reordered pointer/count updates, in at most 64 bytes and 32 static
instructions. Raw/full-ELF certificates retain explicit current caller
input/stack/resource conditions; an ELF function entry supplies no process
startup contract. Linux loader/kernel refinement, broader syscalls,
native lock/runtime refinement, weak memory and general source eDSLs/validators remain planned. See
the precise [implemented coverage and trust boundary](docs/coverage.md).

## Read the plan

| Document | Question it answers |
| --- | --- |
| [Implemented coverage](docs/coverage.md) | What can run and what has actually been proved? |
| [Address-space contracts](docs/address-space.md) | How do mapping and permission changes connect to binary proofs? |
| [Ownership and lifetimes](docs/ownership.md) | What prevents stale authority after release, address reuse or transfer? |
| [Shared read borrowing](docs/borrowing.md) | What keeps borrowed bytes and permissions stable across managed operations? |
| [Read-worker scheduling](docs/threads.md) | How do actual machine instructions compose with spawn, shared resources and join? |
| [Atomic exchange](docs/atomic-exchange.md) | How does an exact XCHG event update OS cells and respect existing read authority? |
| [Shared atomic handles](docs/atomic-handles.md) | How can actors share an atomic word while blocking conflicting resource changes? |
| [Fetch-add and counters](docs/fetch-add.md) | How do locked arithmetic, status flags and counter traces connect to compiler bytes and OS resources? |
| [Mutable atomic workers](docs/atomic-workers.md) | How do interleaved MOV/XCHG/RET instructions retain actual old values through join? |
| [Counted counter workers](docs/counter-workers.md) | How do independently counted locked-add workers establish the modular total, exact own-step costs and complete collection? |
| [Protected payloads and mutexes](docs/mutex.md) | How do exclusive guards, closed invariants and exact machine operations compose? |
| [Complete mutex worker execution](docs/mutex-workers.md) | How do arbitrary admitted architectural interleavings preserve OS contracts and admit completion? |
| [Buffered x86 execution](docs/store-buffers.md) | How do delayed stores, forwarding and locked operations differ from immediate visibility? |
| [Concurrent syscall boundaries](docs/concurrent-syscalls.md) | How do pending calls retain peer memory changes and consume invocation IDs once? |
| [Private futex service](docs/futex.md) | How do actual requests, mutable-word lifetime, queue eligibility and current RAM compose? |
| [Private-word notification](docs/futex-notification.md) | When do actual publication and wake prevent later queueing, and what completion is enabled? |
| [Predicate-rechecking WAIT](docs/futex-predicate.md) | When does the actual loop return1, and which postnotification suffix is constructively enabled? |
| [ELF container verification](docs/elf.md) | How do complete ELF bytes establish the executable entry code? |
| [Standalone exit contract](docs/process-exit.md) | What connects ELF entry execution to exit status, and what progress is assumed? |
| [Stream output and exit](docs/process-write.md) | How do short writes and errors compose with the next userspace instructions? |
| [Counted control flow](docs/control-flow.md) | How are a backward branch, loop invariant, termination and input-dependent cost proved? |
| [Ordinary sum32 loops](docs/sum32.md) | How do two compiler-produced loop shapes meet one sum, termination, memory, read-loan and cost contract? |
| [Checked CFGs and local proofs](docs/cfg.md) | How can new control-flow patterns use local Lean obligations against an independent task contract? |
| [Two-array sum proofs](docs/pair32.md) | How do two loops and two current input resources compose through that interface? |
| [Full64 array maximum](docs/array-maximum64.md) | How do different compiler loops meet one unsigned result and current array-resource contract? |
| [Full64 modular array sum](docs/array-sum64.md) | How do different full64 loops meet one wrapping-sum contract with current resources and separate cost proofs? |
| [Owned nested calls](docs/call-stack.md) | How do actual CALL/PUSH/POP/RET steps compose with current private-stack ownership and whole compiler text? |
| [Call-stack proof grading](docs/call-stack-grading.md) | How can different implementations prove the same callable result and resource contract at a selected raw/ELF entry? |
| [Callable DATA8 and private stack](docs/call-memory64.md) | How do actual helper stores/reloads compose with private CALL/PUSH writes and reusable current resources? |
| [Callable DATA8 grading](docs/call-memory64-grading.md) | How do nested and inlined implementations prove one owned-memory result with separate minimum-instruction accounting? |
| [Counted helper calls](docs/call-memory-loop64.md) | How do all-count helper loops preserve actual saved stack words, DATA and current resources? |
| [Roadmap and acceptance gates](docs/roadmap.md) | What must be built, in what order, and how will completion be established? |
| [Architecture](docs/architecture.md) | How do Lean models, compilers, certificates, and platform contracts fit together? |
| [Binary-first verification](docs/binary-first.md) | How can one machine-code target reduce source-language proof work? |
| [Verification](docs/verification.md) | What exact theorem connects the source to final executable bytes? |
| [Language domains](docs/languages.md) | What semantics do GNU C23, GNU C++26, LLVM IR, and assembly each need? |
| [OS semantics](docs/os-semantics.md) | Which OS facilities matter, and what must be proved or assumed about them? |
| [Platform model](docs/platform-model.md) | How do ISA, ABI, memory, loader, libraries, and kernel compose? |
| [OS implementation proofs](docs/os-implementation.md) | How can source/IR/assembly inputs discharge concrete OS contracts? |
| [Findings and reporting](docs/findings.md) | How do checked defects enter a private reporting queue? |
| [Costs and lower bounds](docs/cost-model.md) | When can we prove operation counts or optimality? |
| [Trust and evidence](docs/trust.md) | What is currently trusted, checked, assumed, or outside the claim? |
| [Reuse assessment](docs/research-map.md) | Which existing projects should be evaluated before building new machinery? |

Start with the roadmap, then the OS and platform documents. Restricted x86-64
functions, a counted loop and bounded stream-write/exit entries are checked;
ownership, lifetimes, shared read borrowing and managed read-worker scheduling
are checked too. An atomic-exchange foundation now connects XCHG events and
guarded OS cells. Shared atomic handles now preserve reservations and resource
lifetimes. Mutable atomic workers execute actual instructions against shared
cells and retain exchanged values privately through join. Counted locked-add
workers now establish the modular shared-counter workload and checked collection
across every successful completing supplied schedule. A separate mutex protocol
now protects payload invariants through exclusive guards and exact machine
operations. Complete critical-section workers now cover every admitted
instruction-only architectural interleaving, retain execution readiness, and
have schedule-independent completed totals, constructive completion and exact
retry costs. A zero-busy schedule attains the fixed routine's `13*n`
instruction lower bound. The separate buffered mutex proof also covers delayed
stores, independent drains and stalled release, with constructive continuation
from every admitted prefix. Hardware and concrete thread/runtime refinement
remain open.
General GNU C++26 ingestion and a fully verified Linux kernel are substantial
separate research work.

## Build

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake build EDSL edsl-certify edsl-certify-process edsl-certify-counter edsl-certify-mutex-worker edsl-certify-futex edsl-certify-futex-client edsl-certify-futex-predicate edsl-certify-sum32 edsl-cfg-import
lake build edsl-grade-call-stack edsl-proof-export tests.fixtures.CallStack.CoveredAudit tests.fixtures.CallStack.FoundationAudit tests.fixtures.CallStack.Inline.Accounting
lake env lean -DwarningAsError=true tests/X86.lean
lake env lean -DwarningAsError=true tests/Memory.lean
lake env lean -DwarningAsError=true tests/AddressSpace.lean
lake env lean -DwarningAsError=true tests/OSComposition.lean
lake env lean -DwarningAsError=true tests/WordStore.lean
lake env lean -DwarningAsError=true tests/ELF.lean
lake env lean -DwarningAsError=true tests/Process.lean
lake env lean -DwarningAsError=true tests/Write.lean
lake env lean -DwarningAsError=true tests/ControlFlow.lean
lake env lean -DwarningAsError=true tests/Ownership.lean
lake env lean -DwarningAsError=true tests/Borrowing.lean
lake env lean -DwarningAsError=true tests/Threads.lean
lake env lean -DwarningAsError=true tests/AtomicExchange.lean
lake env lean -DwarningAsError=true tests/OSAtomicExchange.lean
lake env lean -DwarningAsError=true tests/Atomics.lean
lake env lean -DwarningAsError=true tests/AtomicThreads.lean
lake env lean -DwarningAsError=true tests/FetchAdd.lean
lake env lean -DwarningAsError=true tests/CounterThreads.lean
lake env lean -DwarningAsError=true tests/CounterThreadsWitness.lean
lake env lean -DwarningAsError=true tests/Mutex.lean
lake env lean -DwarningAsError=true tests/MutexISA.lean
lake env lean -DwarningAsError=true tests/MutexReplay.lean
lake env lean -DwarningAsError=true tests/MutexInvariant.lean
lake env lean -DwarningAsError=true tests/MutexExecution.lean
lake env lean -DwarningAsError=true tests/StoreBuffer.lean
lake env lean -DwarningAsError=true tests/TSO.lean
lake env lean -DwarningAsError=true tests/MutexTSO.lean
lake env lean -DwarningAsError=true tests/Suspend.lean
lake env lean -DwarningAsError=true tests/FutexResources.lean
lake env lean -DwarningAsError=true tests/FutexStubs.lean
lake env lean -DwarningAsError=true tests/FutexService.lean
lake env lean -DwarningAsError=true tests/FutexPhysical.lean
lake env lean -DwarningAsError=true tests/FutexAdmission.lean
lake env lean -DwarningAsError=true tests/FutexClientFrames.lean
lake env lean -DwarningAsError=true tests/FutexClientControl.lean
lake env lean -DwarningAsError=true tests/FutexClientPhysical.lean
lake env lean -DwarningAsError=true tests/FutexClientCertificate.lean
lake env lean -DwarningAsError=true tests/FutexClientCoverage.lean
lake env lean -DwarningAsError=true tests/FutexNotification.lean
lake env lean -DwarningAsError=true tests/FutexNotificationCertificate.lean
lake env lean -DwarningAsError=true tests/FutexPredicate.lean
lake env lean -DwarningAsError=true tests/FutexPredicateCertificate.lean
lake env lean -DwarningAsError=true tests/FutexPredicateAccounting.lean
lake env lean -DwarningAsError=true tests/SequentialISA.lean
lake env lean -DwarningAsError=true tests/SequentialExecution.lean
lake env lean -DwarningAsError=true tests/SequentialMoves.lean
lake env lean -DwarningAsError=true tests/SequentialMoves64.lean
lake env lean -DwarningAsError=true tests/SequentialMoveResources.lean
lake env lean -DwarningAsError=true tests/SequentialAddMemory64.lean
lake env lean -DwarningAsError=true tests/SequentialAddMemory64Resources.lean
lake env lean -DwarningAsError=true tests/CallStackDomain.lean
lake env lean -DwarningAsError=true tests/CallStackCoverage.lean
lake env lean -DwarningAsError=true tests/GradingCallStackContract.lean
lake env lean -DwarningAsError=true tests/StoreReturn32Raw.lean
lake env lean -DwarningAsError=true tests/StoreReturn32Resources.lean
lake env lean -DwarningAsError=true tests/GradingStoreReturn.lean
lake env lean -DwarningAsError=true tests/StoreReturnRcx.lean
lake env lean -DwarningAsError=true tests/StoreReturnAccounting.lean
lake env lean -DwarningAsError=true tests/ArrayResources.lean
lake env lean -DwarningAsError=true tests/ArraySum64.lean
lake env lean -DwarningAsError=true tests/Sum32Pointer.lean
lake env lean -DwarningAsError=true tests/Sum32Index.lean
lake env lean -DwarningAsError=true tests/Sum32Artifact.lean
lake env lean -DwarningAsError=true tests/CFG.lean
lake env lean -DwarningAsError=true tests/Stride32.lean
lake env lean -DwarningAsError=true tests/Pair32.lean
lake env lean -DwarningAsError=true tests/Pair32Resources.lean
bash scripts/check-audit.sh
lake env leanchecker --fresh EDSL
bash scripts/verify-compilers.sh
bash scripts/verify-process.sh
bash scripts/verify-loops.sh
bash scripts/verify-fetch-add.sh
bash scripts/verify-counter-workers.sh
bash scripts/verify-mutex.sh
bash scripts/verify-mutex-workers.sh
bash scripts/verify-futex.sh
bash scripts/verify-futex-clients.sh
bash scripts/verify-futex-predicate.sh
EDSL_GCC=gcc-13 EDSL_CLANG=clang-18 bash scripts/verify-sum32.sh
EDSL_CLANG=clang-18 bash scripts/verify-sequential-moves.sh
EDSL_CLANG=clang-18 bash scripts/verify-sequential-arithmetic64.sh
EDSL_CLANG=clang-18 bash scripts/verify-sequential-add-memory64.sh
EDSL_GCC=gcc-13 EDSL_CLANG=clang-18 bash scripts/verify-array-sum64.sh
EDSL_GCC=gcc-13 EDSL_CLANG=clang-18 bash scripts/verify-call-stack.sh
bash scripts/verify-call-memory-loop64.sh
EDSL_GCC=gcc-13 EDSL_CLANG=clang-18 bash scripts/verify-counted-store-direct64.sh
EDSL_GCC=gcc-13 EDSL_CLANG=clang-18 bash scripts/verify-store-return32.sh
EDSL_GCC=gcc-13 EDSL_CLANG=clang-18 bash scripts/verify-store-return-grading.sh
EDSL_GCC=gcc-13 bash scripts/verify-store-return-xchg.sh
EDSL_GCC=gcc-13 EDSL_CLANG=clang-18 EDSL_CLANGXX=clang++-18 bash scripts/verify-store-load64.sh
EDSL_GCC=gcc-13 bash scripts/verify-counted-store64.sh
EDSL_CLANG=clang-18 bash scripts/verify-counted-store64-clang.sh
EDSL_GCC=gcc-13 EDSL_CLANG=clang-18 bash scripts/verify-counted-store64-grading.sh
EDSL_GCC=gcc-13 EDSL_CLANG=clang-18 bash scripts/verify-counted-store-final64.sh
EDSL_GCC=gcc-13 EDSL_CLANG=clang-18 EDSL_CLANGXX=clang++-18 bash scripts/verify-store-return-value64-grading.sh
EDSL_GCC=gcc-13 bash scripts/verify-cfg.sh
```

`lean-toolchain` pins Lean 4.35.0. The library currently needs no third-party
Lean packages. The audit rejects transitive axiom dependencies outside Lean's
standard `propext`, `Quot.sound`, and `Classical.choice`; it also rejects proof
holes. Its negative check injects an untrusted transitive dependency and
requires rejection. The bundled `leanchecker` replays the stored proofs in a
fresh kernel environment. These check the current declarations, not the adequacy of a future
language, OS, or hardware model. The compiler integration command also needs
Linux/x86-64, Clang, GCC and binutils; it uses only owned synthetic fixtures.
CI caches the pinned Lean toolchain and Lake build outputs. Compatible previous
builds supply incremental inputs; Lake still checks source and dependency traces.
Every run retains the contract tests, axiom audit, fresh kernel replay, and native
integration checks. Cache misses build normally. Bump the workflow's cache
version strings to discard old entries when diagnosing a cache problem.
The sum32 integration selects GCC 13 (`-Os -fno-ivopts`, GNU23 spelled `gnu2x`)
and Clang 18 (`-Oz`, `gnu23`), with scalar code and LTO/CET disabled. Its
certificates, native observations and provenance use `artifacts/sum32-fixtures/`.
The CFG integration uses GCC 13 and `flock`, checks complete raw/explicit-span
ELF imports, and separately proves the stride function's independent contract.
Its owned native observations and generated proofs use `artifacts/cfg-fixtures/`.
The array-sum integration uses GCC 13/Clang 18 GNU23 `-Os` outputs and writes
owned evidence to `artifacts/array-sum64/`. Its parallel workflow keeps a separate
partial build cache. Default success requires every model/proof and native gate;
`--native-only` explicitly leaves universal Lean validation `NOTRUN`.
The counted-helper default gate requires both native and formal validation of
the complete GCC/Clang texts; `--native-only` reports `formal=NOTRUN`. It retains
source/provenance snapshots and fresh kernel replay; see the
[proof scope and reproduction commands](docs/call-memory-loop64.md).

The optional native compiler probes are separate from proofs:

```sh
cmake -S . -B build -G Ninja \
  -DCMAKE_C_COMPILER=clang \
  -DCMAKE_CXX_COMPILER=clang++
cmake --build build
```

These require exact `-std=gnu23` and `-std=gnu++26` acceptance, checked with
Clang 18.1.3 for the bootstrap. They establish language-mode/syntax availability,
not complete language support or semantic preservation.

## License and contributions

[Apache-2.0](LICENSE), with attribution in [NOTICE](NOTICE) and research citation
metadata in [CITATION.cff](CITATION.cff). Contributions require a
[DCO 1.1 sign-off](CONTRIBUTING.md); contributors retain their copyrights.
