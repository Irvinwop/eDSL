<a id="documentation"></a>

# eDieSeL documentation

eDieSeL is a Lean 4 library for proving behavior and resource properties of
machine-code programs. Its current reusable entry point covers restricted
sequential x86-64 functions; additional call, memory, process and concurrency
profiles have their own contracts. The broader goal includes verification of
kernel and operating-system components.

Read [implementation status](implementation-status.md) and [coverage](coverage.md)
for supported capabilities, and [trust](trust.md) for the assumptions behind a
proof. Source-language frontends and a privileged kernel target remain future
work.

The latest [signed signum measurement](../corpus/measurements/signed-signum32-v1/)
records the accepted source and full-gate evidence for validated conditional
coverage of **20/40 functions and 40/80 artifacts**, including **three distinct
concurrent functions**; **20 functions / 40 artifacts** remain. Fetch-add and
plain load/store retain their separate managed models.

## Verify a program

| Task | Start here |
| --- | --- |
| Prove a new function against your own contract | [Complete worked example](verify-a-function.md), then [the reusable checker](reusable-checker.md) |
| Import exact machine code | [Raw/ELF CFG import](cfg.md) or [named-function ELF import](named-elf-import.md) |
| Supply caller or input-buffer authority | [Scalar calls and loop frames](pure-call.md), [scratch-frame proofs](scratch-frame.md), [buffer calls](bounded-byte-scans.md), [read-only call transport](read-only-call-transport.md), [caller resource domain](call-resource-domain.md) |
| Bind a theorem to a final file | [Standalone scalar ELF certificates](elf-certificates.md) or [registered-contract certificates](corpus-certificates.md) |
| Check and reproduce a proof | [Build and validation](validation.md), [proof packets and grading](grading.md) |

An import checks code structure and artifact identity. The client still proves
an independently stated result and supplies current resource premises.
[Binary-first verification](binary-first.md) explains this division;
[verification guide](verification.md) describes the required evidence.

## Find or extend the library

Use the [repository map](repository-layout.md) to choose an import or add a
client, and [architecture](architecture.md) to understand the proof layers.
The [frozen corpus](compiler-corpus.md) and [measured blockers](corpus-blockers.md)
show where existing proof coverage ends. The [roadmap](roadmap.md) separates
accepted work from planned extensions.

For a new semantic domain, read the [language plan](languages.md),
[platform model](platform-model.md), [OS contracts](os-semantics.md) and
[OS implementation track](os-implementation.md). The [research map](research-map.md)
collects related work; [cost-model guide](cost-model.md) explains instruction-count
and lower-bound claims.

## Memory and OS resources

| Need | References |
| --- | --- |
| Mappings, permissions and lifetimes | [Address spaces](address-space.md), [ownership](ownership.md), [borrowing](borrowing.md) |
| Writable calls and private stacks | [Call stack](call-stack.md), [DATA8 calls](call-memory64.md), [counted helper calls](call-memory-loop64.md) |
| Threads and shared atomics | [Threads](threads.md), [exchange](atomic-exchange.md), [atomic handles](atomic-handles.md), [fetch-add](fetch-add.md) |
| Full64 managed concurrency | [Atomic foundations](atomic-fetch-add64.md), [scheduler and histories](managed-fetch-add64.md), [frozen certificates](concurrent-fetch-add-certificates.md) |
| Arithmetic RMW and current OS authority | [Universal XADD/ADD/INC coupling and retained resources](native-add-rmw64-os.md), [captured-delta event origins](arithmetic-rmw-origin.md), [arithmetic scheduler families](arithmetic-rmw-scheduler.md), [mixed instruction graphs](mixed-cfg.md) |
| Declared atomic interface graphs | [C23 event graphs](c23-atomic-events.md), [sound finite admission](c23-atomic-checker.md), and [checked graphs from actual finite executions](checked-atomic-traces.md) |
| Scheduler proof rules | [Instruction admission, buffered execution and shared RET facts](managed-vc-rules.md) |
| Checked effects in the scheduler | [Current-state admission, private FIFO effects and actual schedule simulation](effect-scheduler-bridge.md), [resumable ordinary/RMW blocks](mixed-resumption.md) |
| Counted shared-word workers | [Independent cohort contract](counter-contracts.md), [complete-file certificates and loaded overlaps](counted-certificates.md) |
| Managed load/store bodies | [One checked method family, resources and useful execution witnesses](managed-plain-methods.md), [accepted corpus measurement](../corpus/measurements/managed-plain64-v1/) |
| Atomic method foundations | [Independent call contracts, finite queue closure and order weakening](atomic-call-contracts.md) |
| Weak memory and call histories | [Managed store traces](managed-store-trace.md), [managed-word TSO refinement](word-tso-refinement.md), [mixed-width store buffers](mixed-store-buffer.md), [TSO counter](tso-counter.md), [linearizability](counter-call-linearizability.md) |
| Locks and blocking | [Mutexes](mutex.md), [buffered mutex](store-buffers.md), [syscall boundaries](concurrent-syscalls.md), [futexes](futex.md), [predicate rechecking](futex-predicate.md) |
| Process boundaries | [Restricted ELF loading](elf.md), [exit](process-exit.md), [write/exit](process-write.md) |

## Machine semantics and artifacts

| Need | References |
| --- | --- |
| Execution, branches and loops | [Control flow](control-flow.md), [CFG proofs](cfg.md), [explicit CFG bounds](cfg-profiles.md), [effect-independent structure and continuation](structural-cfg.md), [effect-aware VCs](effect-vcg.md), [short branches](sequential-short-jcc.md) |
| Caller-only execution across changed RAM | [Exact execution transport](caller-only-transport.md), [reusing sequential proofs in the OS model](caller-only-os-proofs.md) |
| Register and memory instructions | [Moves](sequential-moves.md), [memory64](memory64.md), [arithmetic64](sequential-arithmetic64.md), [memory addition](sequential-add-memory64.md), [logic64](sequential-logical64.md) |
| Native arithmetic RMW | [Exact qword XADD/ADD/INC CPU family and compatibility](native-add-rmw64-isa.md) |
| Conditions and operand widths | [Corpus ISA](sequential-corpus-isa.md), [CMOV64](sequential-cmov64.md), [CMOV32](sequential-cmov32.md), [byte order](sequential-byte-order.md), [low32 logic and CMP64](sequential-parity-isa.md), [SUB32/CMP32 imm8](sequential-immediate32.md), [LEA32 and byte TEST](address32-byte-test.md), [low-byte results](low8-results.md) |
| Unary, counter and shift rules | [NEG32/BSWAP64](sequential-unary.md), [counter/address rules](popcount.md#reusable-proof-components), [SHR64 by one](shift-one.md), [SHR/SAR32 and vector effects](shift-right32.md), [ROL64 by CL](rotate.md) |
| Exact executable identity | [ELF windows](elf-function-window.md), [named symbols](elf-function-symbol.md), [certificate composition](corpus-certificates.md) |

## Reference clients and specialized profiles

These examples reuse the library under their stated profiles:

- Scalar contracts: [comparisons](compiler-comparison-claims.md),
  [arithmetic](compiler-arithmetic.md), [clamp32](compiler-clamp32.md),
  [unary functions](unary-functions.md), [popcount](popcount.md),
  [unsigned average](unsigned-average.md), [parity](parity.md) and
  [rotation](rotate.md).
- Read-only loops: [byte scans](bounded-byte-scans.md),
  [first-match searches](first-match-searches.md),
  [paired byte comparison](paired-byte-comparison.md),
  [byte equality](byte-equality.md), [sum32](sum32.md),
  [pair32](pair32.md), [array sum64](array-sum64.md) and
  [array maximum64](array-maximum64.md).
- Mutation and workers: [store/return32](store-return32.md),
  [counted stores](counted-store64.md), [atomic workers](atomic-workers.md)
  and [atomic set workers](atomic-set-workers.md). The
  [coverage reference](coverage.md) links the remaining specialized profiles.

## Contributing and findings

See [contributing](../CONTRIBUTING.md) for development guidance and the
[security policy](../SECURITY.md) for reporting vulnerabilities in eDieSeL.
[Evidence guidance](findings.md) covers results from analyzing other programs.
