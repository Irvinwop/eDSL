# Buffered x86 execution

`EDSL.OS.TSO` adds explicit FIFO store buffers to the supported x86 instruction
slice. It is a separate scheduler from the immediate-visibility
`OS.MachineThreads` model used by the current universal mutex certificates.
The buffer semantics are prerequisites for extending those certificates to
weak-memory executions; the existing certificates do not acquire that claim
merely by importing this module.

## Execution boundary

Each worker has a private register/flags/RIP context, a return marker and an
oldest-first queue of ordinary stores. Starting with empty queues, or with
`BuffersValid`, all pending stores satisfy the aligned four-byte profile.
Shared memory contains
bytes and read/write/execute permissions. The action list explicitly chooses
instruction issues and independent buffer drains:

- Instruction fetch reads shared executable bytes. The decoded instruction
  executes through `X86.executeInstruction`, the same execution definition
  used by `X86.step`.
- An ordinary MOV store validates its complete operand, advances its actual
  context, and appends its address/value to the issuing worker's FIFO. It does
  not immediately change shared bytes.
- Ordinary loads read shared RAM overlaid by that worker's pending writes.
  The most recent pending matching byte wins. They do not read peer buffers.
- XCHG and locked XADD wait while their own FIFO is nonempty. A blocked issue
  leaves the whole state unchanged and retires no instruction. With an empty
  FIFO, the operation updates shared RAM indivisibly and retains its actual
  old/new event. It does not require peer FIFOs to be empty.
- A drain commits only the selected FIFO's oldest store. It preserves the
  worker's context and return marker, and retires no user instruction.
- Actual RET advances RSP and reads its target through the local data view.
  RET does not flush the FIFO. Draining a returned worker remains permitted.
  `Finished` therefore requires both actual returns and empty buffers.

Missing workers, already-returned instruction selections, empty-buffer drains,
unsupported alignment, architectural errors and syscall boundaries are explicit
errors. Instruction issue rejects writes to executable bytes. Raw state/queue
constructors do not establish admission. No mutex, phase, guard, loan,
expected opcode or endpoint checker chooses the instruction.

The model has fixed mappings and permissions. The aligned four-byte data
profile uses `atomicAddressable`, with canonical/nonwrapping operands and no
cache-line or page crossing. Its physical interpretation assumes coherent
write-back RAM, stable translation, no physical aliases or mixed-size overlapping
accesses, and no self-modifying code. Stack accesses keep the existing eight-byte
RET contract; callers must exclude overlapping concurrent data stores. Devices,
non-temporal stores, exceptions, interrupts, page-table changes, MFENCE and
other unsupported instructions are outside this slice. Unsupported does not
mean defective.

## Checked results

`X86.StoreBuffer` proves newest-store forwarding, FIFO drain invariance,
code/read/return-stack framing, and exact permission/accessibility preservation
for checked pending writes. Disjoint ordinary writes commute bytewise, including
modular addresses. The queue is unbounded; no finite-capacity or eventual-drain
assumption is hidden in these safety lemmas.

`TSO.schedule_trace` and its converse connect the evaluator and finite traces.
`issue_effect` characterizes queued stores, ordinary execution, actual returns,
atomic retirement and blocked issues in both directions. Its ordinary cases
prove equality of the complete output memory with the local input view, while
atomic cases retain the complete shared-memory transition. `BuffersValid`
survives successful issues, drains and schedules. `MemoryFrame` preserves
permission functions, the exact mapped-byte domain and every executable byte;
`initial_schedule_code` derives code preservation from actual initial code and
an executed prefix, with no endpoint premise.

`TSO.drain_ok` exposes the actual FIFO head and complete resulting state;
`TSO.drain_view` proves that publication leaves the selected worker's local
view unchanged. Drains, stalls and retired instructions remain distinct in the
trace, so buffer scheduling is not charged as user instructions.

`publish_worker` constructs publication in exactly the current queue length
from current writable-operand facts, retaining context, return flag and local
view. `publish_after_schedule` obtains those facts from any successful prefix
starting with empty buffers. The publication suffix contains no retired
instructions or RMW events, and works for a caller that already returned.
It establishes an available path, without an eventual-drain assumption.

`MutexReplay.Footprints` derives lock/payload separation and worker code/stack
footprints from current ownership, registration and actual stored read loans.
Its queue-frame theorems preserve instruction fetch, saved return reads and lock
observations through buffered payload stores. The existing invariant establishes
payload byte addressability, while aligned payload `atomicAddressable` remains
an explicit additional profile requirement. Buffered mutex admission must also
establish `dataOnly` for both lock and payload destinations. Separation from a
particular code image does not prove that those bytes lack execute permission.

`tests/StoreBuffer.lean` checks independent byte-level forwarding and framing.
`tests/TSO.lean` executes owned machine bytes for the two-location store-buffer
litmus: both reads can return zero before either buffered store drains. The six
ordinary immediate-visibility interleavings exclude that outcome. Further
regressions exercise same-address forwarding, RET before publication, drains
after return, and the existing mutex routine stalling at release until its two
payload stores publish in FIFO order.

These are model proofs and owned regression executions. Universal transfer of
the mutex's total/resource/cost theorem to arbitrary buffered interleavings
still requires the simulation that relates pending writes, exclusive guards
and the OS resource state. Hardware conformance, native thread identity,
fairness, elapsed time, store-buffer capacity and Linux runtime refinement also
remain separate obligations. Native tests of the immediate-visibility certified
profiles do not discharge them.

## References

The programmer-level FIFO/forwarding and locked-operation rules follow
[Sewell et al., x86-TSO](https://www.cl.cam.ac.uk/~mom22/cacm10.pdf), especially
Section 3. The implementation does not reproduce the paper's entire instruction
or axiomatic model and does not prove equivalence to its HOL4 formalization.
The [Intel system programming manual](https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html)
documents the target memory-ordering rules; it is a specification reference,
not an unchecked axiom imported into Lean.
