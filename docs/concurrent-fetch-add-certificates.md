# Frozen full64 concurrent fetch-add certificates

`Corpus.V1.FetchAddCertificates` certifies both unchanged final-ELF
`c_atomic_fetch_add64` windows against the fixed independent
`Grading.ConcurrentTask.FetchAdd64.Claim`. At their introduction, these
certificates brought conditional coverage to **5/40 functions, 10/80 compiler
artifacts and one distinct concurrent function**. See
[implementation status](implementation-status.md) for current totals. The
target model is `managed-tso64-closed-batch-v1`; its results remain conditional
on that model's machine and resource assumptions.

The GCC window is all 13 bytes at `0x403280`, including its original ENDBR64.
The Clang window is all nine bytes at `0x401ab0`. Full-file, unique symbol,
extent and executable mapping checks reuse the frozen ELF proofs. Compiler
options and frozen files are unchanged. CET indirect-branch tracking and shadow
stacks are disabled in the recorded target profile.

## One reusable proof path

`X86.VCGen.AtomicMethods.check` recognizes padding, argument copy, LOCK XADD
and RET using the production decoders. Its soundness proof covers the existing
managed scheduler. New compiler windows instantiate this checker rather than
introducing their own execution semantics or per-instruction proof chain.

`FetchAddBatch64.Admission.admit` constructs a whole-population method family
from the independent entry contract. Entry admission checks only actual present
code, full64 arguments, represented scalar ABI and current OS authority. It
does not require future success, a desired output, an initial counter value,
an accepted history or a candidate-provided invariant.

`FetchAddBatch64.Pre.complete` derives complete invocation/RMW/response histories
from actual successful completed schedules. Each original context denotes one
call occurrence; the entire context population belongs to the closed cohort.
Unique call IDs distinguish equal inputs and zero updates. Every selected-cell
RMW appears exactly once in chronological order, with the actual full64 input
and the current old word returned by that call. The history satisfies the
independently defined modular-counter relation and extends real-time order.
`Linearizability.Batch` supplies the shared finite-history protocol argument.

`FetchAddBatch64.Frames` proves all five independent Claim obligations:

- Completed schedules satisfy that exact history and return contract.
- Every successful prefix retains current resources and well-formedness.
- Every running worker has an enabled issue retiring one instruction, for
  either auxiliary arithmetic-flag input.
- An actual finite schedule completes the entire population.
- A positive uniform own-issue bound implies return and an empty own FIFO.

Return frames include full old-value RAX, callee-saved registers, original
caller continuation, the eight-byte stack pop, clear DF, current loans/handles
and successful collection. World metadata and permissions remain stable;
published bytes outside the selected qword remain equal. Foreign RMW events
are excluded, including zero-valued ones. The generic bound 67 is conservative;
the concrete GCC and Clang paths retire four and three own instructions.
Neither count is an operation minimum or a scheduling-fairness result.

`FetchAddBatch64.checked_claim` composes these proofs. The frozen claims each
specialize that one theorem with a static check of the entire function image.

## Useful loaded executions

Each typed certificate also supplies an actual resource witness at its checked
ELF address. `FetchAddResources` retains every cell of the complete installed
image, then uses checked allocation, store, protection, borrow, atomic-handle
and worker-attachment operations with their preservation proofs. A proved
extensionally equal address-space representation speeds reduction without
discarding the rest of the installed image.

Setup accepts arbitrary initial words and both input words. The certificate's
useful witness selects two nonzero inputs, a shared live counter and distinct
private aligned original caller slots. Its actual completed schedule contains
`RMW(thread 0) < RMW(thread 1) < RET(thread 0)` on that counter. The universal
contract applies to this same overlapping execution; a separate serial
completion cannot replace it. A finite witness establishes nonvacuity, while
the reusable Claim proves arbitrary admitted inputs and successful schedules.

## Validation and limits

`tests/CorpusFetchAdd64.lean` executes the real gated scheduler and checks
independently specified high-half carry, wraparound, old-word returns, reverse
RMW order, caller frames and collection. Negative cases reject duplicate IDs,
missing RET, upper-half argument mismatches, a changed final code byte, set DF,
the peer caller slot as RSP and an interior entry PC.

`lake build ManagedFetchAdd64Tests` caches shared proof dependencies through
Lake's input traces. The maintained certificate gate independently requires
both fixed typed concurrent certificate inhabitants, checks report identities
against the frozen ELF inventory, rejects altered files/reports and freshly
replays the production proof closure. Cached elaboration output alone supplies
no fresh-replay claim.

The model assumes coherent scalar WB RAM, suitable physical backing and
aliases, stable translation/permissions, no asynchronous external resource
mutation and all accesses through the represented managed resources. Actor
labels are modeled principals, not authenticated native OS owners. Empty own
FIFOs follow from these bodies; this is not a proof for arbitrary pending
stores, thread creation/join, SIMD state or external peers. Published x86-TSO
refinement, physical LOCK behavior, GNU source memory orders, Linux enforcement,
fairness and hardware lower bounds remain separate obligations.
