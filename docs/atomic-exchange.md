# Atomic exchange foundation

The `exchange32` function profile accepts exactly `89 f0 87 07 c3`:
`MOV EAX,ESI; XCHG DWORD PTR [RDI],EAX; RET`. The memory operand of this XCHG
encoding is implicitly locked. Its modeled effect returns the old 32-bit word
zero-extended into RAX and replaces that word with the low 32 RSI bits. Flags,
unrelated registers, permissions and bytes outside the four-byte footprint are
preserved. RSP advances by eight and RIP takes the readable canonical return
address. The whole function takes exactly three modeled user instructions.

`X86.AtomicEvent` records the address and actual before/after words.
`exchangeDWord` checks the entire operand before producing an updated memory;
`ExchangeTransition` exposes one indivisible RMW transition, with no observable
load/store intermediate state. `X86.step` returns a distinct `.atomic` result.
`step_atomic_sound` connects every such result to that memory transition and
the register/flags effects. `AtomicExecutes` retains the exact ordered event
list and proves its uniqueness along with result/count; ordinary instructions
contribute no events. Function and first-syscall
evaluators count atomic continuations, and their divergence relations include
infinite atomic continuations too.

`Examples.Compiler.Exchange.atomic_execution` proves exactly one exchange event
between the MOV and RET. `correct` adds ordinary execution, termination and
unique result/count; `value_and_frame` gives readback and framing. The raw and
complete-ELF certificate routes retain the singleton event theorem rather than
discarding it. Preconditions require supported operand addressing, accessible
writable bytes, executable code, an accessible return stack, canonical return
target, and data disjoint from code/return stack. Symbolic regressions exhibit
admitted states for every old 32-bit word and every 64-bit replacement argument.

## OS resources and histories

`OS.AtomicExchange.exchangeWord` operates on the current borrowing/resource
world. On well-formed states it checks current owner/ticket authority,
containment within one live allocation, absence of conflicting read loans,
OS permissions and the machine
atomic-operand profile. The pure guarded store supplies the authority check and
OS-cell updater; it is not an extra exposed execution step. A successful result
contains the updated world and old word read from the original current cells.
Failure exposes no partial updated state.

`exchangeWord_sound` proves that the projected OS cells implement the same
`ExchangeTransition`. `exchangeWord_guarded` and `exchangeWord_wellFormed`
preserve the existing resource discipline. Under `Borrowing.WellFormed`,
`exchangeWord_borrowed` rejects mutation while any read loan names that allocation,
including loans on a disjoint subregion. Read authority on other allocations
retains its cells and permissions.

`exchange32_updates_space` composes the successful resource operation with the
exact compiler bytes, retaining the projected final OS space, singleton atomic
event, three-instruction count, unique result and termination. Executable code,
disjoint data/stack footprints and the return contract remain explicit premises.

Labeled `Step` and same-cell `History` record owner, ticket, address and actual
before/after words. `History.chain` proves every returned old word equals the
preceding new word, starting from an independently observed initial value;
the final projected memory contains the last new value. This covers arbitrary
finite admitted exchange histories. `History.loan_stable` preserves surviving
read-loan cells by composition with the guarded borrowing history.

Principals/tickets remain logical labels. This API takes current-owner/ticket
authority directly; separate stored actor authorization is supplied by the
shared-handle layer. Same-cell histories contain exchange operations,
without thread start/join, ordinary intervening writes, resource transfers or
general machine-instruction schedules. The separate mutable-worker layer adds
that lifecycle over stored handles; the read-worker dispatcher retains its
original load/RET profile.

The [shared atomic-handle layer](atomic-handles.md) is now implemented over this
exclusive-owner primitive. It stores distinct actor handles, reserves their
allocation against ordinary changes, preserves surviving read loans elsewhere,
and permanently revokes closed IDs. Exchange-only schedules have value-chain
and multiset-conservation proofs. The [mutable-worker layer](atomic-workers.md)
now executes each actual MOV/XCHG/RET instruction against current shared cells,
retains observed old words privately through later join, and revokes the
worker's handle and two loans. Protected invariants, lock protocols and concrete
runtime refinement remain future obligations.

## Supported physical profile and remaining obligations

Operands must be naturally aligned four-byte ranges with canonical bytes,
no address wrap and no virtual 64-byte-line or 4-KiB-page crossing. These are
deliberately narrow support conditions. Other hardware XCHG forms are unsupported;
rejection does not assert that they are non-atomic or faulting.

Physical interpretation assumes ordinary coherent write-back RAM, stable
translation and permissions, compatible physical cache-line/page placement,
no unmanaged aliases or mixed-size overlapping accesses, and no device/DMA or
non-temporal interference. Code and return stack must remain stable. Existing
x86 userspace control-state assumptions also apply. The functional byte-store
primitive by itself still provides no atomicity guarantee.

The model interprets selected behavior from the [Intel SDM revision 093](https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html):
[volume 2D](https://cdrdv2.intel.com/v1/dl/getContent/671143), XCHG pp. 6-32–6-33;
[volume 1](https://cdrdv2.intel.com/v1/dl/getContent/671436), §3.4.1.1 for EAX zero extension;
and [volume 3A](https://cdrdv2.intel.com/v1/dl/getContent/671190), §§11.1.2.1–11.1.4 for locking.
Locked-instruction ordering and interactions with ordinary accesses
(§§11.2.3.8–11.2.3.9) are separate refinement obligations. The current proofs do
not establish a complete x86-TSO model, C/C++ sequential-consistency preservation,
acquire/release/relaxed semantics, fences, physical atomic conformance or kernel
implementation correctness. Compiling a source `seq_cst` exchange is provenance
for the bytes, not a source-semantics theorem.

## Reproduction and independent observations

```sh
lake build EDSL.All edsl-certify edsl-certify-process
lake env lean -DwarningAsError=true tests/AtomicExchange.lean
lake env lean -DwarningAsError=true tests/OSAtomicExchange.lean
bash scripts/check-audit.sh
bash scripts/verify-compilers.sh
lake exe edsl-certify exchange32 FUNCTION.bin artifacts/Exchange.lean
lake exe edsl-certify --elf exchange32 FUNCTION.elf artifacts/ELFExchange.lean
```

Owned C `_Atomic` and C++ `std::atomic` fixtures use sequentially consistent
exchange. Clang C/C++ and GCC C output receive raw/full-ELF certificates, compiler
provenance and hashes. The native driver independently checks old returns, new
little-endian bytes and guards, then runs eight pthread workers performing
100,000 exchanges each. Tokens initially occur exactly once across workers and
the shared cell; after join their multiset must still contain each token once.
This detects lost/duplicated exchanges under tested schedules. It neither
proves all native schedules nor validates pthreads/CPU conformance universally.
Lean regressions cover exact event labeling, widths, flags/framing, fuel and
unsupported/denied operands. All fixtures and negatives are project-owned.
