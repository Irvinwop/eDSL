# Callable DATA8 and private-stack effects

`EDSL.CallMemory64` proves a callable result with two separately owned mutable
regions: a private stack allocation and one ordinary eight-byte DATA operand.
The independent contract requires `*pointer = input`, full64
`RAX = (input + 1) mod 2^64`, the original caller return, RSP+8, and the usual
callee-saved registers and nonarithmetic flags. Every byte outside the union
of those two regions and every memory permission remains unchanged.

This is a verification library with concrete compiler clients. The existing
`edsl-grade` and `edsl-grade-call-stack` task propositions retain their scope.
This extension does not add a DATA8 task to either executable.

## Current resources and actual execution

`OS.CallMemory64.Descriptor` holds the existing private-stack descriptor plus
a separate DATA ticket and target address. Its `Contract` requires the actual
current stack contract, `WordResources64.WordValid` for the whole target,
an unborrowed target allocation and distinct live allocation identifiers.
Well-formed allocation separation derives disjointness. `Current` couples the
complete CPU memory to that same current borrowing world.

`CallMemory64.ResourcePre` binds RDI to the target, RSI to the full64 scalar,
RSP to the original caller slot and RIP to the selected code entry. It requires
at least sixteen private bytes and external RSP mod 16 = 8. Initial target
contents, other GPRs and modeled flags remain arbitrary. Admission assumes no
decoding, future store, successful execution, result, count or read order.

The sibling CPU relation checks actual decoding, execution, the frozen return
boundary and current read authority at every step. CALL/PUSH write effects
retain their stack classification. Ordinary DATA8 stores use a real checked
mutation through the DATA ticket. DATA8 reads use an actual owner observation
of the current world, without manufacturing a read loan. All writes and reads
thread one evolving `Borrowing.State` and full RAM coupling.

The new `CoveredExecution` retains complete actual instruction footprints,
including internal and terminal RET, using the existing `CallStack.FetchWithin`.
It cannot be replaced by the older private-only history: a DATA store requires
the union frame. Every actual preterminal prefix has a coupled current world;
the concrete run and endpoint follow from the same covered execution.

`CallMemory64.SemanticClaim` quantifies over every admitted world and AF choice
stream. `Claim` additionally requires a useful admitted state in which both the
target and RAX need to change. Unsupported code still has useful admissions.
`Returned` retains the actual endpoint, mixed history, metadata and functional
postcondition. Its `target_read` derives the stored input through the same
current owner handle after the function returns.

The generic `StackFrame.Contract.transport` preserves stack authority through
checked histories retaining allocation metadata, permissions and live loans.
This permits external DATA writes while retaining code and caller-slot loans.
Mixed preservation also retains allocation/frontier/loan/next-loan metadata,
all permissions and all cells outside the union. Both owner capabilities remain
usable after either kind of write.

## Reachable domain and compiler clients

`CallMemory64.Domain` starts from the existing checked stack domain, allocates
the DATA qword at address 262144 and initializes it through a checked store.
The actual next-frontier ticket is identifier 5 after private-stack ticket 4.
The construction preserves existing allocations and every original live loan.
It admits every nonempty code window up to 4096 bytes, every in-bounds entry,
every full64 scalar and old target word, and arbitrary other registers/flags.
It establishes present resources without establishing execution.

Two separate-translation-unit GNU23 compiler outputs meet the same task:

| Client | Complete text bytes | Entry | Helper | Instructions |
| --- | ---: | ---: | ---: | ---: |
| GCC 13 | 18 | 0 | 11 | 8 |
| Clang 18 | 18 | 0 | 11 | 8 |

The helper stores RSI through RDI, reloads the target into RAX and returns.
The caller increments that result and returns. GCC POPs old RAX into RDX before
INC; Clang INCs before POP into RCX. Actual checked stack writes retain the
internal return word while the separately owned DATA word changes.

The public client namespace is `EDSL.CallMemory64.Client`, with closed
`gccSeparate` and `clangSeparate` claims in
`tests.fixtures.CallMemory64.Covered`. The shared prefix proves the actual
PUSH, CALL, DATA store, current reload and internal RET. Compiler accounting
separately proves eight instructions and the exact DATA/stack read list.
Those descriptions do not constrain task acceptance and are not minimum-cost
or timing results.

Direct proof checks use the pinned Lean installation:

```sh
lake build EDSL tests.fixtures.CallMemory64.Covered tests.fixtures.CallMemory64.Audit
lake env lean -DwarningAsError=true tests/CallMemory64Resources.lean
lake env lean -DwarningAsError=true tests/CallMemory64Domain.lean
lake env lean -DwarningAsError=true tests/CallMemory64CPU.lean
lake env lean -DwarningAsError=true tests/CallMemory64Contract.lean
```

On Linux x86-64, the reproducible compiler/native/formal gate is:

```sh
bash scripts/verify-call-memory64.sh
```

It rebuilds both complete linked texts, checks the actual entry/helper bindings
and absence of final relocations, then runs two independently compiled native
observers. Every-byte mutations, truncation, extension and cross-profile inputs
must reject before observation. The formal phase instantiates both closed
claims on decimal literals extracted from those fresh files, audits theorem
dependencies and replays the generated module and its imports in a fresh kernel.
It does not translate finite native observations into universal proofs.

`CALL_MEMORY64_EVIDENCE_ROOT` selects the archive directory; the default is
`.cache/call-memory64-native`. Complete pages and observations stay in that
archive. CI retains compact receipts and source provenance. Explicit
`--native-only` skips formal checks and reports `formal=NOTRUN`. Failed,
unsupported or incomplete gates establish no security defect.

## Native boundary and target limits

The owned native observer authenticates both complete compiler texts against
bounded embedded slots before any probe. Input files remain data. It uses
separate guarded RW/NX stack and DATA pages, installs the original return slot,
and captures all sixteen GPRs and requested/effective flags. Its independent
base-256 oracle checks the wrapping result. Full page snapshots check the target
and RAM outside the union; owned negatives exercise missing stores, stale
reloads, mapped out-of-target writes and callee-saved damage.

Native entry is a controlled JMP with a preinstalled original return word.
Internal CALL and both RETs execute on RAM. Target positions include unaligned
ordinary-RAM accesses and the last complete qword in a page. These are exact
machine-code observations, without a C source-semantics claim for those inputs.
Page and mapping checks observe endpoints, not a hardware access trace.

The physical target requires canonical ordinary x86-64 RAM, AC/CET disabled and
no asynchronous interference. Available shadow-stack status is recorded;
an unavailable status interface does not establish CET support or disablement.
The library covers ordinary DATA8 at its owned target and private stack effects.
DATA4, atomics, MMIO, syscalls, concurrent call profiles, general interprocedural
automation and kernel/source refinement remain outside this slice. The formal
compiler claims bind whole extracted machine-code windows and selected entries;
ELF containers remain build provenance rather than a new fixed-task ELF grader.
