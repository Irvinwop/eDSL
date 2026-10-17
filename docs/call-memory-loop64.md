# Counted helper calls with DATA8 and a private stack

`EDSL.CallMemoryLoop64` proves two complete compiler outputs that repeatedly
call a store/reload helper while preserving saved registers in mutable stack
RAM. Both meet one independent mathematical contract for every full64 value
`x` and count `n`, including zero and `2^64-1`, every old DATA word and every
undefined-AF choice stream:

| Output | Required result |
| --- | --- |
| RAX | `(x + n) mod 2^64` |
| DATA8, `n = 0` | The actual initial target word |
| DATA8, `n > 0` | `(x + n - 1) mod 2^64` |

The original caller RET, RSP+8, callee-saved registers and nonarithmetic flags
are preserved. Every RAM byte outside the union of the **provided private
allocation and DATA8** is unchanged, as are all permissions, allocation and
loan metadata. Both owner capabilities remain current and usable. Private
contents may change; the frame is the provided allocation, including any
capacity beyond the bytes these clients use.

Both universal compiler claims have successful pinned Lean 4.35.0 builds with
warnings as errors. Their audited theorem dependencies use only `propext`,
`Classical.choice` and `Quot.sound`. The default combined gate requires fresh
compiler-byte binding, native observations, dependency audits, fresh kernel
replay and a complete source/provenance snapshot.

## Present resources and stack high-water mark

`ResourcePre` extends the [callable DATA8 admission](call-memory64.md): RDI is
the target, RSI is `x`, RDX is `n`, RSP is the original caller slot `S`, and RIP
is the selected code entry. External RSP mod 16 is eight. The current borrowing
world supplies code/caller-slot loans, distinct unborrowed private and DATA
allocations, whole-qword permissions and complete CPU/RAM coupling. Other
registers, modeled flags and initial DATA contents remain arbitrary.

Admission explicitly requires at least **32 private bytes**, including for
zero count. Three PUSHes use `S-8`, `S-16` and `S-24`; the helper CALL reaches
`S-32`. This is a present capacity requirement. Admission assumes no future
execution, decoded loop shape, CALL, count bound, fuel, result or read order.
`Claim` adds a useful nonvacuity witness requiring both outputs to change;
that witness does not restrict the universal input domain.

The checked `CallStack.CapacityDomain` supports every positive capacity up to
4096 bytes. `CallMemory64.CapacityDomain.resource_pre` additionally requires
at least 16 bytes; this counted contract requires 32. The counted `Domain`
specializes actual allocation and initialization to 32 bytes with original
top 65544, private region `[65512,65544)` and DATA target 262144. Private ticket
4 is issued first, then DATA ticket 5; initialization stores the arbitrary old
word through checked ownership. All original allocations and live loans survive.
Generic stack-contract transport frames the current code and caller loans
through the allocation and initialization history.

`Domain.resource_pre` admits every nonempty code window up to 4096 bytes and
every in-bounds entry, independently of decoding, with arbitrary full64
value/count/old word and arbitrary other registers and flags. Unsupported bytes
have admissions too. The compiler theorems quantify over **arbitrary current
admitted resources and CPU states**, beyond this concrete allocation witness.

## Complete compiler texts and execution proofs

The GNU23 caller and helper are separate translation units, using the same
`-Os`, `-fno-lto`, `-fno-optimize-sibling-calls` and remaining compiler/linker
flags as the earlier callable DATA8 fixture, without tuning. The complete
linked text retains the helper after the caller's RET.

| Client | Text bytes | Entry offset | Helper offset | Exact modeled instructions, `N = n.toNat` |
| --- | ---: | ---: | ---: | --- |
| GCC 13 | 45 | 0 | 38 | `12 + 10*N` |
| Clang 18 | 52 | 0 | 45 | `4` if zero; otherwise `12 + 9*N` |

GCC saves incoming RBP/RBX and pushes padding RCX. Each iteration decrements
the remaining count, performs an actual CALL, checked DATA store, current
reload and internal RET, then updates the accumulator. The exit observes the
padding word and restores the saved registers with actual POPs. Clang returns
in four instructions for zero; otherwise it saves R14/RBX, pushes padding RAX,
runs its helper loop, discards padding with `ADD RSP,8` and POPs the saved words.

The public claims are `EDSL.CallMemoryLoop64.GCC.claim` and
`EDSL.CallMemoryLoop64.Clang.claim`, imported from
`tests.fixtures.CallMemoryLoop64.GCC` and
`tests.fixtures.CallMemoryLoop64.Clang`. Their `covered` and `evaluated`
theorems construct actual mixed CPU/OS executions from per-instruction steps
and induction on the natural remaining count. Every instruction has checked
decoding and complete fetch coverage. Each join uses the actual evolved world
and AF stream offset; the original `descriptor.frame.top` stays frozen across
all internal returns.

The same `CoveredExecution` supplies every current prefix world, the actual
evaluator result, mixed mutation history and union/permission/metadata frame.
`Returned.target_read_zero` and `Returned.target_read_nonzero` derive endpoint
readback through the same current DATA owner ticket, without a new read loan.
Termination covers maximum full64 counts by proof, without enumerating them.
The instruction formulas above are separate consequences of execution; they
constrain neither admission nor acceptance and establish no minimum-operation,
cycle or micro-op result.

Saved-word preservation is available in `EDSL.OS.CallMemory64.Private`.
`History.Excludes` requires every other private write to be disjoint from the
**whole protected qword**; different starting addresses are insufficient.
DATA writes preserve private words by current allocation separation. These
facts retain the actual saved register and CALL words through checked mixed
histories, with no assumption that private RAM is immutable. The original
caller slot retains its separate read-loan protection.

The generic `OS.CallMemory64.Cutpoints.Certificate` is also implemented, with
local actual-step obligations, current worlds, static segment depths and a
decreasing natural rank. Its checked client uses the existing inline
store/LEA/RET program to prove the independent DATA/result/ABI contract and
prefix composition. The two new compiler proofs use covered histories and
direct remaining-count induction; they do not instantiate that certificate.

## Reproduction and evidence boundaries

On Linux x86-64, the default integration interface requires both formal and
native phases:

```sh
bash scripts/verify-call-memory-loop64.sh
```

Explicit native-only mode skips the universal proof phase and reports
`formal=NOTRUN`:

```sh
bash scripts/verify-call-memory-loop64.sh --native-only
```

The formal helper accepts a fresh output directory and both complete raw
extractions. It owns `/tmp/edsl-lean-build.lock`; invoke it without an outer
Lean lock:

```sh
bash scripts/check-call-memory-loop64-proofs.sh OUTPUT GCC_TEXT CLANG_TEXT
```

It embeds decimal byte literals from those files, checks their binding to both
closed claims, derives execution for arbitrary current resources and the
reachable domain, audits dependencies and replays the generated module and
imports in a fresh kernel. Full ELF files provide compile/link/entry/extraction
provenance here. This milestone adds no full-ELF artifact `Claim`, grader task
or CLI; existing grader propositions, limits and foundational imports retain
their scope. The combined gate joins these phases with a complete source
snapshot and provenance; individual proof builds and a native-only report
provide separate evidence for their respective phases.

Two independent GCC 13/Clang 18 observer builds authenticate both complete input
files and both end-bounded embedded 45/52-byte slots before output admission or
execution. The input files remain data. The bounded matrix uses counts
`0,1,2,3,7,31,257,1024`, eight edge values and 128 effective flag profiles per
observer. An independent base-256 addition oracle checks the result and final
DATA, without replaying the counted helper. The model proofs cover all counts.

Native RSP starts at stack-page+40: private32 is `[page+8,page+40)` and the
original caller slot is `[page+40,page+48)`. Records retain all sixteen pre/post
GPRs and flags, requested/effective entry flags and complete pre/post guarded
stack and DATA pages. Checks cover the original return word, ABI, endpoint
mapping permissions and every observed page byte outside the union. Owned
synthetic mutants exercise skipped iterations, missing stores, stale reloads,
outside-DATA writes and callee-saved damage. Extraction and embedded-slot
mutations must reject before observation. Native-only evidence reports
`formal=NOTRUN`; no native inline or closed-form client is claimed.

## Target assumptions and limits

This slice models sequential ordinary RAM with four-level canonical x86-64
addresses. Physical interpretation requires valid control state, AC/CET
disabled and no asynchronous interference. An unavailable shadow-stack status
query does not establish CET disablement. Unaligned native DATA cases concern
the exact binary and establish no C source-validity result. Page snapshots and
mapping observations concern endpoints, without a hardware access-order trace.

Source/IR preservation, full OS/kernel or physical CPU conformance, concurrency,
atomics, syscalls, recursion and indirect calls remain outside this slice.
Unsupported code, proof failure, timeout or an incomplete gate establishes no
security defect. Native negatives are project-owned synthetic fixtures.
