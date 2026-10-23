# Compiler corpus and reusable verification

The scaling target is independent programs proved against independent contracts.
Adding another hand-written theorem for a nearby instruction encoding does not
measure that target. Frozen corpus v1 provides 40 distinct project-owned C
functions and 80 final-ELF function windows, produced by two ordinary `-O2`
compiler profiles. It includes strings, arrays, arithmetic, loops, struct copies,
atomics, spinlocks, a Linux futex wait loop, and a two-thread counter worker.
The functions are representative compiled algorithms, not claims to reproduce
all behavior of an upstream libc or kernel implementation.

The initial metric is **0/40 functions certified end-to-end**, **0/80 compiler
artifacts certified end-to-end**, and **0 concurrent contracts proved**. The
existing repository's certificates for different fixed routines do not certify
these exact final ELF images. Native checks, compiler success, byte extraction,
CFG discovery, an SMT solver result, and a timeout are each separate evidence.
None by itself increases certification coverage or establishes a security bug.

At the signed-clamp milestone,
[named scalar certificates](corpus-scalar-certificates.md) covered
**4/40 functions and 8/80 compiler artifacts**: `c_min_u64`, `c_max_u64`,
`c_add_mod64` and `c_clamp_i32` for both frozen compiler profiles.
The [scalar report](../corpus/measurements/scalar-clamp32-v1/)
is separate from the immutable initial reports. These are conditional callable
machine proofs with actual-address modeled OS resources and the recorded
CET/IBT-disabled target, not native Linux startup or physical CPU refinement.
The [concurrent fetch-add certificates](concurrent-fetch-add-certificates.md)
added `c_atomic_fetch_add64` for both profiles, bringing conditional coverage to
**5/40 functions, 10/80 artifacts and one concurrent function**. Its fixed
`managed-tso64-closed-batch-v1` contract covers actual interleavings, exact
histories, ABI/resource frames and progress. Physical/published x86-TSO and
GNU source-order refinement remain separate obligations.
The [concurrent measurement](../corpus/measurements/managed-fetch-add64-v1/)
retains the preceding scalar reports as history.

The [bounded byte-scan milestone](bounded-byte-scans.md) implements both
unchanged row-18 `c_strnlen_bytes` windows: GCC 35 bytes and Clang 34 bytes.
Its fixed first-NUL task, shared sparse-cutpoint VCG and useful complete-image
resource witnesses are composed in typed final-ELF certificates. At that milestone the
conditional totals reached **6/40 functions and 12/80 artifacts**, with one
distinct concurrent function. The
[bounded-scan measurement](../corpus/measurements/bounded-byte-scans-v1/)
records the passed full-project/corpus gate and actual fresh aggregate replay.
The [first-match search milestone](first-match-searches.md) adds both frozen
`c_memchr_index` and `c_linear_search_u32` outputs through two width-parametric
compiler-layout proofs. The byte and u32
tasks return the earliest matching index or full64 SIZE_MAX, with arbitrary
key upper bits and no DATA access on empty input.
The [paired byte-comparison milestone](paired-byte-comparison.md) adds both
unchanged `c_memcmp_bytes` outputs using shared paired snapshots, unsigned
lexicographic mathematics and signed low32 return semantics. At that milestone,
coverage reached **9/40 functions and 18/80 artifacts**, with one distinct concurrent
function. Empty calls ignore both pointers and input-loan selectors; compatible
read-only aliases remain admitted.
The [absolute-value and byte-reversal milestone](unary-functions.md) adds both
unchanged `c_abs_i32` and `c_byteswap64` outputs, bringing conditional
coverage at that milestone to **11/40 functions and 22/80 artifacts**, with one
distinct concurrent function. Shared NEG32/BSWAP64 semantics, independent word mathematics and compact
generated-WP proofs reuse the scalar/resource/final-file path. The
[unary measurement](../corpus/measurements/unary-registers-v1/) records the
passed full-project gate, fresh replay and actual default-limit packet grading.
No historical diagnostic or frozen compiler input is replaced.

The [full64 popcount milestone](popcount.md) adds both unchanged row-11
`c_popcount_loop` outputs, bringing conditional coverage at that milestone to
**12/40 functions and 24/80 artifacts**, with one distinct concurrent function.
Independent cardinality, shared sparse scalar proofs and current-resource
composition cover all Word64 inputs. The
[popcount measurement](../corpus/measurements/popcount-v1/) is a new immutable
record; every earlier measurement retains its historical score and evidence.

The [unsigned-average milestone](unsigned-average.md) adds both unchanged
row-08 `c_average_u64` outputs. The final aggregate gate and fresh replay passed;
conditional coverage at that milestone reached **13/40 functions and 26/80 artifacts**,
including one concurrent function. The
[average measurement](../corpus/measurements/unsigned-average-v1/) retains the
preceding reports as history. Every
full64 argument pair is admitted; the contract uses the floor of the unbounded
natural sum, including machine-word overflow. Shared SHR semantics, mathematical
identities and the existing scalar VCG/resource/final-file path supply the
proof.

The [parity](parity.md) and [rotation](rotate.md) milestones add both unchanged
row-12 `c_parity_loop` and row-09 `c_rotl64` outputs. The combined
full-project/corpus gate and fresh kernel replay passed locally. Conditional
coverage at that milestone was **15/40 functions and 30/80 artifacts**, including
one distinct concurrent function; **25 functions / 50 artifacts** remained.
The
[parity and rotation measurement](../corpus/measurements/parity-rotation-v1/)
retains these historical results.

The [byte-equality milestone](byte-equality.md) certifies both unchanged row-20
`c_bytes_equal` outputs against independent complete-list equality: low8 RAX is
exactly 0/1, with upper56 unconstrained. Shared paired snapshots and original
input loans compose through [read-only call transport](read-only-call-transport.md)
with universal body proofs and complete-file binding, without resetting RAM or
inputs. GCC's 46-byte window uses the default 64-byte cap; Clang's complete
68-byte window requires the explicit [128-byte profile](cfg-profiles.md), both
with a 32-node cap. The default path rejects the entire Clang window.
The full-project/corpus certificate gate and external fresh replay passed on
source `383d1f1ef928f551b89a8424ae46c8bb019ce2e2`. At that milestone, validated
conditional coverage was **16/40 functions and 32/80 artifacts**, including
**one distinct concurrent function**; **24 functions / 48 artifacts** remained.
The byte-equality
[measurement](../corpus/measurements/byte-equality-v1/) records these scopes.
See [commit-specific CI results in GitHub Actions](https://github.com/Irvinwop/eDieSeL/actions).
Earlier measurements retain their counts and evidence.

The [managed plain64 milestone](managed-plain-methods.md) adds both unchanged
row-35 `c_atomic_load_acquire64` and row-36 `c_atomic_store_release64` outputs.
One checked method family supplies the independent universal Claim, current
resources and progress for both compilers. Whole-image high-word homogeneous
witnesses place both accesses before either return; a same-file mixed run retains
`writer RET < publication < reader access` and the actual selected-writer RF edge
in that same closed history. The
[measurement](../corpus/measurements/managed-plain64-v1/) records the accepted
source and full-gate evidence. At that milestone, conditional coverage was **18/40 functions and
36/80 artifacts**, including **three distinct concurrent functions**;
**22 functions / 44 artifacts** remained. Fetch-add retains
`managed-tso64-closed-batch-v1`; plain load/store use
`managed-tso64-plain64-cohort-v1`. Acquire/release are declared interface
annotations; closed legal histories require initialized resources and empty
initial and final queues.

The [multiplication milestone](../corpus/measurements/multiply-modulo64-v1/)
adds both unchanged `c_mul_mod64` outputs. The shared vector VCG, resource
and named-ELF adapters establish the full64 natural product modulo 2^64 for
all independent flag streams. At that milestone, conditional coverage was
**19/40 functions and 38/80 artifacts**, including **three distinct concurrent
functions**; **21 functions / 42 artifacts** remained.

The [signed signum milestone](../corpus/measurements/signed-signum32-v1/) adds
both unchanged `c_sign_i32` outputs. Shared low32 shift/order algebra, the vector
VCG and named-ELF/current-resource adapters establish the independent signed
result for every low32 input, including INT32_MIN, arbitrary incoming upper
RDI bits and all flag streams. Conditional coverage is **20/40 functions and
40/80 artifacts**, including **three distinct concurrent functions**;
**20 functions / 40 artifacts** remain. Both bodies retire seven modeled
instructions and read only the original eight-byte return slot. The
[measurement](../corpus/measurements/signed-signum32-v1/) records the accepted
source, full corpus gate, stored assertions and exact packet controls.

## What is frozen

`corpus/v1/specifications.tsv` is the ordered 40-function definition. Each row
has a stable id, exact symbol, instruction/OS family, an independent behavioral
contract, and the relevant environmental/ownership obligations. Definitions,
source, options, compiler identities, and machine bytes are frozen together.
Changing them requires a new corpus version; failures do not justify changing
an input to improve a coverage score.
`corpus/v1/contracts.md` supplies the common ABI, frame, pointer, lifetime, and
conditional synchronization obligations and is included in the source seal.

The GCC and Clang profiles use GNU C23 spelling `-std=gnu2x`, `-O2`, baseline
`-march=x86-64 -mtune=generic`, and a non-PIE Linux x86-64 executable. GNU++26,
LLVM IR input, other architectures, dynamic code, and a complete Linux process
loader are later corpus expansions. `noinline` keeps each named candidate
available for extraction. Builtin recognition, vectorization, loop transforms,
conditional moves, tail calls, and external libc calls remain enabled. Compiler
provenance includes the exact executable hashes, versions, target triples,
linker identity/hash, commands, libc version, and Lean pin. Executables also
include the independently written native contract harness, compiled separately;
the exact corpus object is linked into that executable without recompilation.

`corpus/v1/{gcc,clang}/final.elf` contains the exact final linked images. The
adjacent JSON manifests contain each selected function's bytes, virtual address,
file offset, and size. Source and artifact SHA-256 files bind those inputs.
The full ELF matters: a PC-relative call or load can leave the selected symbol
window, and its target cannot be justified by a raw byte span alone. System
libraries and the actual kernel remain explicit environment dependencies.

The bounded Lean tool `corpus/Extract.lean` accepts little-endian x86-64 ET_EXEC
images, locates one unique global defined STT_FUNC per selected symbol, and
checks the selected PROGBITS section against one readable executable PT_LOAD.
Both mappings must identify the same file-backed byte interval. It rejects
truncation, malformed tables, unsupported containers, missing/duplicate symbols,
zero-size symbols, and ambiguous or inconsistent code mappings. Tooling limits
are 4 MiB per file, 1024 sections, 128 program headers, 65536 symbols, and 65536
bytes per selected function. These are extraction limits, not ISA semantics.
It does not use `objcopy`, disassembly text, or symbol names as proof authority.
It is executable Lean tooling with no proved extraction-soundness theorem;
a later certificate must kernel-check its literal full-ELF/code binding.
The repository's existing proved restricted ELF loader is a separate API, and
normal dynamically linked corpus images do not automatically satisfy it.
This extraction profile also requires low-canonical page-congruent PT_LOAD
segments with disjoint rounded 4096-byte page extents. Competing writable or
partial mappings cannot be ignored merely because one executable segment covers
the selected symbol. This conservative profile is not a general Linux loader.

## Reproduction and native evidence

Run `bash scripts/verify-corpus-v1.sh --frozen` from the repository root to check
hashes, re-extract every window with pinned Lean, compare manifests, execute the
frozen native harnesses, and reject independently malformed ELF headers,
missing/duplicated function symbols, and nonexecutable program mappings.
The host must be Linux x86-64 with a compatible glibc and futex/pthread support.
Run `--rebuild` to additionally require the recorded compiler provenance and
byte-identical regenerated final ELF images. The script records logs, extracted
raw windows, disassembly, coverage, exit status, and SHA-256 receipts under
ignored `artifacts/compiler-corpus-v1/`. It does not overwrite frozen v1.
The builder snapshots every declared source, specification, common contract,
and tool input before compilation, checks that snapshot against its initial
digest, builds both compilers from that one copy, and requires the live inputs
to retain that digest at completion. A freeze publishes its staged compiler
artifacts only after both profiles, diagnostics and negative cases succeed;
the checksum seal is moved last. An interruption before that seal is not a
completed freeze. Retain the ignored staged run for diagnosis and remove only
an unsealed partial publication before retrying; never overwrite a sealed v1.

`corpus/Probe.lean` separately runs the existing production read-only CFG
discovery/checker on every extracted window and records the first actual
blocking obligation for each artifact. The frozen `baseline-cfg.json` files
record the initial coverage; fresh reports use current checker sources, whose
hashes are included in each run. A CFG-accepted row still counts as uncertified.
This diagnostic makes corpus failures available to select the next ISA/OS
extension without changing compiler output or the target contract.
The actual initial checker accepts **0/40 GCC** and **4/40 Clang** CFGs. The four
Clang candidates are `min_u64`, `max_u64`, `add_mod64`, and the acquire load.
GCC's first blocker is its default `ENDBR64` on 37 candidates and the 64-byte
span limit on three. These counts concern the initial CFG discovery only;
certification was **0/40 functions and 0/80 artifacts** at that freeze.

The later [comparison/padding measurement](../corpus/measurements/cmp32-endbr-nop-v1/)
accepts **5/40 GCC** and **4/40 Clang** CFGs under the explicit CET/IBT-disabled
target, while retaining every frozen byte and compiler option. Its reports
record the remaining first blockers. CFG acceptance itself establishes no
end-to-end certificate; the named comparison family supplies separate evidence.

The native harness checks independent algebraic contracts, memory frames,
boundaries, actual two-thread shared-counter and spinlock use, and futex
wait/wake behavior with timeouts. They can expose synthetic regressions in
these project-owned fixtures. They do not prove universal correctness,
linearizability, absence of races, fairness, or correspondence to physical CPUs.
No real security findings or their metadata belong in public corpus files.

## Checker integration

A reusable checker consumes the frozen full ELF, symbol address and extent,
literal bytes, and a contract identifier. It must obtain code binding from a
kernel-checked theorem over the final image and the modeled loaded memory.
This extraction CLI is an untrusted producer of that data. The checker then
uses one fixed decoded-ISA semantics and one proved-sound symbolic execution or
VC rule set. Per-input obligations describe independent mathematical behavior,
ABI frames, memory permissions/ownership, and environmental actions. A decoded
CFG and discharged arithmetic obligations alone do not discharge OS contracts.

An initial integration can reuse `EDSL.X86.Sequential.CFG` and its actual
semantics transport. Its current 64-byte / 32-static-instruction read-only
profile must remain visible in coverage reports. The
[reusable VC generator](reusable-checker.md) supplies checked bounded execution
and sparse-cutpoint proofs over that machine. Its generic soundness theorems
and examples do not themselves certify a frozen ELF function.
A larger loop, a load width, a compiler-generated external call, SIMD, or a
syscall not modeled by that API is reported as unsupported with its first
blocking obligation. Preserve ordinary optimized output when choosing the next
extension. Do not lower an operation to a weaker contract to count it.
For example, this Ubuntu GCC profile emits `ENDBR64` by default. Retain it;
the sequential decoder supports its exact encoding under the explicit
CET/IBT-disabled target. CET-enabled behavior remains outside that profile.

A machine-readable certificate receipt should identify:

- Corpus version, compiler profile, symbol, full-ELF SHA-256, exact entry and span.
- Independent contract id/version and explicit environmental assumptions.
- Checked byte-binding theorem, checker soundness theorem, proof module/declaration.
- Kernel/replay and theorem-dependency audit receipt hashes.
- Sequential/concurrent scope and any cost/progress claim proved separately.

Until such evidence exists for a row, it remains `unverified`. Certification of
one compiler's output counts one of 80 artifacts. The primary 40-function score
requires both frozen compiler profiles, so a single easy encoding cannot hide
a missing compiler path. Report both denominators on every milestone. Cost
proofs must state a model (retired instructions, memory events, abstract steps,
etc.); they do not establish physical timing or a minimum possible algorithm.

## Concurrency is an independent acceptance gate

`c_atomic_fetch_add64`, `c_counter_worker`, and the native two-thread workload
force concurrency into the corpus. The final-value arithmetic of one
uninterrupted call is insufficient. Acceptance needs a legal interleaved
machine execution with two disjoint thread contexts and a live shared atomic
cell, one linearization event per RMW, correspondence to a sequential history,
and an explicit x86-TSO refinement or accurately stated narrower memory model.
It must preserve shared ownership/lifetime through completion and join.
An existing or new theorem for 32-bit `LOCK XADD` does not certify these frozen
64-bit artifacts. The width, decoded instruction, exact bytes, and OS-resource
contracts must match; a synthetic 32-bit stress witness remains separate.

The [fetch-add certificates](concurrent-fetch-add-certificates.md) compose the
shared full64 instruction checker, actual-address resources, overlapping calls,
independent histories and bounded own progress for both frozen outputs. The
[plain load/store certificates](managed-plain-methods.md) similarly compose one
checked method family with the independent universal Claim, complete loaded-image
resources and homogeneous/mixed execution witnesses. Each CLI plain row projects
from its compiler's same-file cohort certificate, retaining every original gate.
File/symbol identity or graph checking alone supplies no corpus credit.

The spinlock additionally transfers an invariant with acquire/release ordering;
its liveness needs scheduling assumptions. The futex loop additionally needs
the Linux syscall ABI, errno/TLS/external-call contracts, wait/wake queues,
EINTR/EAGAIN and spurious-wakeup behavior, rechecking after wakes, and process
address-space/lifetime obligations. Source release/acquire labels do not prove
these low-level facts. A whole Linux distribution or operating system remains
far beyond this corpus and is not claimed to be safe.

## Common contract obligations

Every row's eventual machine contract must include the SysV x86-64 call entry:
a live readable return continuation, aligned stack, preserved callee-saved
registers, and separately authorized private scratch/stack effects. An outside
memory frame refers to caller-observable memory after return; it does not
forbid authorized stack spills. Pointer-bearing rows additionally need live
allocations, valid pointer provenance for the source-level contract, and
nonwrapping byte extents (including element-size multiplication). For n=0 no
object byte may be read or written; the chosen source and machine contract must
still state whether null/one-past pointers are admitted. Overlap is allowed only
where the row permits it. Compiler-generated widened reads, vector stores,
external calls, errno/TLS, and process resources add actual machine obligations.

Acquire/release labels alone do not create an inter-thread synchronization
edge. The matching reads-from/release-sequence conditions must hold. An acquire
load may legally read an initial or relaxed value without synchronizing with a
release. The managed plain64 contract constructs legal closed histories and
retains the selected release writer for its mixed acquiring reader. Its interface
annotations are declared, and closed histories require initialized resources and
empty initial and final queues. Source-to-interface and compiler-ordering
preservation, physical x86-TSO and native Linux correspondence remain separate
obligations.

The native futex checks cover predicate mismatch and positive kernel wake,
recheck, and requeue observations. They do not deliberately exercise EINTR,
deterministically witness EAGAIN, or validate an unretried kernel error. A
negative returned errno can be an environmental failure; it is not itself a
program defect. Native process timeouts are bounded independently of Lean
builds and lock waits; the script claims no overall 30-second verifier bound.
