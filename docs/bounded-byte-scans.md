# Bounded byte scans

The bounded-scan implementation connects both unchanged frozen
`c_strnlen_bytes` functions to one independent first-NUL contract through the
shared read-only CFG and sparse-cutpoint VCG. It supplies typed final-ELF
certificates, universal body proofs and useful loaded resource witnesses.
At this milestone, conditional corpus coverage reached
**6/40 functions and 12/80 artifacts**;
the concurrent-function count remains one. The
[measurement](../corpus/measurements/bounded-byte-scans-v1/README.md) records the
full-project/corpus gate, actual fresh kernel replay and regression checks.

| Frozen compiler profile | Complete symbol | Entry | Extent |
| --- | --- | --- | ---: |
| GCC 13.3.0 | `c_strnlen_bytes` | `0x402f60` | 35 bytes |
| Clang 18.1.3 | `c_strnlen_bytes` | `0x4014a0` | 34 bytes |

The [frozen corpus](compiler-corpus.md), compiler options, final ELF images and
historical measurements are unchanged. GCC retains ENDBR64 and its padding;
Clang retains its complete nine-byte NOP. Neither function is replaced with a
more convenient compiler output.

## Independent contract

[`Grading.ByteScan.BoundedNulLength`](../EDSL/Grading/ByteScan.lean) relates an
initial byte list of length `n` to a result `r`: `r ≤ n`, every index before `r`
contains a nonzero byte, and the byte at `r` is zero when `r < n`. Thus it returns
the first NUL, or `n` if there is none. Existence and uniqueness include multiple
NULs, high-bit bytes and the empty list. No instruction shape, decoder result,
fuel or desired machine state defines this mathematics.

The fixed `BufferTask.firstBoundedNulLength` task binds full64 RDI to the buffer
base, full64 RSI to `n`, and full64 RAX to `r`. Its mathematical domain is
`n < 2^64`; current memory adds the readable, nonwrapping snapshot requirement.
There is no small-input bound. For `n = 0`, the result is zero and no DATA read
is allowed. The data pointer may be null, one-past, unaligned, unmapped or
noncanonical, and its unused data-loan identifier is never consulted. The
executable code and original caller return slot remain required.

[`BufferCall.Contract`](../EDSL/BufferCall/Contract.lean) generalizes this
admission to lists of byte snapshots and full64, low32 or low8 argument views.
Compatible read-only aliases are allowed, including overlapping snapshots.
Positive DATA reads must fit wholly inside one initial snapshot; readable
padding or an unrelated live loan supplies no extra authority. STACK8 refers
to the original caller slot, even if a candidate changes RSP.

## Shared proof and resource composition

[`VCGen.BufferCall`](../EDSL/X86/VCGen/BufferCall.lean) connects the production
cutpoint annotations to the fixed buffer-call contract.
[`VCGen.ByteScan`](../EDSL/X86/VCGen/ByteScan.lean) shares the nonzero-prefix,
current-byte-read, full-memory/ABI frame and nonwrapping increment lemmas.
[`ByteScanBodies`](../EDSL/Corpus/V1/ByteScanBodies.lean) then discharges the two
compiler layouts using only entry and byte-comparison-header cutpoints. Every
instruction in each complete CFG is authenticated, including unreachable GCC
padding. The loop rank is `n-i`, with entry rank `n+1`; generated finite blocks
reuse the existing decoder and executor rather than unrolling the input.

The resulting semantics proves actual total execution for **every AF choice
stream**, together with the independent result and every-prefix permitted-read
policy. AF choices describe the model's undefined-flag choices, not scheduling.
Annotations and ranks are proof evidence outside the present-only input
precondition. No future successful run or checker-success oracle is admitted.

The postcondition retains complete modeled RAM and its permissions, the
original return RIP, `RSP+8`, SysV callee-saved GPRs, and all nonarithmetic flag
bits. [`BufferCall.Resources`](../EDSL/BufferCall/Resources.lean) derives current
code, original caller and nonempty input-loan authority at every continuing
prefix and return. Its separate managed-history frame retains those snapshots
and permissions while the original loans survive; other allocations may
change. That resource frame does not turn the sequential ISA execution into a
concurrent execution theorem.

[`ByteScanWindows`](../EDSL/Corpus/V1/ByteScanWindows.lean) checks the complete
frozen file, requested name, unique symbol extent and executable mapping.
[`ByteScanResources`](../EDSL/Corpus/V1/ByteScanResources.lean) constructs a
useful nonempty call at each actual selected entry with checked current loans,
an aligned private original caller slot, and actual buffer bytes. The witness
retains **every installed ELF cell and all its permissions**, including cells
outside the function, in the same resource world as that call.
[`ByteScanCertificates`](../EDSL/Corpus/V1/ByteScanCertificates.lean) composes
those facts with universal body semantics through the fixed
[`BufferCertificate`](../EDSL/Corpus/BufferCertificate.lean) API. A candidate
cannot choose a weaker task specification or substitute an unrelated useful
example for the loaded call.

## Instruction count and target limits

`ByteScanBodies.dynamic_bound` derives successful evaluation and conservative
instruction bounds of `6*(n+2)` for GCC and `7*(n+2)` for Clang. These count
modeled instructions. They are upper bounds, with no claim of exact cost,
minimum operations, cycles or hardware performance. The static 64-byte /
32-instruction CFG profile bounds the function representation, not `n`.

The [sequential ISA subset](sequential-corpus-isa.md) adds exactly the CMP8
memory/immediate form `80 /7 ib` with the existing unprefixed mod=00 base/SIB
address subset, plus exact NOP9
`66 0f 1f 84 00 00 00 00 00`. CMP reads one DATA byte and sets subtraction flags
at width 8; NOP9 has no operand read. Additional prefix/address combinations
and NOP lengths 6–8 remain unsupported. Later
[first-match search proofs](first-match-searches.md) add memory/register CMP8
and CMP32. All instruction bytes still require successful executable fetches.
Unsupported
instructions, malformed certificates and faults reject; they do not establish
a program defect or justify a weaker contract.

The represented target assumes long mode, multi-byte NOP support, disabled CET
IBT/shadow stacks, stable ordinary RAM, the modeled ownership/loan rules, and no
asynchronous interference or MMIO. It proves no source-level pointer provenance,
GNU preservation, native loader/physical CPU correspondence or Linux correctness.
These scan functions have no synchronization or concurrent-memory claim.

Regression cases cover first versus later NULs, high bytes, the final readable
byte, forbidden widened reads, arbitrary empty pointers, compatible code/data
and caller/data aliases, exact-file/name substitution, current authority and
actual loan revocation. The owned CMP8/NOP9 native observations are finite
conformance evidence; they are neither a proof oracle nor universal hardware
verification. CI rechecks the proof, resource and native regression suites;
the corpus gate separately audits and fresh-replays its imported proof closure.
