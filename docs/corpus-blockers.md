# Corpus v1 baseline and extension order

The [frozen corpus](compiler-corpus.md) has 40 function identities and two
compiler profiles: Ubuntu GCC 13.3.0 and Clang 18.1.3, with the exact executable
identities and options recorded alongside each final ELF. These are the
recorded initial production-CFG probe results:

| Stage | GCC artifacts | Clang artifacts | Meaning |
| --- | ---: | ---: | --- |
| Extracted exact function windows | 40/40 | 40/40 | Located bytes in the final linked image |
| Accepted by the original read-only CFG checker | 0/40 | 4/40 | Supported decoding and checked control flow |
| Certified end-to-end | 0/40 | 0/40 | Full independent contract and artifact/OS bridge |

The primary function score was **0/40** at the initial freeze: both compiler
profiles must meet the function's contract. The four accepted Clang CFGs were `c_min_u64`, `c_max_u64`,
`c_add_mod64`, and `c_atomic_load_acquire64`. In particular, decoding the atomic
load establishes no acquire synchronization or source-memory-order theorem.
Generic checker soundness or a separate 32-bit TSO counter theorem does not
certify the frozen 64-bit concurrent entries.

The [comparison/padding batch measurement](../corpus/measurements/cmp32-endbr-nop-v1/)
raises GCC CFG acceptance to **5/40**, with Clang at **4/40**, on the unchanged
80 windows. The GCC candidates are min, max, modular addition, the uint32 sum
loop and the acquire-load encoding. Exact ENDBR64 is supported under the
explicit CET/IBT-disabled target; register CMP/TEST32 and exact NOPs through
five bytes are supported too. This is a CFG-stage improvement. End-to-end
certification was still **0/40 functions and 0/80 artifacts** at that ISA-stage
measurement.

The later [named comparison report](../corpus/measurements/named-comparisons-v1/)
certifies **2/40 functions and 4/80 artifacts** under the recorded model
assumptions: full64 unsigned minimum and maximum for both exact final ELFs.
Their shared VCG, complete named-file checks and actual-address caller resources
are composed in one family adapter.

The subsequent [scalar-addition report](../corpus/measurements/scalar-addition-v1/)
reaches **3/40 functions and 6/80 artifacts** by adding both exact `c_add_mod64`
symbols. Registry-owned scalar specifications, generated-WP/resource bridges and
one generic final-file constructor share the recurring proof work. Overflow is
included. At that measurement, 37 functions / 74 artifacts retained their
outstanding ISA, contract, resource and concurrency obligations.

The [signed-clamp report](../corpus/measurements/scalar-clamp32-v1/) adds both
unchanged `c_clamp_i32` symbols for **4/40 functions and 8/80 artifacts**.
Reusable register CMOV32, low32 signed specifications and the existing scalar
constructor cover equal endpoints, signed extremes and arbitrary upper argument
halves. At that checkpoint, **36 functions / 72 artifacts** retained their ISA, result,
resource and concurrency obligations.
No frozen concurrent entry is certified by the separate finite complete TSO32
call-history adapter.

The subsequent [managed fetch-add report](../corpus/measurements/managed-fetch-add64-v1/)
adds both unchanged `c_atomic_fetch_add64` windows for **5/40 functions and
10/80 artifacts**, including one distinct concurrent function under the fixed
managed closed-batch model. One shared instruction-family checker and generic
batch admission/history/frame proofs establish the independent contract.
Actual full-image resource construction and a completed overlapping execution
establish useful admission separately. At that stage, **35 functions / 70 artifacts**
remained. Published x86-TSO,
GNU source orders and native Linux refinement remain separate obligations.

The [bounded byte-scan milestone](bounded-byte-scans.md) addresses row 18,
`c_strnlen_bytes`, through memory/immediate CMP8, exact NOP9, reusable byte-buffer
contracts and sparse first-match loop proofs. Both complete frozen GCC35/Clang34
windows now have universal body semantics and useful actual loaded-resource
certificates. The full-project/corpus gate and actual fresh aggregate replay
passed. At that milestone, conditional coverage was **6/40 functions and 12/80 artifacts**.
The [first-match search milestone](first-match-searches.md) then adds the
unchanged row-21 byte search and row-25 u32 search for both compilers through
shared width-parametric loop proofs and current full-image resource adapters.
That milestone reached **8/40 functions and 16/80 artifacts**. The subsequent
[paired byte-comparison milestone](paired-byte-comparison.md) adds both unchanged
row-19 `c_memcmp_bytes` windows through shared paired-buffer VCG and resource
rules and an independent unsigned lexicographic sign contract. That milestone
reached **9/40 functions and 18/80 artifacts**. The subsequent
[absolute-value and byte-reversal milestone](unary-functions.md) adds unchanged
rows 04 and 10 using shared unary semantics and compact VCG proof terms.
That milestone reached **11/40 functions and 22/80 artifacts**, leaving
**29 functions / 58 artifacts** at that checkpoint. The
[full64 popcount milestone](popcount.md) then adds both unchanged row-11
clearing-bit loops through shared counter/address rules, cardinality invariants
and sparse scalar/resource composition. The new
[popcount measurement](../corpus/measurements/popcount-v1/) brought
conditional coverage to **12/40 functions and 24/80 artifacts**.
The subsequent [unsigned-average milestone](unsigned-average.md) adds both
unchanged row-08 outputs using shared logical-shift semantics, independent
unbounded natural arithmetic and the existing scalar VCG/resource constructors.
The average aggregate gate and fresh replay passed. At that checkpoint,
conditional coverage was **13/40 functions and 26/80 artifacts**, leaving
**27 functions / 54 artifacts**.

The subsequent [parity](parity.md) and [rotation](rotate.md) milestones add both
unchanged row-12 `c_parity_loop` and row-09 `c_rotl64` outputs. Their combined
full-project/corpus gate and fresh kernel replay passed locally. At that milestone,
conditional coverage was **15/40 functions and 30/80 artifacts**;
**25 functions / 50 artifacts** remained. One distinct concurrent function was
certified under the existing managed model. The
[parity and rotation measurement](../corpus/measurements/parity-rotation-v1/)
retains these historical results.

The [byte-equality milestone](byte-equality.md) adds both unchanged row-20
`c_bytes_equal` outputs, reusing paired snapshots, original input loans and
read-only call transport. The complete-list contract requires canonical low8
0/1 and leaves upper56 unconstrained. GCC's 46-byte window uses a 64-byte cap;
Clang's complete 68-byte window uses an explicit 128-byte cap, both with a 32-node cap.
The full-project/corpus certificate gate and external fresh replay passed on
source `383d1f1ef928f551b89a8424ae46c8bb019ce2e2`. At that milestone, validated
conditional coverage was **16/40 functions and 32/80 artifacts**, including
**one distinct concurrent function**; **24 functions / 48 artifacts** remained.
The byte-equality
[measurement](../corpus/measurements/byte-equality-v1/) records these scopes and
[commit-specific CI results in GitHub Actions](https://github.com/Irvinwop/eDieSeL/actions).
Earlier probe counts below retain their historical scope.

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
all independent flag streams. Conditional coverage is **19/40 functions and
38/80 artifacts**, including **three distinct concurrent functions**;
**21 functions / 42 artifacts** remain.

Planned shared extensions include shifts and predicates with independently
undefined flags, additional multiplication forms, vector/struct effects, richer atomic methods
and lock histories, and further OS/resource composition. Source load/store and
acquire/release correspondence remain unproved. CFG admission alone certifies
none of these contracts.

At the initial probe, the first blocker for 37 GCC artifacts was opcode `0xf3` at offset zero; their
literal windows begin with `f3 0f 1e fa` (`ENDBR64`). The other three exceed the
current 64-byte profile. Ten Clang artifacts also exceed that bound. Remaining
Clang failures include unsupported 32-bit compare/test, shifts, additional
arithmetic and prefix encodings, addressing forms, and effects outside the read-only
profile. The machine-readable per-function reports are
[`gcc/baseline-cfg.json`](../corpus/v1/gcc/baseline-cfg.json) and
[`clang/baseline-cfg.json`](../corpus/v1/clang/baseline-cfg.json).

These are **first** blockers. Removing one may reveal another; 37 leading
`ENDBR64` failures do not predict 37 newly certified functions. The size check
also precedes decoding, so an over-limit entry has unmeasured instruction and
contract obligations. The frozen reports remain historical baselines; later
runs write new diagnostics under ignored artifacts or separate published
measurements rather than replacing them.

Use the following order for subsequent work:

1. Connect the common checker to independent arithmetic/order contracts and
   exact frozen full-ELF selection, ABI and owned caller-stack obligations.
   This establishes a real certification numerator and exposes repeated proof
   work that should move into shared rules.
2. Preserve the checked ENDBR64 target conditions when composing the newly
   accepted GCC functions. CET-enabled execution remains unsupported; decoding
   the exact landing-pad bytes does not establish hardware feature settings.
3. Extend whole-block VC generation and sparse loop invariants across the
   next common arithmetic, memory and control-flow families. Reuse the bounded
   scan's byte snapshots, first-match prefix and resource bridge for related
   search/comparison rows, while proving their independent results. Review the small
   CFG limits separately from semantic coverage; increasing a limit alone is
   no proof of safety, scalability or termination.
4. Extend beyond the implemented fetch-add and plain load/store cohorts to
   richer invocation/response histories and ownership composition. Handle lock
   invariant transfer and futex wait/recheck contracts, retaining explicit
   memory-model and progress assumptions. Keep concurrent entries in the score.

Every later milestone should report both certification denominators, the delta
from this baseline, first remaining blockers, and any new environmental
assumptions. Native conformance, decoder coverage, generated-VC discharge and
end-to-end certification remain separate measurements.
