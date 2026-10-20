# Full64 comparison clients

Three independent grading tasks specify unsigned maximum (`maximum64`),
unsigned minimum (`minimum64`) and signed maximum (`signedMaximum64`).
`Comparison64.MathematicalResult` compares the returned word's `toNat` with
mathematical `max`/`min`, or its `toInt` with signed mathematical `max`.
Neither the specification nor admission selects flags, a conditional move,
compiler bytes, a trace shape or an instruction count.

Each task requires all-input termination and the System V callable frame:
the actual caller return address, RSP advanced by eight, all six callee-saved
GPRs, the complete unchanged memory record and all nonarithmetic flag bits.
Arithmetic status flags may change. Equal arguments, all full64 bit patterns,
arbitrary incoming RAX and flags remain in the universal input domain.

## Current OS resources

Resource admission uses `OS.CallResources`: the current well-formed borrowing
world, actual executable bytes and the original complete caller-slot loan,
with exact RAM coupling and the ABI argument bindings. It requires no unrelated
owned mutable DATA target. `Domain.resource_pre` constructs admission for any
nonempty byte span up to 4096 bytes and all full64 argument pairs independently
of decoding or execution. Useful unequal witnesses establish nonvacuity;
they do not restrict the universal semantic claim.

The resource policy requires current admission before every reachable step,
successful authorized operand reads, decoded read-only effects and complete
RAM preservation. It authorizes only reads of the original caller slot.
The raw-to-resource bridge consumes a proved original-STACK8 policy and full
RAM equality to retain the same coherent world at every prefix and return.
All cells, permissions, allocation owner/epoch metadata and existing loans
therefore survive. Returned code/slot authority remains usable. A different
RSP gains no new stack authority.

## Six exact compiler outputs

The client modules `tests/fixtures/Comparison64/{Machine,Raw}.lean` and their
aggregate prove six complete final linked GNU23 outputs. They remain outside
the grader's trusted imports. `Known` imports the independent domain and its
nonvacuity proof; it imports no comparison implementation theorem.

| Compiler | Task | Complete final bytes |
|---|---|---|
| GCC 13 | `maximum64` | `4839f74889f0480f43c7c3` |
| GCC 13 | `minimum64` | `4839fe4889f8480f46c6c3` |
| GCC 13 | `signedMaximum64` | `4839f74889f0480f4dc7c3` |
| Clang 18 | `maximum64` | `4889f04839f7480f47c7c3` |
| Clang 18 | `minimum64` | `4889f04839f7480f42c7c3` |
| Clang 18 | `signedMaximum64` | `4889f04839f7480f4fc7c3` |

Each eleven-byte window executes an actual CMP, register copy, register CMOV64
and RET. The shared proof covers both instruction orders and GCC minimum's
reversed comparison. Signed/unsigned condition adequacy comes from proved
mathematical order, including subtraction overflow. All AF choice streams
produce the independent result and full frame. Separate accounting proves
exactly four modeled instructions, including RET, and the singleton original
STACK8 read. Accounting is absent from task acceptance and establishes no
global minimum, micro-op count or physical timing.

The exact-profile integration uses GNU23 spelling `-std=gnu2x` with `-Os`,
warnings as errors, no LTO/CET instrumentation and separate function sections.
Each function is separately final-linked, the entire final `.text` is extracted,
and relocations reject. Compiler drift reports unsupported bytes. Final callable
ELF artifacts are entry windows; they are not standalone processes to execute.
No C-to-machine preservation theorem is claimed.

## Validation and grading

```sh
EDSL_GCC=gcc-13 EDSL_CLANG=clang-18 bash scripts/verify-comparison64.sh
```

The integration binds raw and complete ELF artifacts to their registered
contracts using exported data-only client proofs and fresh kernel checks.
Altered task IDs, byte spans, bytes and cross-compiler proof packets reject.
Kernel-checked counterexamples additionally show that a supported terminating
minimum implementation cannot satisfy maximum, and an unsigned maximum cannot
satisfy signed maximum at the signed boundary. These semantic counterexamples
are stronger evidence than failure to find a proof.

Independent finite native contracts require the result to be an original input
that bounds both inputs in the requested signed or unsigned order. The C oracle
does not decode instructions or reconstruct subtraction flags. It calls embedded
copies of the actual final extractions, checks all six saved GPRs, the real RSP
and all captured nonarithmetic RFLAGS. Boundary pairs, every bit boundary,
equality and deterministic full64 samples cover 188,416 calls per output,
1,130,496 total. All 128 CF/PF/AF/ZF/SF/OF/ID profiles must actually be installed;
DF is clear at each System V call.

Eighteen safe owned mutants exercise wrong direction/signedness, operands,
signed-overflow handling, narrowing, every saved GPR, stack imbalance, DF and ID damage. Twenty-four
altered/truncated/extended/substituted extraction cases must reject before
any native probe. These test the observer and binding, and are not compiler
or security findings. Signals, timeouts and unsupported bytes are inconclusive.

CI runs comparison integration as a separate parallel workflow with pinned
Lean and build caches. Its partial Lake cache has a distinct key from the
main full-project cache. Cached outputs never skip client audits, isolation,
fresh kernel replay, grading or native checks. Evidence is generated beneath
`artifacts/comparison64/`; `--native-only` explicitly omits proof checking.

These claims retain the documented sequential ordinary-RAM and CPU/OS
assumptions: CMOV support, stable code/caller memory, System V interpretation,
four-level canonical addresses, disabled alignment checking/CET and no modeled
asynchronous interference. Native observations do not establish universal CPU
or kernel correctness, data-memory access traces, speculation, concurrency,
atomicity, source preservation or whole-OS safety. GNU C++26/LLVM frontends and
broader ISA/OS support remain separate work.
