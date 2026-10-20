# Signed absolute value and byte reversal

The frozen row04 `c_abs_i32` and row10 `c_byteswap64` clients reuse the
[sequential checker](reusable-checker.md), [scalar-call contract](pure-call.md)
and [complete-file scalar constructor](corpus-scalar-certificates.md).
They add no interpreter, resource allocator or command-line executable.

## Independent contracts

`Scalar32.absoluteSigned` binds only low32 RDI, leaving its upper half arbitrary.
For every input except signed `INT32_MIN`, the signed low32 return must be
nonnegative and have the same mathematical integer square as the input.
Admission does not require a result, successful execution or compiler shape.
The signed minimum remains a supported machine NEG operand, but cannot satisfy
this signed absolute-value contract.

`Arithmetic64.byteSwap` binds full64 RDI. Each of the eight output base-256
digits equals the corresponding input digit in reverse order. Every full64
input is admitted, including zero. The shared `EDSL.WordMath` provider proves
uniqueness and the required arithmetic/byte-permutation facts independently of
decoding, instructions, OS admission and the selected compiler.

## Shared proof path

| Responsibility | Module |
| --- | --- |
| Candidate complete bytes and fixed spec selection | [`UnaryCode`](../EDSL/Corpus/V1/UnaryCode.lean) |
| Generated CFG/WP evidence and universal returning execution | [`UnaryBodies`](../EDSL/Corpus/V1/UnaryBodies.lean) |
| Complete frozen-file, unique symbol and entire-extent checks | [`UnaryWindows`](../EDSL/Corpus/V1/UnaryWindows.lean) |
| Registered contract and useful current caller resources at the actual address | [`UnaryCertificates`](../EDSL/Corpus/V1/UnaryCertificates.lean) |

File identity and functional behavior are independent obligations. Both consume
one candidate-byte definition and meet only at the existing certificate
constructor. The body proof uses production discovery and generated block
reduction, with the shared NEG32/BSWAP64 WP rules and mathematical lemmas.
Actual decoded RET, the original return slot, full RAM/permission equality,
callee-saved registers and original caller authority come from shared rules.

The theorem is universal over admitted inputs, initial registers/flags and AF
streams. A useful negative input for absolute value and an asymmetric input for
byte reversal separately establish inhabited admission at the selected ELF
address; they do not restrict the universal theorem to those examples.

| Compiler/function | File offset | Address | Bytes | Retired model instructions |
| --- | ---: | ---: | ---: | ---: |
| GCC absolute value | 11632 | 4205936 | 12 | 5 |
| Clang absolute value | 4864 | 4199168 | 8 | 4 |
| GCC byte reversal | 11760 | 4206064 | 11 | 4 |
| Clang byte reversal | 4960 | 4199264 | 7 | 3 |

Counts include RET and the original GCC ENDBR64. They follow from actual
returning model execution and are output guarantees, not admission conditions,
algorithmic lower bounds, physical CPU timing or minimum-cost claims.

## Validation and limits

```sh
lake build UnaryTests EDSL.Corpus.V1.UnaryCertificates
bash scripts/verify-sequential-unary.sh
bash scripts/verify-corpus-certificates.sh --full-project
```

[Body regressions](../tests/UnaryBodies.lean) challenge signed boundaries,
dirty upper arguments, full64 byte order and changed code. [Artifact/resource
regressions](../tests/CorpusUnaryResources.lean) challenge names, complete
extents, addresses, current executable text, permissions and finished loans.
[Native conformance](sequential-unary.md) compares owned CPU observations with
the production step for both AF choices, separately from these certificates.
CI preserves that finite owned evidence and fresh-replays the project/corpus
and unary regression closure through the complete corpus gate.
The full-project gate also exports all four raw claims, grades their exact
frozen byte spans through the installed CLI, and rejects wrong contracts and
changed code at default limits. Complete named-ELF binding is established by
the separate typed certificates above.

The existing sequential long-mode, canonical-address, CET/IBT/shadow-stack-off,
stable ordinary RAM and absent asynchronous interference assumptions remain.
Logical ownership does not authenticate native thread or kernel authority.
These results establish no physical CPU/OS refinement, source/LLVM preservation,
concurrent call history or whole-OS safety. Unsupported encodings, failed proof
search and timeouts yield no certificate or defect claim. The [corpus report](compiler-corpus.md)
records accepted coverage only after the full evidence gates pass.
