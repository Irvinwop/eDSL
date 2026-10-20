# Unsigned average over full64 arguments

Both unchanged bodies passed the final aggregate gate, fresh kernel replay,
exact-file/resource checks and default-limit packet grading. This milestone
brings conditional coverage to **13/40 functions and 26/80 artifacts**. The
[measurement](../corpus/measurements/unsigned-average-v1/) records exact scope
and distinguishes local acceptance from CI and physical conformance.

The frozen `c_average_u64` functions use the existing scalar-call VCG,
complete named-ELF checker and current caller-resource constructors. Their
independent result is the floor of the **unbounded natural sum** divided by two:

```lean
result value output := output.toNat = (value.1.toNat + value.2.toNat) / 2
```

Every pair of full64 RDI/RSI arguments is admitted. In particular, the
specification does not restrict the sum to fit a word. Distinct overflowing
inputs `(0xffffffffffffffff, 0xfffffffffffffffd)` provide useful admission
separately from the universal domain.

| Responsibility | Reused component |
| --- | --- |
| Width-parametric natural arithmetic | [WordMath.Average](../EDSL/WordMath/Average.lean) |
| Independent full64 scalar specification | [Arithmetic64.Average](../EDSL/Arithmetic64/Average.lean) |
| Logical right shift and independent undefined AF | [Sequential.ShiftOne](../EDSL/X86/Sequential/ShiftOne.lean), [shift guide](shift-one.md) |
| Checked graph and production-generated obligations | [AverageBodies](../EDSL/Corpus/V1/AverageBodies.lean), [VCG](reusable-checker.md) |
| Complete named executable binding | [AverageWindows](../EDSL/Corpus/V1/AverageWindows.lean) |
| Current resources and registered certificates | [AverageCertificates](../EDSL/Corpus/V1/AverageCertificates.lean), [Scalar](../EDSL/Corpus/Scalar.lean) |
| Decoder-independent useful raw-code admission | [PureCall.Candidate](../EDSL/PureCall/Candidate.lean) |

The shared arithmetic proof establishes
`a + b = 2 * (a AND b) + (a XOR b)` in natural numbers, then proves that
`(a AND b) + ((a XOR b) >>> 1)` fits the output word and gives the specified
floor. It handles arbitrary bit widths, including zero. These mathematical
helpers have no machine, compiler, ownership or execution premises.

Each compiler's generated proof reduces its own checked production CFG and
uses that shared identity. Shared scalar frames handle scratch registers,
RAM, permissions, nonarithmetic flags and the actual return. The function adds
no interpreter, instruction-by-instruction proof chain or executable driver.
For another straight-line scalar function, follow the
[new-function guide](verify-a-function.md): supply an independent specification,
exact bytes, a checked graph and the remaining mathematical obligation.

| Compiler | File offset | Virtual address | Complete extent | Retired model instructions |
| --- | ---: | ---: | ---: | ---: |
| GCC | 11712 | 4206016 | 20 bytes | 7 |
| Clang | 4928 | 4199232 | 16 bytes | 6 |

GCC's original ENDBR64 remains in the unchanged frozen bytes. Counts include
it and RET and are conclusions of decoded execution. They measure this binary
in the model; they establish no optimal algorithm, minimum across equivalent
binaries, CPU timing or physical micro-operation count.

For raw packets, select `AverageBodies.gcc_semantics` or `clang_semantics`
before building the claim. The compiler-indexed convenience dispatcher refers
to both branches; direct selection avoids carrying the other compiler's
annotation proof into a packet. The required dependencies remain kernel
checked. The registered task is `average64`.

The final-file constructors check the complete original ELF, unique requested
name, full symbol extent, LOAD mapping and exact body bytes. They construct a
useful modeled caller at the actual selected address and reuse its original
code and eight-byte caller-slot loans. RAM, permissions and current resources
are preserved at every execution prefix and return. The mathematical result,
return target, RSP adjustment and callee-save ABI are established at return.
Every independent AF stream is covered; physical AF is undefined.

```sh
lake build AverageTests
bash scripts/verify-sequential-shift-one.sh
bash scripts/verify-shift-one.sh
bash scripts/verify-corpus-certificates.sh --full-project
```

Body/resource regressions challenge full-width input binding, overflowing
addition, floor rounding, dirty unbound state and the original return-slot
read. Grading controls reject a proof for the addition task or changed final
RET. The native runner separately checks owned finite SHR observations against
independent arithmetic and flags, and replays the production decoder/executor.
Finite observations do not replace the universal average proof.

The sequential target requires stable ordinary RAM, the recorded canonical
address profile, CET/IBT/shadow stacks disabled, supplied logical ownership and
caller loans, and absent asynchronous interference. These certificates do not
establish native Linux loading or ownership, physical CPU/OS refinement,
source/IR/compiler preservation or concurrent correctness. Proof failure,
timeout and unsupported encodings establish no security defect.
