# Direct-add compiler clients

Two fresh Lean clients prove complete GCC13 and Clang18 GNU23 outputs against
the same registered `countedStore64` contract as the counted loops. With
`-std=gnu2x -Os`, LTO and CET disabled, the owned fixture emits:

| Compiler | Exact bytes | Decoded instructions |
| --- | --- | --- |
| GCC13 | `48 8d 04 16 48 85 d2 74 03 48 89 07 c3` | LEA; TEST; JE; STORE; RET |
| Clang18 | `48 89 f0 48 01 d0 48 85 d2 74 03 48 89 07 c3` | MOV; ADD; TEST; JE; STORE; RET |

The registered mathematical input supplies a full64 value, full64 count,
old target contents and actual caller return address. The independent result
is `value + count` modulo 2^64. Zero count retains the old eight-byte target;
positive count publishes the result. Complete outside-byte, permission,
callee-saved register, nonarithmetic-flag and actual RET/RSP frames survive.
No loop, source program, intermediate store count or compiler shape is part
of acceptance. These are final-code proofs without C or volatile preservation.

`tests/fixtures/CountedStoreDirect64/{Machine,Raw,Policy}.lean` shares the
arithmetic-prefix and guarded-store suffix arguments across both variants.
`gccClaim` and `clangClaim` are outside the grader's Known/trusted snapshot.
They quantify over every admitted input and every modeled undefined-AF stream.
The high-count and maximum-count evaluator regressions exercise the actual
decoder and RET; supported synthetic wrong-index and missing-store programs
return normally but violate independently specified result or memory posts.
An unsupported opcode, timeout or failed proof does not establish a defect.

## Present OS authority

The checked execution carries its actual current ownership world, complete
machine RAM coupling, live code/caller-slot loans and owner/epoch identities.
The positive path performs one actual checked owner mutation. Both paths
return the same coherent lifted execution, loan contents and outside frame,
with authority to perform another arbitrary checked64 store.

The reusable `Grading.StoreReturnValue64.StackPolicy` bridge lifts a proved
local policy whose reads use only the original complete caller slot. It
derives each actual32/64 ordinary store from current ownership and preserves
the real effect width. Readonly steps keep the same world, including register
changes. It does not turn unrestricted raw data reads into loan/owner authority
or manufacture a new stack binding after a change to RSP. The bridge is in the
aggregate library audit; the clients export it as proof evidence without
expanding the grader's trusted imports.

## Separate instruction accounting

The exact model costs include RET:

| Count | GCC13 | Clang18 |
| --- | ---: | ---: |
| Zero | 4 | 5 |
| Positive, including full64 maximum | 5 | 6 |

Every execution has the singleton original eight-byte STACK operand read.
Instruction fetches and write-validation queries are distinct from these
operand reads. Both positive costs are strictly below the proved final-store
loop's `3*N+5`; GCC's zero cost matches that loop's four instructions.
Clang's zero cost is five. These compare concrete implementations under one
result/resource task and prove no global minimum, source-effect equivalence,
micro-op count, CPU cycles or physical timing.

## Reproduce

```sh
EDSL_GCC=gcc-13 EDSL_CLANG=clang-18 bash scripts/verify-counted-store-direct64.sh
```

The script records compiler/linker versions, full arguments, ELF metadata,
disassembly and complete extracted `.text`. Identity gates require the exact
13/15-byte nonrelocated outputs. It runs the unchanged independent native
observer: 504 calls per output across high64 values, practical counts,
aligned/unaligned/page-edge targets above4GiB, old target values and full page
and external SysV ABI frames. Six generic owned loop-shaped oracle mutants
are separate from these direct implementations. Native runs do not cover
huge counts or independently observe every nonarithmetic flag.

The full path requires the client axiom audit, trusted-snapshot isolation,
fresh stored-proof kernel replay and reference/body packets for each output.
Packets bind complete raw and restricted ELF inputs. Changed task, bytes,
selected ELF span and the other compiler's packet reject. The existing direct
convenience shape APIs remain unsupported for these windows. All controller
limits remain unchanged; small named proof lemmas keep packet expression
depth within the existing bound. Evidence and hashes live under
`artifacts/counted-store-direct64/`.

The [ordinary machine profile](coverage.md#supported-machine-profile) and
[trust boundaries](trust.md) still apply: stable ordinary RAM/code and the
documented userspace CPU/OS environment, disabled alignment checking/CET and
no asynchronous interference. This adds no concurrent visibility, physical
ISA/kernel verification or whole-OS safety result.
