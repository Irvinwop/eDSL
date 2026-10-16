# Ordinary sum32 loops

Two ordinary C loop outputs satisfy the same independently stated unsigned
32-bit sum contract. The checked result covers every admitted input and every
sequence of undefined AF choices, with constructive termination, memory and
register frames, exact operand reads and an instruction-count theorem. A
structural checker accepts restricted pointer/count and indexed loop shapes.
This is a direct machine-code result; general source frontends, source/IR
preservation and arbitrary-program verification remain future work.

## Independent contract

[`X86.sum32`](../EDSL/X86/ArrayMemory.lean) converts the input words to natural
numbers, sums the list, and reduces modulo 2^32. Both loop implementations use
this definition. Their shared [`Sum32.Pre`](../EDSL/Sum32/Contract.lean) requires:

- Actual executable `CodeAt` bytes at the initial RIP.
- `ArrayAt` in current memory: each input element has a successful four-byte
  little-endian load at `RDI + 4*i`.
- A nonwrapping input span, `RDI.toNat + 4*values.length ≤ 2^64`, and the full
  64-bit RSI equal to the list length. The count is never truncated to 32 bits.
- A successful eight-byte `readWord` at the actual RSP, a canonical return
  target, and canonical `RSP + 8`.

`Sum32.Post` gives full RAX equal to the zero-extended modular sum, full
`Memory` equality including permission maps, RIP equal to the saved target,
and RSP advanced by eight. Every general register outside
`[rax, rcx, rsi, rdi, rsp]` is preserved, including all SysV callee-saved
general-purpose registers. All abstract flag bits outside CF/PF/AF/ZF/SF/OF are preserved;
the shared postcondition promises no particular final arithmetic flags.

The independent `operandReads` list contains one four-byte data read per
element, in increasing element order, followed by the actual eight-byte stack
read. There is no one-past input read. For empty input, `ArrayAt` and the span
bound require no readable or canonical input pointer. Its sole operand read is
the return slot; instruction fetches are outside this operand-read observation.
These are symbolic list theorems for every admitted nonwrapping span, rather
than a finite input enumeration or a fixed unrolling limit.

## Actual execution and termination

[`EDSL.Sum32.sound`](../EDSL/Sum32/Correctness.lean) takes a static `Valid`
certificate, the current `Pre`, and any `Sequential.Choices` stream. It
constructs a result of the actual decoded `Sequential.run` at the derived
instruction bound, satisfying `Post`, the exact cost and `operandReads`.
Successful execution and sufficient fuel are conclusions of the theorem.

`executes` constructs the corresponding finite transition execution;
`all_executions` quantifies over all choice streams. `safe` proves enabled,
fault-free execution from every reachable continuing prefix, and
`no_divergence` excludes an infinite continuing trace for any stream.
`checked_sound` composes `check_sound` with the same semantic theorem.
The generic [`Sequential.Execution`](../EDSL/X86/Sequential/Execution.lean)
layer proves evaluator soundness/completeness, fixed-stream uniqueness, block
composition, read origins, fault exclusion and all-choice divergence exclusion.

The [`pointer_loop`](../EDSL/Sum32/Pointer.lean) and
[`index_loop`](../EDSL/Sum32/Index.lean) proofs induct on the remaining list.
They maintain the accumulated modular sum, current readable suffix, actual
full-width pointer or index, code binding, return slot and frame. Checked
prologue initialization composes these header theorems into the shared entry
contract.

## Restricted structural checker

[`Sum32.Check`](../EDSL/Sum32/Check.lean) decodes the candidate's actual bytes,
discovers a proposed graph, and rechecks it through
[`Sum32.checkPlan`](../EDSL/Sum32/Code.lean) and
[`Shape`](../EDSL/Sum32/Shape.lean). Admission is capped at **64 bytes and 32
static instructions**. These limits bound the function window, not the input
count or execution length.

| Component | Pointer/count | Indexed |
| --- | --- | --- |
| Initialization | Clear RAX | Clear RAX and RCX |
| Header | `test rsi,rsi` | `cmp rsi,rcx` |
| Exit guard | `je` to RET | `je` to RET |
| Accumulation | `add eax,[rdi]` | `add eax,[rdi+rcx*4]` |
| Updates | `dec rsi` and `add rdi,4`, in either order | `inc rcx` |
| Back edge | `jmp` to header | `jmp` to header |

Prologues may use `xor eax,eax`, `xor ecx,ecx` and the supported `mov eax,0`,
with repeated clears and different clear order. The required registers must
actually be cleared, and other prologue effects reject. The graph has contiguous
decoded instruction boundaries, the prescribed operations, signed relative
branch links to the actual header/exit, and a final one-byte RET. There are no
per-compiler whole-byte equality recognizers for these shapes.

`Valid.decoded` transports each checked node to actual current `CodeAt` memory;
`forward_target` and `backward_target` establish the real branch destinations.
The interpreter selects instructions solely by actual fetch/decode, without
an expected-PC or expected-opcode gate. Decode transport needs no padding after
the final RET. The checker remains restricted to these two graph families and
register roles; it infers no general loop invariant or arbitrary contract.

## Separate sequential ISA

[`Sequential.Machine`](../EDSL/X86/Sequential/Machine.lean) embeds legacy
instructions exactly and adds these parameterized families:

| Family | Supported new encoding/effect |
| --- | --- |
| XOR-self32 | `31 /r`, register mode with identical operands; zero-extend zero into the destination |
| TEST64 | `48 85 /r`, two registers; full-width AND for flags only |
| CMP64 | `48 39 /r`, two registers; subtract the reg operand from the r/m operand for flags |
| ADD-memory32 | `03 /r`, mod=00 base or SIB address; read four bytes and zero-extend the 32-bit register result |
| MOV-register32 | `89 /r` or `8b /r`, register mode; copy low32 and zero-extend into the full destination |
| MOV-register64 | `48`–`4f` REX.W then `89 /r` or `8b /r`, register mode; copy the full source across all 16 GPRs |
| XCHG-register64 | `48`–`4f` then `87 /r` in register mode or `90+rd`; swap both original full64 values, preserving all flags/RAM |
| MOV-load32 | `8b /r`, mod=00 base or SIB address; actual four-byte read and zero-extended destination |
| MOV-store32 | `89 /r`, mod=00 base or SIB address; actual checked four-byte store with all registers/flags preserved |
| ADD-immediate64 | `48 83 /0`, register destination and sign-extended imm8 |
| INC64 | `48 ff /0`, register destination, preserving CF |
| DEC64 | `48 ff /1`, register destination, preserving CF |
| JE | `74 rel8`, consume ZF and check a taken target |
| JMP | `eb rel8`, check the relative target |

MOV64 and ModRM XCHG64 register operands use REX.R/B to select all 16 GPRs;
REX.X is ignored in register mode. Short XCHG64 uses B for the opcode register,
ignores R/X and advances by two bytes. Other new register operands use the eight lower GPRs.
Memory ADD/MOV accepts no
displacement: a plain base excludes encoded RSP/RBP; SIB supports scales
1/2/4/8 with a present base and index, excludes index=4 and base=5, and evaluates
both registers at 64 bits. Memory operands reject REX prefixes, 64-bit loads
and stores, RIP-relative addressing, missing-base/index and other unsupported
forms. The other listed 64-bit families require exact `48`; W=0 REX, repeated
REX and extra prefixes reject. XCHG64 admits no memory operand or LOCK prefix.
See [MOV/exchange scope and references](sequential-moves.md).

[`Sequential.Flags`](../EDSL/X86/Sequential/Flags.lean) proves the six status
bits, arithmetic carry/borrow/overflow and preservation of all remaining bits.
XOR/TEST clear CF/OF and derive SF/ZF/PF from the width-correct result; AF is
undefined in Intel's instruction contracts. See the official
[XOR entry, volume 2D, pp. 6-40–41](https://cdrdv2-public.intel.com/843855/334569-sdm-vol-2d-dec-24.pdf#page=43)
and [TEST entry, volume 2B, pp. 4-721–722](https://cdrdv2.intel.com/v1/dl/getContent/671241#page=729).
The model supplies a Boolean choice for each retired instruction; only
XOR/TEST use it. Both AF outcomes satisfy and exhaust the logical-flags
contract. An AF choice stays in the concrete flags word until overwritten.
Quantifying over all streams conservatively covers undefinedness without
asserting that a physical processor realizes every stream.

The existing deterministic and TSO decoders retain their original subset.
Additional encodings reject there; overlapping legacy MOV encodings keep their
original representation in the sequential decoder. Legacy execution embeds with
its complete state, flags and cost for every stream. Existing exact-flags and restricted minimality
theorems retain their scope. This sequential extension establishes no new
concurrent or buffered execution backend.

## Current OS resources

[`OS.ArrayResources`](../EDSL/OS/ArrayResources.lean) requires current
well-formed borrowing resources, authorized code and complete eight-byte stack
loans, plus an input loan only when the list is nonempty. Code/stack and the
nonempty input spans are disjoint. Current `CodeAt`, `readWord`, `ArrayAt`,
range and return facts accompany that authority. Empty input needs no input
allocation or live input-loan ID, even for an unused noncanonical pointer.

`Admission` couples the machine's **full current Memory** to the current OS RAM
projection. It contains no snapshot substitution, assumed future successful
execution or callback. `Contract.frame` and `frame_atomics` preserve protected
current cells and permissions through guarded histories while their loans
survive; unrelated memory may change. These resource frames do not execute the
new ISA in the old concurrent profiles.

[`Artifact.pre_of_admission`](../EDSL/Sum32/Artifact.lean) derives `Pre` from
current admission and explicit RIP/RSP/RDI/RSI bindings. `resource_sound` then
constructs all-choice execution with the same `Post`, cost and reads, retained
resource admission, and current loan permission for every actual operand read.
Logical loan IDs do not enforce native authority; native OS/resource and
hardware conformance remain external obligations.

## Artifact and native boundary

`edsl-certify-sum32` accepts a complete raw function window or a restricted
full ELF64 `ET_EXEC` container. Generated Lean embeds literal observed bytes
and a typed literal plan, recomputes checker acceptance in the kernel, derives
`certified` from `Sum32.sound`, and exposes conditional `resourceCertified`.
Raw mode retains `Pre`, including actual code binding. ELF mode also embeds
the full observed file/image, checks parsing and entry bytes, proves modeled
loading, and derives `loadedCertified` at that same installed entry. Current
caller RAM, input, return stack and page freshness remain explicit premises.

ELF window selection follows actual sequential instruction boundaries through
the first RET within the static bounds; unsupported bytes are never skipped.
The CFG checker independently verifies the reachable branch links. An ELF
entry here is a **callable function**, without a process-startup or whole-ELF
safety theorem. A file cannot establish native resource admission.

| Owned C output | Selected profile | Function bytes | Prologue instructions | Proved retired instructions |
| --- | --- | --- | --- | --- |
| GCC 13 `sum32_ptr` | `-Os -fno-ivopts` | 19 | 1 | `6*n+4` |
| Clang 18 `sum32_index` | `-Oz` | 18 | 2 | `5*n+5` |

Both outputs come from [`fixtures/sum32.c`](../fixtures/sum32.c), with scalar
code, no LTO and no CET. GCC 13 spells GNU23 `gnu2x`; Clang uses `gnu23`.
For any admitted plan, the derived cost is
`(updates.length+4)*n + Ninit+3`: `Ninit+6*n+3` for pointer/count and
`Ninit+5*n+3` for index, including RET. Byte counts alone prove no cost result;
these counts claim no CPU timing, hardware performance or optimality.

[`scripts/verify-sum32.sh`](../scripts/verify-sum32.sh) produces final linked
function containers, extracts their final `.text`, and certifies both raw
windows and full ELFs. A separate owned assembly variant mixes MOV/XOR clears,
duplicates an RCX clear and reverses the pointer/count updates through the same
checker. Provenance, certificates and native observations go to
`artifacts/sum32-fixtures/`. An external assembly trampoline observes full RAX,
callee-saved registers, DF and practical stack/return behavior. The owned
observer uses closed algebraic sum expectations,
wraparound cases, empty null/guard pointers, and read-only arrays ending at
guard pages. Synthetic result/stride/overread and ABI mutants exercise these
observations. These finite native checks supplement the model proofs; they
establish neither universal platform conformance nor source preservation.

## Reproduce and rejection behavior

```sh
lake build EDSL edsl-certify-sum32
lake env lean -DwarningAsError=true tests/SequentialISA.lean
lake env lean -DwarningAsError=true tests/SequentialExecution.lean
lake env lean -DwarningAsError=true tests/ArrayResources.lean
lake env lean -DwarningAsError=true tests/Sum32Pointer.lean
lake env lean -DwarningAsError=true tests/Sum32Index.lean
lake env lean -DwarningAsError=true tests/Sum32Artifact.lean
bash scripts/check-audit.sh
lake env leanchecker --fresh EDSL
EDSL_GCC=gcc-13 EDSL_CLANG=clang-18 bash scripts/verify-sum32.sh
lake exe edsl-certify-sum32 FUNCTION.bin artifacts/Sum32Raw.lean
lake exe edsl-certify-sum32 --elf FUNCTION.elf artifacts/Sum32ELF.lean
```

The suites cover independent width/flag/address boundary vectors, distinct AF
histories, actual operand-read origins, current resources after managed peer
changes, complete stack protection, alternate layouts and both real loop modes.
Admitted empty-pointer families and modular-wrap examples exercise the complete
all-choice contract. Rejected supported-ISA mutants have an independently
demonstrated wrong result, invalid read, skipped-element fault or actual
infinite self-JMP trace; divergence is proved as a trace, not inferred from a
timeout.

CLI exit 0 requires Lean checking with warnings as errors and transitive axiom
auditing of the generated semantic certificate. Exit 3 means unsupported code,
layout, static bound or container feature; exit 4 means malformed input. Usage,
certificate-check and I/O failures return 2, 1 and 5 respectively. Rejection,
proof failure, timeout and old output-file existence establish no defect or
certification. CI builds the CLI, runs these six suites alongside the existing
suites, audits and replays the library, runs the owned native script, and
preserves only `artifacts/sum32-fixtures/` for this milestone. The broader
[coverage](coverage.md) and [trust boundary](trust.md) remain applicable.
