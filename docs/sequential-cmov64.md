# Conditional register moves

The separate Lean `X86.Sequential` backend admits register-only CMOV64:
one REX.W byte `48`–`4f`, `0f`, a condition opcode `40`–`4f`, and a
mod=11 ModRM byte. The instruction is four bytes long. R extends the
destination in ModRM.reg; B extends the source in ModRM.r/m; X is ignored.
All 16 general registers are available, including RSP and operand aliases.
The existing legacy sequential/TSO decoder retains its previous subset.

`Condition` represents all sixteen condition codes. Its predicates inspect
CF/PF/ZF/SF/OF; AF is irrelevant. `ConditionFlags` proves equality and
unsigned CMP comparisons against `toNat` order, and signed comparisons
against `toInt` order. In particular, SF xor OF is proved to correct the
sign of wrapped subtraction; signed order is not inferred from SF alone.

`execute_cmovReg64_context` derives the full64 pre-source value when the
condition holds and retains the complete old destination otherwise. Both
outcomes preserve every other register, every flag, the entire memory
record and both permission maps, with no operand read or store intent.
The false-case theorem preserves the entire register file. There is no
undefined-AF choice for CMOV. The CFG layer treats it as read-only
fallthrough; static decoding still leaves functional correctness to local
proofs. Sum32's specialized shape checker does not gain a new loop shape.

Memory operands, W=0, extra/repeated prefixes and other opcode families
reject. This restriction matters: the architectural memory source of CMOV
is read unconditionally, including when its condition is false. A future
memory form must model that access and its failure behavior explicitly.
The reference is Intel's [CMOVcc entry, volume 2A, printed pages 3-157–3-160](https://cdrdv2-public.intel.com/868140/253666-089-sdm-vol-2a.pdf#page=275).

## Current OS resources

`OS.CallResources` provides current admission for calls with code and the
original complete caller-slot loans. It requires no unrelated owned DATA
allocation. Its contract records the current well-formed borrowing world,
executable bytes, eight return bytes, canonical return/post-stack addresses
and stack bounds. `Current` couples the complete machine memory to that
world's address space.

The CMOV bridge derives actual success from decoding and preserves the
same world, including all allocation owner/epoch metadata, loans, cells
and permissions. A CMOV that replaces RSP retains the original caller-slot
loan and contents. It does not authorize a different slot. Deriving RET
success and read authority through `current_ret_step` requires the machine's
present RSP to bind to the original slot; it performs the original STACK8 read. Resource regressions
exercise both a taken RSP replacement and an untaken CMOV followed by RET.

These are reusable instruction and resource foundations. They do not add
a scalar comparison task to the fixed-contract grader, a general program
certifier, source/IR preservation, a Linux implementation proof, hardware
timing or a global operation minimum. Target interpretation assumes CMOV
support, the existing ordinary RAM and System V profile, ordinary RET
without CET, and no asynchronous interference during the modeled call.

## Independent finite native checks

`scripts/verify-sequential-cmov64.sh` builds owned instruction windows into
a final linked ELF section. Before probing, it requires exact identity
between the extracted section and executed bytes; an altered extraction
must reject without emitting Lean observations.

The independent C contracts request named conditions and register operands
without decoding instruction bytes. They check all 16 GPRs and complete
captured RFLAGS against actual effective incoming flags. There are 52
positive windows and 1,664 snapshots: all sixteen conditions with all 32
CF/PF/ZF/SF/OF combinations, AF/DF profiles, register-bank combinations,
self-aliases, ignored X and RSP operands. This is selected register-pair
and value coverage, not every pair or every full64 payload. Six safe owned
mutants test incorrect conditions, operand selection, narrowing and flag
damage against the independent contracts.

Assembly captures all registers through RIP-relative stores before
restoring the host stack and capturing flags. No stack access occurs while
an arbitrary modeled RSP is installed. Successful observations replay
through actual `Sequential.step` for both AF choices as kernel-checked
Lean theorems, followed by the transitive dependency audit. Replay maps
only exact instruction bytes and requests an empty operand-read list;
this is a model footprint, not a hardware access trace.

```sh
EDSL_CLANG=clang-18 bash scripts/verify-sequential-cmov64.sh
```

Evidence and hashes are written under `artifacts/sequential-cmov64/`.
The harness is single-threaded, non-PIE Linux x86-64 with CET and alignment
checking disabled. Finite observations do not establish universal CPU/OS
correctness, memory fault delivery, speculation, concurrency, atomicity,
physical timing or whole-kernel safety.
