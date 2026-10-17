# Full64 logical compiler clients and proof grading

Three independent callable tasks specify intersection, union and symmetric
difference of the set of one-bit positions in two full64 words:

| Task ID | Mathematical operation | Owned C function |
| --- | --- | --- |
| `intersection64` | Membership in both inputs | `intersection64` |
| `union64` | Membership in either input | `union64` |
| `symmetricDifference64` | Membership in exactly one input | `symmetric_difference64` |

`EDSL.Logical64.Contract` specifies all 64 positions using natural-number
`testBit` membership and proves that an answer is unique. The result contains
no ISA operation, flags, compiler, source expression or instruction count.
The public task contract admits present executable bytes, full64 RDI/RSI
arguments, arbitrary incoming RAX and flags, and complete original caller-slot
bytes with the canonical/nonwrapping return conditions. Zero and equal inputs
remain admitted. Nonzero unequal witnesses establish nonvacuity separately.

`ResourcePre` additionally binds the present borrowing world, code/caller-slot
loans, entry, arguments and actual RSP. It needs no mutable DATA target, future
successful execution, decoder/CFG result or instruction budget. Return retains
the independent answer, complete RAM and permission maps, actual caller RIP,
RSP+8, six SysV saved registers and every nonarithmetic flag. Arithmetic flags,
including AF, are unconstrained at this callable boundary.

## Complete byte proofs

Fresh GCC13 and Clang18 `-std=gnu2x -Os` outputs select the same seven bytes
per operation:

| Operation | Complete selected bytes |
| --- | --- |
| Intersection | `48 89 f8 48 21 f0 c3` |
| Union | `48 89 f8 48 09 f0 c3` |
| Symmetric difference | `48 89 f8 48 31 f0 c3` |

Each is MOV RAX,RDI, the full64 logical instruction with RSI, then RET.
`tests/fixtures/Logical64/Raw.lean` proves actual decoding/execution for every
full64 operand pair and every modeled AF stream. Prefix proofs follow the
actual reachable states and retain original RAM and authorized reads.
`returned_resources` retains the same current OS world and reusable original
code and caller-slot loans. The only operand read is the original STACK8.

These implementations retire exactly three modeled instructions. The separate
`Logical64.minimum_modeled_instructions` theorem gives at least two for any
actual returning implementation when the independent required answer differs
from incoming RAX. It uses the full sequential ISA, including atomic prefixes,
and no compiler or CFG shape. Neither statement proves a global three-instruction
minimum, a physical instruction/uop minimum or a cycle bound.

The `edsl-grade` registry fixes these mathematical and resource contracts.
It imports generic domains and contracts, excluding the client implementation
proofs. A serialized packet is data checked by the Lean kernel against the
selected task and exact artifact bytes, with the existing packet limits and
approved axiom policy. Reference and body exports both work. The identical
compiler windows intentionally accept the same packet; compiler identity is
not an admission requirement. Changing task, selected bytes, suffix or ELF span
rejects reuse of that packet without establishing a defect in the changed code.
A separate mathematical counterexample refutes the union claim for the complete
XOR implementation on equal high-bit inputs.

```sh
lake build edsl-grade edsl-proof-export tests.fixtures.Logical64
mkdir -p artifacts/logical64
lake env edsl-proof-export tests.fixtures.Logical64 \
  EDSL.Logical64.Client.intersection artifacts/logical64/intersection-proof.json --body
lake env edsl-grade intersection64 path/to/function.bin \
  artifacts/logical64/intersection-proof.json
lake env edsl-grade --elf 7 intersection64 path/to/function.elf \
  artifacts/logical64/intersection-proof.json
```

Use the corresponding function files in the native evidence directory printed
by the full verifier. ELF grading selects the complete entry window and binds
its exact bytes; native loading and caller admission remain explicit boundaries.
No complete C/source or LLVM-IR preservation result is established here.

## Independent native evidence and CI

```sh
EDSL_GCC=gcc-13 EDSL_CLANG=clang-18 bash scripts/verify-logical64.sh
```

The full runner snapshots the source, builds and audits the proofs, replays
EDSL and the client through fresh kernel environments, checks trusted-snapshot
isolation, exports six reference/body packets and grades 24 raw/full-ELF cases
covering both compilers. Twenty-four negative checks change task, span, internal
bytes or suffix. The separate cached CI job runs alongside the main suite.
Failures retain incomplete status and hashed evidence.

`scripts/verify-logical64-native.sh` separately supplies finite physical evidence.
It compiles and independently links all six complete functions, checks final
relocations and bytes, and embeds the exact extracted windows into an owned
observer. All six loaded windows must match the file extractions before any
probe. The oracle checks every result bit through set membership, six saved
GPRs, real caller stack/return behavior and all nonarithmetic effective flags.
It supplies no opcode decoder or Lean result computation.

There are 1,523,712 compiler-output calls across all six functions, covering
boundary words, all membership combinations at every bit position, equality,
complements and deterministic full64 inputs under 128 arithmetic/ID flag
profiles. Twenty-one safe owned mutants exercise wrong operations, width,
operands, saved-register clobbers, stack imbalance and DF/ID damage. Thirty-six
altered/truncated/extended/substituted/empty/full-ELF extraction inputs reject
before probing. Another 393,216 control calls check that the native observer
permits arbitrary arithmetic flags; those controls establish no complete RAM
or model-resource contract of their own.

Evidence lives under `artifacts/logical64/` for the full flow, or
`artifacts/logical64-native/` for native-only runs. `EDSL_LOGICAL64_PROOF_OUTPUT`
and `EDSL_LOGICAL64_OUTPUT` select their respective output roots. Source copies,
commands, statuses, final ELF/bytes and nested manifests are retained.

The target is the existing `sequentialReadOnlyX86CallableV1`: stable ordinary
sequential RAM, no MMIO or asynchronous interference, four-level canonical
addresses, disabled alignment checking and ordinary RET without CET. Logical
worker identity and physical CPU/kernel/loading conformance remain environmental
assumptions. Finite native calls do not prove universal hardware behavior,
physical whole-RAM tracing, concurrency, speculation, timing or whole-OS safety.
