# Grading callable DATA8 effects

`edsl-grade-call-memory64` checks the existing independent `CallMemory64.Claim`
against a complete raw code window or a selected ELF window and entry. It fixes
RDI as the current owned DATA8 pointer, RSI as the full64 input, target=input
and RAX=(input+1) mod 2^64. Actual covered CPU/OS execution, both current owner
capabilities, the union RAM frame, permissions, return and ABI are required.
Admission supplies present resources, with useful inputs for arbitrary bounded
code, including unsupported bytes. It assumes no future successful execution.

The candidate supplies code and proof data. It cannot choose the specification,
admission, engine, resource policy, imports or budget. CALL, a target reload,
operand-read order and instruction count are not acceptance conditions.

| Client proof | Module | Text bytes | Entry | Instructions |
| --- | --- | ---: | ---: | ---: |
| `EDSL.CallMemory64.Client.gccSeparate` | `tests.fixtures.CallMemory64.Covered` | 18 | 0 | 8 |
| `EDSL.CallMemory64.Client.clangSeparate` | `tests.fixtures.CallMemory64.Covered` | 18 | 0 | 8 |
| `EDSL.CallMemory64.Inline.claim` | `tests.fixtures.CallMemory64.Inline` | 8 | 0 | 3 |

The last client stores RSI through RDI, computes RAX with LEA, and returns.
Its exact bytes are `48 89 37 48 8d 46 01 c3`. Fresh GCC and Clang leaf outputs
meet the same task as the nested store/reload implementations. Counts and
read traces are separate proof results; the task does not require them.

Build the pinned installation and export a client packet:

```sh
lake build edsl-grade-call-memory64 edsl-proof-export tests.fixtures.CallMemory64.Covered
lake env .lake/build/bin/edsl-proof-export \
  tests.fixtures.CallMemory64.Covered EDSL.CallMemory64.Client.gccSeparate gcc.json
lake env .lake/build/bin/edsl-grade-call-memory64 0 whole-text.bin gcc.json
lake env .lake/build/bin/edsl-grade-call-memory64 --elf 18 0 function.elf gcc.json
```

The files must be the corresponding complete extracted text and linked ELF.
To reconstruct the three-instruction client's packet:

```sh
lake build tests.fixtures.CallMemory64.Inline.Accounting
lake env .lake/build/bin/edsl-proof-export \
  tests.fixtures.CallMemory64.Inline EDSL.CallMemory64.Inline.claim inline.json
lake env .lake/build/bin/edsl-grade-call-memory64 0 inline.bin inline.json
```

Raw mode retains the entire file. ELF mode uses the shared checked selector:
the whole executable, file-backed window starts at `e_entry - ENTRY_OFFSET`,
and its full span and selected entry must be valid. Helpers remain included;
selection never stops at the first RET. The kernel checks a final wrapper
containing the entire literal file, span and entry metadata, successful pure
selection and the new fixed claim. Another ELF container selecting the same
program may reuse its program proof with a new checked literal-file wrapper.
This establishes the callable contract on admitted worlds, with no process
startup or other-segment/entry-point safety claim.

The fixed foundational installation includes the new artifact contract and
generic verified resources. The exporter and controllers use the same snapshot;
client modules remain outside it. The exporter reads compiled client modules,
while the grader receives serialized proof data, checks fresh declarations and
audits dependencies. Only `propext`, `Classical.choice` and `Quot.sound` are
allowed. The executable, project objects and pinned Lean sysroot must be
provisioned as an immutable trusted installation. Each CLI invocation checks
one candidate, with a cumulative kernel budget shared by packet and wrapper.

Defaults remain 4,194,304 packet bytes, depth 128, 300,000 decoder steps,
256 declaration entries/generated names, 100,000 audit steps and 10,000,000
kernel heartbeats. Raw windows are limited to 4096 bytes; ELF files to 65536
bytes and selected windows to 4096 bytes in one executable file-backed segment
in the lower canonical address range. Usage exits 2, unsupported admission 3,
malformed packets 4, proof/audit rejection 5, exhausted budgets 6 and IO or
installation failures 1. Acceptance prints one `ACCEPTED` line and exits zero.
Every rejection or exhausted budget establishes no security defect.

`CallMemory64.minimum_modeled_instructions` proves that an accepted candidate
needs at least three modeled instructions on admitted inputs where both RAX
and the target need to change. Each permitted actual step retains RAX or the
whole memory; the terminal original-slot RET retains both. The inline witness
attains three. This concerns the accepted mixed effect relation, without a
claim about all raw ISA instructions, CPU cycles or micro-ops.

The default `scripts/verify-call-memory64.sh` gate now includes actual nested
and inline raw/ELF proof grading, artifact/protocol negatives and import-isolation
checks. Inline compiler artifacts receive proof grading. Its native observer
still covers the two nested profiles; no extra inline native observations are
claimed. Explicit `--native-only` skips both formal and grading phases.

The ordinary-RAM, canonical-address and AC/CET-disabled assumptions, with no
asynchronous interference, remain those of the [callable DATA8 model](call-memory64.md).
Current resource ownership and loader freshness remain caller obligations.
Source preservation, full OS/kernel refinement, concurrent calls and general
task registration remain outside this slice.
