# Short conditional branches

The separate sequential x86-64 model decodes all sixteen unprefixed `70..7F`
short conditional branches. Opcode `74` retains the `.je` representation and
`75` retains `.legacy (.jnz _)`; the remaining opcodes use
`.jcc condition displacement`. The legacy decoder and concurrent profiles keep
their existing instruction subsets.

Conditions inspect the current CF, PF, ZF, SF and OF. Signed comparisons use
SF xor OF, equality includes ZF, and no condition reads AF. A displacement is
an eight-bit signed value relative to the end of the two-byte instruction.
The selected target uses full64 modular address arithmetic.

`ShortBranchForm` relates all three representations to the same condition
contract. `execute_shortBranch_context` derives the complete post-state when
`ShortBranchSafe` holds: every register, flag and memory permission remains
unchanged, there are no operand reads, and RIP is the selected destination.
A taken noncanonical destination produces `noncanonicalBranch`. An untaken
branch does not check its unused target. The subsequent fetch separately
checks whether its actual destination is canonical, executable and accessible.
Branch success alone grants no destination fetch permission.

`OS.CallResources.current_shortBranch_step` carries the same current OS world
through the actual decoded step, preserving code and original caller-slot
loans, allocation metadata and complete RAM coupling. It allocates no resource
and authorizes no new region. The resource integration example derives a
branch followed by RET from current code bytes and the original complete
caller slot, including the actual authorized eight-byte RET read.

CFG successor checking includes both fallthrough and signed branch target
independently of incoming flags. Successful dynamic continuations are proved
to select a checked edge, and code-fetch transport retains exact decoded
instructions. Typed Lean rendering supports the new instruction in CFG
artifacts without widening the restricted `sum32` program shape.

`tests/SequentialJcc.lean` checks independent architectural truth-table rows,
signed-displacement boundaries, canonicality, decoding failures and legacy
identities. `tests/SequentialJccResources.lean` derives the real branch/RET
composition against current resources. Each uses the theorem dependency audit.
The separate `scripts/verify-short-jcc.sh` native runner checks all sixteen
conditions at +127 and -128 with all 64 arithmetic flag profiles and both ID
values (4,096 calls), records effective before/after flags and actual reached
addresses, and rejects three synthetic semantic/frame mutants and three
altered extraction inputs. The C Boolean oracle is independent of the assembly
paths and Lean executor. Source snapshots, final bytes, commands and SHA256
manifests accompany each run. Use `EDSL_CC` to select the compiler and
`EDSL_SHORT_JCC_OUTPUT` to put evidence outside the default
`artifacts/short-jcc/`. Signals and timeouts fail the run without establishing
a program defect. Supplied extraction files are compared before probing and
are never executed.

Near Jcc (`0F 80..8F`), operand/address overrides, REX and other prefixed Jcc
remain unsupported. Long-mode control state, asynchronous interference,
debug exceptions, CET and actual OS page-table interpretation retain the
limitations in [coverage](coverage.md). The foundation does not itself prove a
new general compiler loop, source preservation, physical timing or operation
optimality.
