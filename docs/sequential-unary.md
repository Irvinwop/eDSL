# NEG32 and BSWAP64 finite conformance

Run `bash scripts/verify-sequential-unary.sh` from this checkout. It builds and
executes only project-owned Linux x86-64 SysV fixture code. Optional arguments
`ACCEPTED_CAPTURE.tsv ACCEPTED_OPCODE_DIRECTORY` additionally replay an existing
capture with the same complete matrix. Raw captures, generated proofs, compiler
objects and receipts stay under ignored `.cache/unary-registers/native/run.*`.
The script does not register tests or run All, corpus, release or CI gates.

`fixtures/native/unary-registers/{capture.cpp,registers.S,expected-literals.tsv}`
reuse the accepted owned fixture sources and independent literal table. Capture
does not consume expected outputs. Lean derives an input-only list before native
execution. The assembly establishes eight different arithmetic flag states with
ADD, then reads flags with PUSHFQ/POP to a GPR. Instrumentation between snapshots
preserves flags. Live linked instruction labels supply the exact bytes, which
are also saved separately and checked against independent opcode literals.
Final ELF disassembly, text bytes, compiler arguments and object hashes remain
in the receipts. The fixture assumes DF and AC already clear and never uses
POPFQ to install privileged or arbitrary flags.

The complete matrix contains 896 NEG32 observations (28 inputs, four registers,
eight seeds) and 512 BSWAP64 observations (16 inputs, four registers, eight seeds).
RAX, RCX, R8 and R9 have actual before/after snapshots. Inputs include dirty upper
halves, zero, signed extrema, asymmetric bytes and parity/nibble/byte boundaries.
The signed minimum tests the instruction; it remains outside the signed absolute
value function contract. Other native GPRs, every RAM location, OS state, ABI and
the actual instruction-fetch permission map were not captured.

`tests/native/UnaryReplay.lean` implements parsing, literal validation, generation
and the shared replay checker. It verifies the full case/register/seed matrix,
exact live bytes, actual destination prestate, independent full64 results, six
defined NEG arithmetic flags, other NEG flags and the full saved BSWAP flag image.
No expected result is computed with NEG, byte-swap, a model flag function, a
reference executor or a copied decoder. Duplicate, omitted and corrupted rows
must reject before proof generation. Nine corrupted-observation controls call
the full production step projection directly, bypassing literal/schema checks.

Each generated row checks public `Sequential.decodeAt` against the stable
`.negReg32 destination prefixed` / `.bswapReg64 destination` constructors and
public `Sequential.step` for **both** AF choices. It compares the entire modeled
flags word, full64 observed GPR values, exact relocated RIP and empty operand-read
list. The twelve unobserved GPRs have distinct synthetic model canaries; their
preservation is a model test. RAM values and execute/write maps have samples at
code, sentinels, canonical boundaries and holes. The audited `fullRAMFrame` /
`fullRAMAt` theorems separately preserve all three maps at **every** address for
the checker's authenticated new-instruction/no-store admission conditions.

Generated data is split into sixteen-row modules, with one `decide +kernel`
proof per row. The ordinary kernel checks all generated proofs at standard
budgets; no native decision procedure, unchecked solver, project axiom, hole,
resource-cap override or linter suppression is used. The final imported audit
follows all project theorem dependencies and permits only `propext`,
`Quot.sound` and `Classical.choice`. The script builds only the production Machine
and Audit import closure, copies those checked objects to a private module root,
and compiles its owned validator, regressions and generated modules there. Source
and provider pins must still agree at completion. Each Lean call independently
holds `/tmp/edsl-lean-build.lock`, uses the repository's pinned Lean 4.35.0,
`LEAN_NUM_THREADS=1`, `-j1`, and warnings as errors. Do not wrap this script in
an outer acquisition of the same lock.

`tests/SequentialUnary.lean` checks canonical encodings across all sixteen GPRs,
including RSP and R12, optional 40/41 NEG prefixes and 48/49 BSWAP prefixes.
Independent full-state examples cover full64 zero extension, prestate use,
arithmetic flags, RF/VM/debug/high-bit model frames, all untouched GPRs, no data
access and exact fallthrough length. It rejects other widths, memory/ModRM
extensions, LOCK, extra/repeated prefixes and REX.R/X bank aliases. Every required
instruction byte is checked for missing data and denied execute permission;
truncation, the canonical hole and upper-address RIP wrap have precise checks.

This is finite conformance between observations and the abstract production
model. PUSHFQ saves RF and VM as zero, so saved-image equality cannot establish
preservation of their hidden physical values. Arbitrary modeled flag challenges
in regressions are expressly synthetic. Hardware correspondence retains the
production target assumptions (long mode, its canonical-address profile, CET/IBT
and shadow stacks disabled, ordinary RAM, alignment-check/debug/asynchronous
state boundaries); this fixture does not discharge them. It proves no physical
CPU/OS refinement, exhaustive ISA correctness, language/backend preservation,
concurrency result or corpus certificate. Unsupported code, timeout, proof
failure and native fixture failure remain recorded failures, not defect claims.

Every run retains commands, separate stdout/stderr, actual exits, source and
object pins, generated module evidence and a closed SHA256 manifest. A run emits
READY only after its complete scoped compile/run/replay/audit and closing pins
pass. Earlier failed runs are retained. Scoped native conformance is separate
from full-library replay, corpus certification, and CI validation.
