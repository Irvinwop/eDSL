# Ordinary MOV32 and current OS resources

The separate Lean `X86.Sequential` backend decodes unprefixed `89 /r` and
`8b /r` register copies, four-byte loads and four-byte stores. Register operands
use the eight lower GPRs. Copies and loads replace the full destination with
the zero-extended 32-bit value. All forms preserve every flag, independently
of the undefined-AF choice used by other instruction families.

Memory forms accept mod=00 full64 base addressing and SIB with scales 1/2/4/8,
a present base and a present index. Displacements, RIP-relative operands,
prefixes, absent index/base, and extended-register encodings reject. Base forms
occupy two bytes; SIB forms occupy three. Unsupported SIB forms never become
shorter base forms. Both source registers and effective addresses come from
the pre-state, including when a load destination aliases its base or index,
or a store source aliases an address register.

The existing legacy decoder runs first. Its six supported MOV encodings keep
their exact representation and behavior. `decodeAt_transport` proves successful
decoding under successful-fetch preservation, including the actual ModRM byte
for overlapping MOV opcodes. Bytes beyond the decoded instruction need not
be accessible. The legacy concurrent/TSO backends retain their original subset.

`Sequential.Machine` proves register/load context frames and a common checked
`execute_storeIntent` equation for all ordinary stores. Loads record an actual
four-byte data operand read. Stores record no data reads; permission checks
remain part of the actual store primitive. The store checks all four mapped,
writable bytes and the operand's canonical/nonwrapping span before returning
a next state. Its frame retains every register, every flag, permission maps
and every byte outside that word. Errors return no partial next state.

`CFG.readOnly` rejects every generic store, including a same-value store. Register
copies and loads can participate in read-only CFG proofs subject to their usual
current-code, actual-read and independent-contract obligations. The sum32 shape
checker still accepts only its documented operations and register roles.

`OS.WordResources.current_store_step` derives a successful checked owner update
and an actual machine transition from current resources, a decoded instruction
and its actual store intent at the fixed call target. `storeAfterLength` follows
the decoded two- or three-byte length. The existing `storeAfter` convenience
state still advances by two. Returned effects preserve allocations, lifetime
frontier, loans, permissions, unrelated cells, and all surviving loan contents.
The fixed-task grader's ownership and target policy is unchanged.

`current_load_step` derives an actual target load from current owner/ticket
authorization, complete-word containment and memory permissions. It exposes
the real loaded value and read footprint, leaves the OS world unchanged, and
retains full current RAM coupling and the original code/stack loans. It creates
no target loan. A load into RSP retains the caller's original stack slot, while
a later RET separately requires the actual machine RSP to match that slot.

The all-input integration in
[`tests/SequentialMoveResources.lean`](../tests/SequentialMoveResources.lean)
uses exact SIB store/load bytes, a source that aliases the address base, and a
load into ESP. Current resources derive both real steps, source-low32 readback,
three-byte PC advances, current read authorization and the retained stack and
outside-memory frame.

[`scripts/verify-sequential-moves.sh`](../scripts/verify-sequential-moves.sh)
links 50 owned instruction windows and checks the extracted ELF section against
the executed bytes. Its 152 finite observations become named Lean theorems.
A C observer independently checks all 16 GPRs, complete
captured flags and all 32 observed data bytes, including nonzero upper halves,
unaligned operands and addresses above 4 GiB. A stack-independent assembly
capture supports modeled RSP changes. The native snapshots are replayed through
the public Lean step for both AF choices using kernel-checked proofs. Operand
read lists come from independent requested footprints; they are not hardware
read traces. Four safe owned width/direction/omitted-store/neighbor mutants
must fail the C observer, and altered extracted bytes must fail identity checks.
These checks use valid ordinary memory; inaccessible/canonical/nonwrapping
failure cases remain modeled regressions. Evidence goes to
`artifacts/sequential-moves/`.

These are sequential ordinary-RAM results. They establish no atomicity,
concurrent visibility, physical exception delivery, hardware conformance,
source-language preservation, or full x86 support. Modeled instruction lower
bounds for useful `write32` inputs continue to apply to actual candidates in
this extended backend; they count retired instructions including RET rather
than cycles or micro-ops.
