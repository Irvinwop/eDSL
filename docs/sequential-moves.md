# Ordinary MOV and current OS resources

The separate Lean `X86.Sequential` backend decodes unprefixed `89 /r` and
`8b /r` register copies, four-byte loads and four-byte stores. Register operands
use the eight lower GPRs. Copies and loads replace the full destination with
the zero-extended 32-bit value. Register-only MOV64 accepts a single REX.W byte
`48`–`4f` followed by `89 /r` or `8b /r` and mod=11. It copies the complete
pre-state source across all 16 GPRs, including RSP. REX.R extends ModRM.reg,
REX.B extends ModRM.r/m, and REX.X is ignored in register mode. Opcode `89`
writes r/m from reg; `8b` writes reg from r/m. These instructions occupy three
bytes. A self-copy retains the entire state except RIP+3. All MOV forms
preserve every flag, independently
of the undefined-AF choice used by other instruction families.

Memory forms accept mod=00 full64 base addressing and SIB with scales 1/2/4/8,
a present base and a present index. Displacements, RIP-relative operands,
prefixes, absent index/base, and extended-register memory encodings reject. Base forms
occupy two bytes; SIB forms occupy three. Unsupported SIB forms never become
shorter base forms. Both source registers and effective addresses come from
the pre-state, including when a load destination aliases its base or index,
or a store source aliases an address register.
There are no 64-bit memory operations in this extension. W=0 REX, repeated REX
and extra prefixes reject; TEST/CMP/ADD-immediate/INC/DEC retain exact `48`.

The architectural references are Intel's
[REX fields, volume 2, section 2.2.1](https://cdrdv2-public.intel.com/825760/325383-sdm-vol-2abcd.pdf)
and [MOV instruction entry, volume 2B](https://cdrdv2-public.intel.com/868141/253667-089-sdm-vol-2b.pdf).

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
MOV64 copies have no operand reads, store intent, locked effects or AF choice;
the context theorem retains full memory including both permission functions.

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

`current_movReg64_step` derives the actual full-width register copy and retains
the same current OS world, full RAM coupling, original code/stack loans and
all flags. It exposes the destination value, every other register and RIP+3.
Changing RSP retains authority for the original stack slot; it does not establish
that a subsequent RET can use the new RSP.

The all-input integration in
[`tests/SequentialMoveResources.lean`](../tests/SequentialMoveResources.lean)
uses exact SIB store/load bytes, a source that aliases the address base, and a
load into ESP. Current resources derive both real steps, source-low32 readback,
three-byte PC advances, current read authorization and the retained stack and
outside-memory frame.
The same file proves the six-byte `MOV RAX,RDI; MOV [RAX],ESI; RET` sequence
from arbitrary current resources and full-width target pointers. It derives the
real copy, checked mutation through copied RAX, retained current resources and
actual return from the original caller slot, with the full pointer in RAX.
No 32-bit pointer bound or successful future execution is a premise.

[`tests/SequentialMoves64.lean`](../tests/SequentialMoves64.lean) checks both
opcode directions, every GPR as source/destination, all REX.W bytes and bank
bits, self-copy width differences, complete context preservation, exact-byte
CFG admission, fetch failures and rejection by the existing TSO issue path.

[`scripts/verify-sequential-moves.sh`](../scripts/verify-sequential-moves.sh)
links 106 positive owned instruction windows and checks the extracted ELF section
against the executed bytes. Its 264 finite observations become named Lean
theorems: the original 152 MOV32 register/memory cases plus 112 MOV64 register
cases. The 56 MOV64 windows cover 16 assembler `89` copies, 16 explicit `8b`
copies, 16 assembler self-copies and eight ignored-X forms, each with two flag
and value profiles.
A C observer independently checks all 16 GPRs, complete
captured flags and all 32 observed data bytes, including nonzero upper halves,
unaligned operands and addresses above 4 GiB. A stack-independent assembly
capture supports modeled RSP changes. The native snapshots are replayed through
the public Lean step for both AF choices using kernel-checked proofs. Operand
read lists come from independent requested footprints; they are not hardware
read traces. Five safe owned width/direction/omitted-store/neighbor mutants,
including a requested MOV64 executed as MOV32,
must fail the C observer, and altered extracted bytes must fail identity checks.
These checks use valid ordinary memory; inaccessible/canonical/nonwrapping
failure cases remain modeled regressions. Evidence goes to
`artifacts/sequential-moves/`.
The 32 observed bytes are inside an owned writable page; offset 28 is not a
guard-page boundary. Captured flags cover the selected effective user-mode
profiles, not arbitrary RFLAGS. RIP comes from extracted continuation labels,
not hardware instruction tracing.

These are sequential ordinary-RAM results. They establish no atomicity,
concurrent visibility, physical exception delivery, hardware conformance,
source-language preservation, or full x86 support. Modeled instruction lower
bounds for useful `write32` inputs continue to apply to actual candidates in
this extended backend; they count retired instructions including RET rather
than cycles or micro-ops.
