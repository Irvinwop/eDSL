# Eight-byte memory and current OS authority

The separate sequential backend supports ordinary full 64-bit MOV loads and stores
with one REX.W prefix, `48`–`4f`, and opcodes `8b /r` or `89 /r`.
Register operands cover all 16 GPRs. REX.R extends the data register, B extends
the base, and X extends a SIB index. X is ignored without SIB. Addresses and
store values use the pre-state, including data/base/index aliases and RSP.
Loads replace the entire destination; both operations preserve every flag.

The admitted memory subset uses mod=00 with a present base and, for SIB, a
present index at scale 1/2/4/8. Base forms occupy three bytes; SIB forms occupy
four. Encoded base value 5 rejects regardless of B: RBP/R13 require a displacement,
and the plain r/m value 5 encoding is RIP-relative. SIB index 4 rejects when X=0; with X=1 it
is the present R12 index. Missing operands never become weaker base forms.
Displacements, RIP-relative operands, extra prefixes, W=0 and other widths
remain outside this extension. The existing concurrent/TSO decoder is unchanged.

The references are Intel's
[MOV entry, volume 2B, pages 4-28ff](https://cdrdv2-public.intel.com/868141/253667-089-sdm-vol-2b.pdf)
and [REX/SIB field rules, volume 2A, section 2.2.1](https://cdrdv2-public.intel.com/929353/253666-093-sdm-vol-2a.pdf).
These definitions and the platform assumptions remain the physical-conformance
boundary; finite observations do not prove the complete CPU specification.

`X86.Memory64` checks a nonwrapping, canonical eight-byte operand and every
mapped/readable byte. Stores also require all 8 writable bytes before returning
an updated state. Errors return no partial next state. Little-endian readback
retains all 64 bits; the frame outside the eight-byte operand retains every other
byte and both permission functions. Data loads use data faults, while RET retains its
separate stack-fault contract. Loads record DATA8; stores record no operand
read. Instruction fetches are separate.

`Instruction.storeIntent64` is separate from the existing 32-bit intent.
Memory-preservation theorems exclude both widths, and `CFG.readOnly` rejects
all 64-bit stores, even same-value stores. The existing 32-bit raw/resource effect
policies reject these stores and retain their four-byte read authority. Supporting
an instruction does not silently weaken a registered task's resource policy.

`OS.AddressSpace.writeQWord_projects` proves that the checked cell update and
machine update produce exactly the same RAM and permissions. Ownership requires
the entire operand inside one current owner/epoch allocation. Readable adjacent
allocations cannot supply a larger operand. The `store64` mutation uses the
existing checked history and borrowing gate. A live read loan on any subregion
of that allocation freezes the allocation, including a disjoint subregion.
Surviving unrelated loans retain their 32/64-bit reads, cells and permissions.
Loan-authorized `Borrowing.loadWord64` also supports read-only memory.

`WordResources64` supplies a separate eight-byte contract over that same OS
world. Present ownership, full operand permissions, code and caller-slot loans,
and full RAM coupling derive actual load/store steps. A store retains allocation
identities, owners, epochs, frontier, loan records and nextLoan, with exact
readback and outside-cell frames. The following load uses that evolved world.
Loading into RSP retains authority for the original caller slot; RET still
requires its actual machine RSP binding and current slot contents.

`StoreLoad64` proves the seven-byte callable sequence
`48 89 37 48 8b 07 c3`: store RSI through RDI, load RAX from RDI, then RET.
Its independent post requires the complete argument in RAM and RAX, every
RAM and permission frame outside the eight-byte target, all SysV callee-saved
registers, all flags, and the actual return address/stack advance. Present inputs derive execution
for every AF stream. Accounting separately gives three modeled instructions and
DATA8 then STACK8 reads. The current-resource theorem retains the same checked
OS mutation and world through return, with usable owner authority afterward.

The direct certificate CLI checks literal raw or restricted ELF artifacts:

```sh
lake build edsl-certify-store-load64
lake exe edsl-certify-store-load64 FUNCTION.bin artifacts/Raw64.lean
lake exe edsl-certify-store-load64 --elf FUNCTION.elf artifacts/ELF64.lean
EDSL_GCC=gcc-13 EDSL_CLANG=clang-18 EDSL_CLANGXX=clang++-18 bash scripts/verify-store-load64.sh
```

Raw inputs must match the complete seven-byte window. ELF selects the RET-terminated
entry window within 64 bytes/32 instructions, without skipping unsupported code.
Literal parsing, executable file-backed bytes and loaded code are kernel checked.
Fresh loader space, ABI, caller memory/permissions and current resources remain
explicit. This convenience profile is separate from the registered
[`storeReturnValue64` task](store-return-value64.md), which permits different
proved implementations, contained32 accesses and arithmetic-flag changes.
Exit 0 means the emitted certificate checked; exit 1 is certificate failure,
exit 2 usage, exit 3 unsupported input, exit 4 malformed/empty input, and exit 5 IO
failure. Nonempty truncated/trailing raw windows use exit 3. The CLI owns its
checking lock. An old output file or timeout establishes no success or defect.

The integration builds GCC13 GNU23 (`gnu2x`), Clang18 GNU23 and GNU++26 `-Oz`
fixtures. A volatile pointer retains the fixture load; no source or volatile
preservation theorem is claimed. The exact extracted bytes receive 252 native
calls with full 64-bit values, addresses above 4 GiB, aligned/unaligned/page-edge targets
and complete data-page frames. The external trampoline checks saved registers,
stack balance/canary and DF; other flags are not independently observed there.
Six owned width/store/source/endian/neighbor mutants must fail.

The separate instruction observer adds 232 MOV64-memory snapshots across 58
windows, with all data registers, all admitted plain bases, extended SIB fields,
every scale, aliases and RSP changes. Its full register/flags/32-byte checks
replay through the public Lean step for both AF choices. Six new memory mutants
join the earlier 10 cases. Evidence goes to `artifacts/store-load64/` and
`artifacts/sequential-moves/`. Model regressions cover denied/unmapped upper
bytes, canonical holes, wrapping, allocation boundaries, stale epochs and loans.

These are sequential ordinary-RAM contracts under the documented CPU/kernel
profile, with alignment checking/CET disabled for native observations. They
establish no concurrent atomicity, source preservation, timing, unrestricted
optimality, general program verifier or whole-OS correctness.
