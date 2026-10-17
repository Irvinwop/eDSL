# Implemented coverage and remaining trust

Five exact compiler-output profiles verify unsigned 32-bit increment, load,
store, atomic exchange and locked fetch-add functions. A counted assembly-loop
profile adds modular increment by every 64-bit count and proved termination.
The separate ordinary `sum32` checker accepts restricted decoded pointer/count
and indexed loops against one independent list-sum contract, including
all-choice termination, current read resources and exact operand footprints.
The reusable read-only CFG layer checks finite control flow and composes local
Lean obligations for independently supplied contracts; its importer establishes
static graph facts, with functional proof obligations still explicit.
Its GCC stride-two instance proves the independent even-index modular sum,
all-choice termination, full ABI/memory framing, current OS read permissions,
exact `6*count+4` instructions and ordered operand reads. Its two-loop instance
proves the sum of two lists, exact `6*(lengthA+lengthB)+6` instructions, ordered
reads and retained current authority for both inputs, including compatible
readonly aliases.
The [fixed-contract grader](grading.md) registers these two mathematical tasks
and `write32`, a fixed-pointer low32 store, `storeReturn32`, which additionally
returns the full pointer, and `storeReturnValue64`, which stores and returns the
full64 argument, and `countedStore64`, which adds a full64 count with zero-count
target retention. Fresh [direct-add clients](counted-store-direct64.md) prove
complete GCC13 and Clang18 outputs for that same task with exact constant
instruction counts and reusable current OS authority. All require all-input termination
and current OS admission. Pair/stride require reachable read-only effects;
write permits ordinary stores at its fixed target, with checked evolving
ownership, actual prefix/return witnesses and retained allocation/loan,
permission and outside-target frames. It checks data-only proof packets against the chosen
task and exact raw/full-ELF artifact. Fresh safe helpers are kernel-checked.
Shared expression packets also carry the client-only MOV-initialized stride
implementation's universal proof. The same task accepts both implementations
without requiring identical code or instruction selection. Legacy tree packets
retain the same fixed expected theorem and dependency audit.
The owned-word task also accepts a client-only eleven-byte INC/store/DEC/store/
RET implementation, with two actual checked OS evolutions. It meets the same
all-input contract as the three-byte store/RET, including full argument
wraparound, current loans and the returned resource frame. Its five modeled
instructions need not match the separate two-instruction lower-bound witness.
A seven-byte client composes generic register-copy/store/load MOV32 and RET.
Its owner-authorized read follows the checked store in the same current OS
world, retaining the original stack and outside frame. It proves the same
task and exactly four modeled instructions with target4 then stack8 reads.
Task preconditions are inhabited for arbitrary admitted byte lists independently
of decoding; the write witness requires a real value change, and a RET-only
candidate is proved insufficient. The registry exposes fixed sequential callable
tasks with explicit profiles.
The standalone [GCC counted-store profile](counted-store64.md) and separate
[Clang profile](counted-store64-clang.md) prove two exact 20-byte loops against
the same independent contract for every full64 count. They compose checked owner
mutations through a reusable resource-aware cutpoint certificate, preserving
one evolved world, original loans and usable returned authority. Zero-count
retention, modular full64 result, complete byte/permission/ABI frames and a
conservative instruction bound are proved. Separate accounting additionally
proves exactly `6*count.toNat+4` (GCC) or `4*count.toNat+4` (Clang) retired
model instructions, including RET, and the original STACK8 operand read.
Separate raw/ELF checkers retain each profile's formula and bind final
artifacts; 504 native calls per profile and six generic owned mutants provide finite
evidence. A separate [counted-store grader task](counted-store64-grading.md)
accepts both checked proofs under the same independent contract. No byte shape
or accounting is part of its acceptance; no operation-optimality theorem follows.
Standalone ELF profiles reach exit 42 directly or across a bounded stream write
and compose with explicit OS contracts. A separate locked-add-loop certificate
connects exact bytes to finite OS counter-worker workloads and checked
collection. These are narrow slices,
with no general binary verifier, complete ISA, source frontend, Linux implementation
or verified OS claim.

## Supported machine profile

- x86-64 long-mode userspace, flat addressing and the 48-bit canonical-address
  profile. Physical interpretation requires valid architectural control state,
  alignment checking disabled, no single-step/breakpoint interference, CET
  disabled and no asynchronous state changes during the modeled call. These
  facilities are not modeled. Arbitrary modeled `flags` values do not establish
  conformance when physical alignment/debug controls would cause exceptions.
- `8D 47 ib`: `lea eax, [rdi + signed_disp8]`, with 64-bit address calculation,
  32-bit destination and zero extension into RAX. Flags are preserved.
- `8B 07`: `mov eax, DWORD PTR [rdi]`, a little-endian four-byte read and
  zero extension into RAX. `89 37`: `mov DWORD PTR [rdi], esi`, a four-byte
  little-endian store of the low 32 RSI bits. Flags are preserved.
- `8b 06` / `89 06`: MOV EAX,[RSI] / MOV [RSI],EAX, with the same complete
  four-byte checks and zero-extension/framing rules.
- `83 f8 00`: CMP EAX,0 with defined CF/PF/AF/ZF/SF/OF and all other flags
  preserved; `75 cb`: JNZ rel8 reads ZF and checks taken-target canonicality.
- `C3`: near `ret`, reading an accessible little-endian stack word, checking
  canonical return address, advancing RSP by eight and preserving other state.
- `B8/BA/BE/BF id`: MOV EAX/EDX/ESI/EDI immediate32, zero-extended into the full
  register with flags/memory preserved. Other immediate-register forms reject.
- `89 f8`: MOV EAX, EDI; `8d 40 ib`: LEA EAX, [RAX + signed disp8].
- `89 f0`: MOV EAX, ESI; `87 07`: implicitly locked XCHG DWORD PTR [RDI], EAX.
  XCHG emits one indivisible RMW event with actual old/new words, updates the
  four-byte operand and zero-extends the old value into RAX, preserving flags.
- `f0 0f c1 07`: LOCK XADD DWORD PTR [RDI], EAX, an indivisible modular
  fetch-add with old-value return and all six addition status flags.
- `e3 cb` / `e2 cb`: JRCXZ / LOOP rel8, signed offsets from the next instruction,
  full RCX and no flag changes. Taken noncanonical branch targets reject. Prefixes
  and other loop/condition forms remain unsupported.
- `0F 05`: a pre-privileged userspace syscall request boundary. ABI projections
  expose low32 RAX and RDI/RSI/RDX/R10/R8/R9 arguments; no privileged entry,
  RCX/R11 effects, SYSRET or kernel instructions are modeled.
- A memory interface with explicit accessible bytes, execute permission and
  per-byte write permission. Four-byte stores require every byte to be mapped
  and writable; checks complete before producing an updated memory. Mapping this
  interface to real page tables/OS permissions remains an assumption.
- Checked executable-byte binding and nonwrapping code/data/stack-operand ranges.
  Invalid fetch, inaccessible data, denied stores, unsupported encodings and
  noncanonical returns produce explicit errors. Errors/rejections are model
  outcomes, not proofs of a hardware exception class or security defect.
  General decoder fetching uses modular addresses; published profile certificates
  exclude wrapping instruction ranges through `CodeAt`.

Ordinary loads/stores model sequential RAM. A functional four-byte write alone
is **not an atomicity or concurrent-visibility theorem**. The separate XCHG
and locked-XADD profiles have indivisible abstract events; physical interpretation requires aligned
coherent WB RAM, stable translation and the restrictions in [atomic exchange](atomic-exchange.md).
Concurrent code/data changes outside admitted exchange histories,
MMIO, page faults outside this interface and real exception delivery are out of
scope. Misaligned ordinary accesses are admitted under the disabled-alignment-
checking assumption; device-specific constraints are outside this profile.

The ISA definitions are a reviewed subset interpretation of the
[Intel manuals](https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html):
LEA, MOV, SYSCALL and near RET in the instruction reference, 32-bit GPR writes/addressing
and alignment checking in the architecture/system reference. Their adequacy to
physical execution remains a model/physical-conformance boundary.

The separate `X86.Sequential` decoder embeds legacy instructions and adds
parameterized XOR-self32, TEST64, CMP64, ADD-memory32, ADD-register64, LEA64,
MOV-register32/64, XCHG-register64,
MOV-load32/64, MOV-store32/64, ADD-immediate64, INC64, DEC64, JE and JMP families.
Register-only MOV64, ADD64 and ModRM XCHG64 cover all 16 GPRs with REX.W/R/B and ignored X.
TEST/CMP, immediate ADD, INC/DEC and MOV32 register operands use the eight lower GPRs. Supported memory operands use
full-width base/SIB addressing with explicit
rejection of displacements, absent base/index and other unsupported forms.
Its bit-precise flag helpers give XOR/TEST an independent undefined-AF choice
per retired instruction. Ordinary MOV preserves all flags, uses pre-state
operands even under register/address aliasing, and zero-extends 32-bit results.
MOV64 register copies preserve the full source and advance by three bytes;
MOV64 memory uses all 16 data registers and REX.R/B/X for data/base/SIB index,
with three-byte base and four-byte SIB encodings. W=0 and extra prefixes reject.
All8 operand bytes, canonicality, nonwrapping and store permissions are checked.
LEA64 uses the same admitted REX.W mod=00 base/SIB encodings to compute a
full64 value from pre-state registers. It performs no data read or write,
does not check the computed value for canonicality, and preserves all flags.
Register ADD64 accepts both `01` and `03` directions and updates CF/PF/AF/ZF/SF/OF;
other flags, RAM and nondestination registers survive. Both instructions can
compose with the same current OS world, including RSP destinations, without
granting a new caller-slot binding. See [arithmetic scope](sequential-arithmetic64.md).
Register-only CMOV64 adds all sixteen condition codes and all 16 GPRs through
one REX.W prefix, retaining full64 false destinations, all flags and memory.
Signed/unsigned CMP conditions are proved against mathematical integer/natural
order. A pure-call resource bridge requires only current code/caller-slot loans
and derives actual CMOV and RET steps without unrelated target ownership.
Memory CMOV, narrower forms and extra prefixes reject. See
[conditional moves](sequential-cmov64.md) for scope and finite native evidence.
The separate 64-bit store intent cannot be admitted as read-only or by the
existing 32-bit effect policies; data read authority retains its actual width.
OS cell projection, single-allocation ownership, whole-allocation read-loan
freezing and checked histories preserve all 64-bit readback, outside cells,
permissions and existing 32/64 loans. Current resource proofs compose actual
store/load/RET with the same evolved world, owner/epoch/loan frame and original
caller stack binding. A direct raw/ELF profile proves actual GNU23/GNU++26
store/load output and observes full 64-bit values. See [eight-byte memory](memory64.md).
The separate registered `storeReturnValue64` task requires the full64 result and
eight-byte/ABI/current-resource frames, with nonarithmetic flags preserved.
It permits contained ordinary32/64 effects with their real widths and histories,
and target-subspan or current-loan DATA4/8 reads. Two fresh client proofs use
mixed64/32 stores with no data load, and a DATA4 read at target+4 respectively.
All-byte-span useful domains include unsupported code and upper-half-only value
changes. Raw/ELF reference/body grading retains default budgets and trusted
snapshot isolation. The same five final artifacts receive420 native calls;
actual semantic narrow-store/truncated-result rejections supplement wrong-proof
binding checks. Existing32 and strict64 policies are unchanged. See
[full64 result grading](store-return-value64.md).
Register XCHG64 swaps both original full-width operands, preserves every flag
and memory field, and advances by three bytes for `REX.W 87 /r` or two for
`REX.W 90+rd`. The short form uses B and ignores R/X. Both forms compose with
the same current OS world, including exchanges involving RSP; RET separately
requires the actual original stack binding. LOCK and memory64 forms reject.
The new store uses the same whole-word permission checks and outside-memory
frame as the original stores. Its resource bridge follows the actual decoded
length, including three-byte SIB instructions. A current-resource theorem composes
a full-pointer copy, a real store through that pointer and the original RET slot.
See [MOV details](sequential-moves.md).
`EDSL.StoreReturn32` adds direct raw/ELF certificates for two real compiler
store/pointer-copy orderings and a copied-RAX store variant. The independent
post requires the full target pointer in RAX, and current OS proofs retain
the actual checked mutation, world and loans. Exact three-instruction/stack8
accounting is separate from that post. The distinct registered `storeReturn32`
task retains the same domains and policies while requiring the returned pointer.
A fresh four-instruction RCX client proves it outside the direct shape checker;
the five-byte GCC13 GNU23 `-Oz` register-exchange client does so in three instructions.
see [pointer-returning stores](store-return32.md) and [grading](grading.md).
Separate accounting proves a three-instruction lower bound for arbitrary
policy-admitted candidates on useful inputs requiring a changed RAX, with
attainment by the three direct shapes. This includes RET and retains the actual
OS return frame; it is not a hardware or unrestricted-program optimum.
The existing deterministic and TSO decoders retain their original subset;
their exact-flags and minimality results retain their original scope. Legacy
encodings keep precedence in sequential decoding. See the
[encoding and flag details](sum32.md#separate-sequential-isa).

## Checked results

`EDSL.X86.Executes` is an unbounded finite transition closure. Theorems prove
soundness/completeness of the fuelled evaluator against it, deterministic
results/costs, and exclusion of an infinite continuing trace (ordinary or atomic)
after a proved terminating execution. This legacy machine execution is deterministic.
`AtomicExecutes` additionally retains the exact ordered RMW-event trace.
The separate `X86.Sequential.Execution` layer provides choice-indexed actual
execution, evaluator soundness/completeness, block composition and observed-read
origins. Its `AllExecutions` contract constructs a finite result for every
choice stream and derives reachable-prefix safety, no faults and no divergence.

| Profile | Exact bytes | Result for every admitted entry |
| --- | --- | --- |
| `increment` | `8d 47 01 c3` | Zero-extended modular increment of low 32 RDI bits in RAX |
| `load32` | `8b 07 c3` | Four-byte little-endian value at RDI, zero-extended into RAX |
| `store32` | `89 37 c3` | Low 32 RSI bits stored little-endian at RDI |

These three profiles return in exactly two modeled instructions, have no infinite
next-step execution, and have a unique completed result/count. RSP advances by
eight and RIP becomes the stack return address. Modeled flags and unrelated
registers are preserved. Increment/load preserve all memory; store preserves
permissions and bytes outside its four-byte footprint, with a readback theorem.

All profiles require exact executable bytes, a readable eight-byte return stack
and a canonical return target. Load additionally requires a successful data read.
Store requires mapped/writable data and disjointness from code and the return
stack, so the write cannot invalidate the next instruction or return address.
Nonempty entry witnesses cover every 32-bit load value and every old word/64-bit
store argument, as well as every increment input.

The `exchange32` profile checks `89 f0 87 07 c3` in exactly three instructions,
with one event that returns the old32 word and installs low32 RSI. Raw/full-ELF
certificates retain this event trace. Its exact binary theorem, guarded OS-cell
bridge, same-cell history theorem, nonvacuity evidence and physical boundaries
are detailed in [atomic exchange](atomic-exchange.md). The separate
[atomic-worker layer](atomic-workers.md) schedules these instructions over shared
OS cells with handle-managed lifecycle contracts.

Named proof entry points:

- `EDSL.Examples.Compiler.Increment.terminates_and_all_results_match` for increment.
- `EDSL.Examples.Compiler.MemoryOps.load_correct`, `store_correct` and
  `store_value_and_frame` for memory profiles.
- `EDSL.Examples.Compiler.MemoryOps.every_load_value_executes` and
  `every_store_value_executes` for nonvacuity.
- `EDSL.X86.store_sound`, `writeDWord_frame`, `writeDWord_preserves_code` and
  `readWord_congr` for reusable memory rules.

`Executes.changing_rax_costs_two` proves any successful execution in this
supported instruction subset that changes RAX needs at least two instructions.
The increment fixture attains the bound for zero input/initial RAX. This is an
instruction-subset bound, not an all-x86 or CPU-time optimum.

For the separate sequential ISA, `Sequential.Executes.memory_change_needs_two`
proves that any actual memory-changing returning execution needs at least two
modeled instructions. Its return classification covers every modeled
instruction, including stores, atomics and syscall boundaries, without a
read-only premise. `Grading.Write32.minimum_modeled_instructions` derives the
required memory change from the independent word-store contract on useful
inputs. `claim_minimum` applies it to arbitrary registered candidates;
`exact_two` and `resource_exact_two` attain two with the actual resource-return
history. `optimal_for_useful_input` compares all candidates satisfying that
same input contract. An already-equal RET-only raw example takes one, so this
bound is limited to useful inputs. See [cost scope](cost-model.md).

## Counted loop

`increment-loop` checks `89 f8 e3 05 8d 40 01 e2 fb c3`. It returns the low32
RDI value plus the initial full RCX count modulo 2³². RCX becomes zero, RAX is
zero-extended, RSP advances by eight and RIP becomes the stack return address;
other registers, flags and memory are preserved. Its user-instruction count is
exactly `2*initial_RCX.toNat+3`, including RET and the zero guard.

`IncrementLoop.loop_executes` proves the invariant and decreasing natural
remaining-count variant by induction for every 64-bit count, without unrolling.
`actual_bytes_correct` and `terminates_and_all_results_match` compose the entry
instructions, prove finite execution, unique result/count and no ordinary-step
divergence. As for the other functions, code binding, readable return stack and
canonical return target remain explicit. Satisfiable states cover every value/count.

Both raw and complete ELF certificates are supported. The fixture is owned
assembly assembled by Clang/GCC; no C/C++ source-preservation claim is made.
Native observations cover bounded counts; the theorem covers all counts. No
timing/optimality, general loop inference, memory-lifetime or concurrency theorem
is implied. See [control flow and exact scope](control-flow.md).

## Ordinary sum32 loops

`EDSL.Sum32.sound` in [Correctness.lean](../EDSL/Sum32/Correctness.lean) proves
both restricted loop families meet the same independent natural list-sum
contract modulo 2^32. For every admitted current array and every undefined-AF
stream it constructs a successful actual decoded execution, rather than
assuming a future run succeeds. `checked_sound` composes structural acceptance;
`all_executions`, `safe` and `no_divergence` expose the universal execution,
fault-exclusion and termination guarantees.

The shared precondition binds current executable bytes, full RSI to the list
length, current four-byte little-endian elements, a nonwrapping entire input
span, the actual readable eight-byte return slot, and canonical target/RSP+8.
The postcondition gives full RAX zero extension, full unchanged Memory, the
actual return RIP/RSP, every GPR outside `[rax, rcx, rsi, rdi, rsp]` unchanged,
and all flags outside the six arithmetic bits preserved. Exact reads are the
successive four-byte elements then stack8, with no one-past read. Empty input
needs no input allocation, loan, readability or canonical pointer and has only
the actual stack8 operand read. Code fetches are outside this read observation.

`Sum32.Check` discovers a decoded graph and rechecks finite layout/operation
facts through `Sum32.checkPlan`: at most 64 bytes and 32 static instructions,
contiguous nodes, actual decoding and forward/backward branch links. `Valid.decoded`
transports those facts through actual `CodeAt` memory. Supported zeroing
prologues can mix MOV-zero/XOR-self, repeat clears and change clear order;
pointer/count updates can commute. The checker remains restricted to the two
shapes and register roles, without per-variant whole-byte equality recognizers,
general invariant inference or an arbitrary-program grader.

| Owned ordinary C output | Bytes | Derived retired-instruction count, including RET |
| --- | --- | --- |
| GCC 13 pointer/count, `-Os -fno-ivopts` | 19 | `6*n+4` |
| Clang 18 indexed, `-Oz` | 18 | `5*n+5` |

Generic costs are `Ninit+6*n+3` and `Ninit+5*n+3`, with `Ninit` the checked
prologue length. Static byte counts prove no instruction cost, hardware timing
or optimality. Symbolic input lengths are constrained by full-width count and
nonwrapping span conditions, not by the static checker bounds.

`OS.ArrayResources` binds authorized current code/stack/nonempty-input loans
and full current machine RAM to the OS projection. It proves protected framing
through retained-loan managed histories. `Artifact.pre_of_admission` and
`resource_sound` derive the same all-choice execution, exact reads and current
permission for every actual read, retaining resource admission through unchanged
memory. No field assumes future execution or restores an old snapshot.

`edsl-certify-sum32` emits literal raw/full-ELF semantic certificates using the
checked theorem, plus conditional typed resource theorems. ELF mode checks the
whole file and derives code and execution at the same modeled loaded entry.
Current caller input/stack/RAM, resource authority and loader freshness remain
explicit. An ELF callable function entry establishes no process startup or
native OS admission. The owned native script observes exact final linked
windows through an external ABI trampoline; those finite observations leave
hardware/kernel conformance external. Full contracts, supported encodings,
meaningful negative cases and reproduction commands are in [sum32](sum32.md).

## Reusable CFGs and local proof obligations

`X86.Sequential.CFG.check` validates an entire explicit window of at most
64 bytes and 32 static instructions: actual decoding, a complete positive-length
partition, closed successors, entry cutpoint and decreasing noncutpoint depths.
The profile excludes stores, locked operations and syscalls. Discovery proposes
data that the checker revalidates. The actual machine still selects instructions
by current fetch/decode and `CodeAt`, rather than through the graph.

`CFG.Annotations` supplies current code/PC binding, cutpoint invariants and
dynamic ranks, interior annotations and local instruction/read-permission proofs
for every AF choice. The generic theorem constructs all-choice actual execution,
postconditions, prefix safety and no divergence, bounded by
`(maxDepth+1)*(entryRank+1)`. `Cutpoints.Accounting` optionally composes proved
local cost/read equations into exact retired-instruction counts and ordered
operand reads. These are model instruction counts, without timing or optimality.

`edsl-cfg-import` emits kernel-checked literal static imports and a typed local
proof interface. Raw mode uses the complete supplied window; ELF mode requires
an explicit `1..64`-byte entry span and checks the full container. It never
truncates an arbitrary CFG at the first RET. The two-loop 35-byte GCC output
additionally has functional local proofs of an independent two-list sum,
all-choice total correctness, exact cost/reads and two current OS admissions.
Empty inputs need no input loan or valid pointer; compatible readonly aliases
are supported. See [two-array contracts and evidence](pair32.md). The stride-two
instance proves an independent even-index sum, all-choice total correctness,
current OS read origins and exact `6*count+4` instructions/ordered reads through
local annotations. See [the precise contracts and extension workflow](cfg.md).

## Abstract OS address-space contracts

`EDSL.OS.AddressSpace` models sequential byte-granular fresh zero-filled mapping,
protection changes, unmapping and byte writes. Checked operations reject invalid
ranges, overlap, holes and unsupported permissions. Stored bytes survive removal
of read permission; unmapping removes them. Proofs establish outside-region
framing, preservation of existing mappings and read/fetch/store revocation in
the projected x86 memory model.

`EDSL.OS.AddressSpace.load32_after_protect` composes a successful abstract
protection change with the binary load theorem when code, data and return stack
are disjoint from the changed region. A concrete admitted-entry proof exercises
the composition. These operations do not yet model page alignment, allocation
failure, page tables, aliasing, physical reclamation or concurrent revocation.
Full mappedness is required even for abstract unmap; Linux allows unmapped holes.
See [address-space contracts](address-space.md) for the exact API and boundary.

`writeWord_projects` proves that a checked 32-bit OS cell update has exactly the
machine store's projected bytes and permissions. `store32_updates_space` composes
that update with actual compiler bytes, preserving registers, return behavior,
termination and count. All old data and 64-bit store arguments have admitted
witnesses. This byte-cell bridge alone does not prove physical page, aliasing,
resource identity or concurrent atomicity properties.

## Sequential ownership and allocation lifetimes

`EDSL.OS.Ownership` retains the same byte-space projection and adds live region
records with owner, never-reused allocation ID and transfer epoch. Checked
allocate/adopt/transfer/release/protect/store operations have `WellFormed`
preservation proofs: live IDs are below a monotone frontier, valid regions are
fully mapped (including hidden cells), and distinct allocations are disjoint.
Fresh mappings are zero-filled; adoption preserves exact existing cells.

Transfers advance the epoch even for the same owner. `release_invalidates` and
`transfer_invalidates`, combined with `Invalidated.persists` and
`revoked_for_history`, exclude current authority after any later finite managed
history. This covers same-address reallocation and A→B→A transfer. Stores check
all four bytes within one allocation before the machine permission preflight.

`owned_store32_correct` connects a successful authorized operation to the exact
store/RET bytes and OS-cell update, retaining code/stack framing, unique result,
two-step termination and divergence exclusion. A symbolic adopted-entry witness
covers all old words and 64-bit source arguments, with final well-formedness.
Tests also exercise stale/owner rejection, writable boundary crossing, final-byte
overlap, inaccessible adoption and permission restoration. See [ownership scope](ownership.md).

These are sequential proof-level authorities. Tickets/principals are constructible
data, raw instructions do not inspect them, and unmanaged mapping changes are
excluded from the managed history. No hardware stale-pointer prevention, linear
token discipline, C/C++ object provenance, runtime allocator or concurrency
theorem is claimed by the ownership registry. Adoption's finite scan relies on the explicit
well-formedness premise; malformed user-constructed worlds are not validated by
a global runtime checker. The existing certificate CLI does not synthesize
ownership registries automatically.

## Shared read borrowing

`EDSL.OS.Borrowing` wraps that ownership world with fresh stored read-loan IDs.
Checked borrowing authorizes the lender and validates a nonempty contained,
canonical, nonwrapping, fully readable region. Multiple overlapping loans are
allowed. While any loan remains, guards freeze the entire referenced allocation
against managed stores, protection changes, transfer and release; unrelated
allocations remain mutable. Completion checks the stored borrower and removes
only its loan ID.

Every admitted operation preserves `WellFormed`. `History.advances` and
`History.loan_stable` prove exact record/cell/permission stability for surviving
loans over arbitrary finite guarded histories. `finished_for_history` proves
finished IDs can never return. `History.loadWord_stable` retains authorized
word values; `History.buffer_stable` transports independently established
readable snapshots inside a live loan. `loadWord_exists` supplies successful
contained word reads under the well-formedness and authority premises.

`borrowed_load32_correct` composes a checked read with the exact load/RET bytes,
retaining two-instruction termination, unique state/count and divergence
exclusion. Code/return-stack premises refer to the execution state. Symbolic
adopted-entry witnesses cover every 32-bit value and preserve its read result
across every admitted history in which the loan survives. Regressions cover
all guarded mutation kinds, multiple loans, stale/wrong borrowers, disjoint
changes, unreadable tails and readable operands crossing a loan boundary.

The finite loan scan relies on `WellFormed`. This remains a logical sequential
discipline; raw stores, unmanaged mappings and arbitrary interference bypass it.
No concurrent adequacy, runtime authentication/enforcement, mutable/fractional
borrowing, region splitting or physical-alias handling is established. The CLI
does not infer loans. See [the exact borrowing contract](borrowing.md).

## Managed read-worker lifecycle

`EDSL.OS.Threads` adds root-managed spawn, per-instruction scheduling, join and
external guarded mutations over the shared borrowing world. Workers store only
private registers/RIP/flags. Every dispatch reconstructs memory from current
shared OS cells and executes actual `X86.step` for the checked `8b 07 c3`
profile. Spawn protects data, executable code and the return stack with three
internal read loans; completed workers retain them until join. Join returns
retained machine RAX and releases only its worker's loans.

All admitted steps/histories preserve the invariant. `spawned_join_value` proves
every successful join after arbitrary admitted finite interleavings returns an
independently specified initial word zero-extended into RAX. Peer private
contexts remain unchanged by another dispatch. Shared allocations remain frozen
while any peer loan remains. `joined_for_history` and
`joined_loans_for_history` establish permanent thread/loan-ID revocation.

`dispatch_enabled`, `join_enabled` and `two_dispatches_complete` provide positive
progress paths. `schedule_remaining` and `schedule_two_completes` count actual
worker selections and prove two suffice across any successful supplied
instruction schedule, with arbitrary peer preemption. `idle_trace` witnesses
that arbitrary scheduling need not complete a worker. Counts exclude runtime
and kernel overhead; no unconditional progress or timing optimum is inferred.

Owned regressions cover all six interleavings of two actual read workers,
separate return stacks and shared code/data, premature/wrong/repeated join,
completed dispatch, stale IDs, partial creation rejection, explicit resource
failure, protected data/code/stack and unrelated managed changes. Symbolic
witnesses admit every 32-bit word through checked adoption, spawn, both actual
instructions and join, with all-history conditional result preservation.

This is a managed read-worker contract, not native pthread/clone refinement,
CPU context-switch verification, hardware atomicity/SC/weak-memory semantics or
the separate shared-increment workload below. Root/worker Nat names are proof labels;
freshness concerns the lifecycle registry and does not authenticate native
identities. Unmanaged loan release, raw writes and arbitrary external
interference are excluded. Worker stacks do not support push/call here; TLS,
detach, cancellation, nested spawn and native publication barriers remain
unimplemented. A separate atomic-worker profile below adds mutable exchange
workers; a separate checked mutex protocol appears below, while general memory ordering remains unimplemented. See
[the full read-thread profile](threads.md).

## Shared atomic handles and reservations

`EDSL.OS.Atomics` wraps the borrowing world with distinct stored actor handles
for one supported atomic word per allocation. Issuance checks current owner/
epoch, containment, accessibility/write permissions, compatible existing handles
and absence of ordinary read loans. Each exchange checks the stored actor and
reads current cells using stored authority/address. While any handle remains,
the entire allocation is pinned against ordinary stores, protection, transfer,
release and new read loans; unrelated resources remain available.

Every admitted operation preserves `WellFormed`. Mixed histories retain
surviving handle records, permanently revoke closed IDs and preserve surviving
ordinary-loan cells/permissions. `exchange_enabled` supplies positive behavior
for every replacement. `exchange_step` and `exchange32_updates_space` bind the
resource operation to the actual XCHG step and exact compiler routine.
Arbitrary finite exchange-only schedules have actual old/new chaining and
an independent multiset-conservation theorem. Symbolic witnesses cover every
old/new 32-bit pair; regressions exercise distinct actors, last-handle closure,
loan conflicts, stale authority and actual compiler-byte composition after a
peer update. See [the handle contract](atomic-handles.md).

This is a logical shared authority layer. Raw accesses bypass it, finite scans
rely on the explicit invariant and actor labels do not authenticate threads.
Concrete OS/runtime refinement remains unimplemented. Value chaining does not
extend across arbitrary mixed histories with zero-handle gaps; operation
enabledness supplies no scheduling progress.

## Mutable atomic-worker lifecycle

`EDSL.OS.AtomicThreads` adds root-managed spawn, actual MOV/XCHG/RET dispatch,
join and guarded mutations over the shared atomic world. Workers keep private
registers/RIP/flags; each instruction sees current shared cells. Spawn acquires
an actor-specific atomic handle and separate code/stack loans, without reading
or caching the old data word. XCHG captures that instruction's actual old word
privately, and completion retains all three resources until join.

All admitted steps and histories preserve `WellFormed`. `dispatch_atomic_spec`
connects the actual machine event, current-cell update and private result.
`dispatched_join_value` proves every successful later join returns that event's
old word, zero-extended, despite arbitrary admitted peer/lifecycle/resource
actions. Joined thread, handle and loan IDs remain permanently revoked. Peer
private contexts and surviving code/stack authority remain stable.

`dispatch_enabled` and `join_enabled` establish positive operation paths;
`schedule_own_enabled` and `three_dispatches_join` supply a finite successful
own-instruction schedule and checked join from a preparing worker.
`three_dispatches_spec` proves the singleton event, joined old value and final
replacement against an independently observed initial word on that path.
`schedule_remaining` and `schedule_three_completes` prove three selections of a
preparing worker suffice in any successful supplied instruction schedule, with
peer preemption. Infinite idling remains admitted. `schedule_chain` and
`schedule_conservation` prove actual old/new chaining and duplicate-counting
multiset conservation across arbitrary successful dispatch-only schedules when
all workers target one address and initial memory is independently observed.

Owned regressions cover all twenty two-worker instruction interleavings,
independent old returns/final word/events, neighboring guard bytes, separate
return stacks, RIP and flags; they also cover lifecycle errors, stale IDs,
creation failure, partial acquisition rejection, conflicting resource changes
and unrelated allocation/store between instructions. The certificate profiles
are unchanged by this worker layer. Symbolic
witnesses use checked adoption and spawn for every initial/replacement 32-bit
pair, with an independent initial-word observation, exact event, joined old word
and final replacement across a successful three-step schedule/join.

This is an abstract lifecycle and scheduler contract with logical actor IDs.
Its histories admit only spawn, dispatch, join, guarded mutation and idle;
arbitrary raw exchanges and resource operations are outside the contract.
Native pthread/clone refinement, publication, context switching and general
x86/C++ memory ordering remain unproved. The separate counter-worker profile
below adds a counted algorithm, and the separate mutex profile protects a payload
invariant. General memory ordering and wait/wake remain planned. Mixed-history result/resource proofs do
not imply final-memory value chaining across zero-handle gaps. Counts exclude
runtime/kernel overhead and establish no unconditional progress. See
[atomic-worker contracts and assumptions](atomic-workers.md).

## Locked fetch-add and modular counters

The exact `fetch-add32` profile checks MOV/LOCK-XADD/RET in three instructions,
returning the actual old32 value and installing its modular sum with low32 RSI.
All six addition status flags are modeled and their bit positions, carry and
signed-overflow interpretations, and other-bit preservation are proved without
unchecked solver dependencies. Exact raw/full-ELF compiler certificates retain
the singleton RMW event, termination and unique result/count.

The checked OS-handle operation preserves the shared resource invariant and
projects to existing guarded histories. Its actual instruction and complete
compiler-routine bridges bind final machine memory to updated OS cells.
`AddTrace.counter` proves the final initial-plus-deltas modular sum across every
successful finite same-cell trace. Positive enabledness and symbolic admitted
states cover every old/delta pair. The separate counter-worker profile below
adds locked-add dispatch and lifecycle proofs; native thread lifecycles and
general memory ordering remain external.

Six fetch-add artifact certificates retain raw/full-ELF bindings from the three
compiler modes. Independent native observations check 144 flag pairs and 800,000
contended increments with unique old results per compiler. See the exact
[fetch-add contracts, evidence and limits](fetch-add.md).

## Counted atomic workers

`OS.CounterThreads` implements root-managed spawn, per-instruction dispatch and
join for the exact nineteen-byte JRCXZ/MOV/LOCK-XADD/LOOP/MOV/RET routine. Each
worker holds an actor-specific atomic handle and protected code/stack loans
until join. Full 64-bit entry RCX supplies its iteration request, RDI supplies
the counter address and completed workers return zero. The zero guard avoids
LOOP underflow. Well-formed managed mixed histories preserve private contexts,
resource authority and permanent joined thread/handle/loan revocation.

`dispatch_machine` refines the complete current-memory machine step, including
registers, flags and projected memory. Each recorded event adds one modulo 2^32;
other instructions leave OS cells unchanged. `schedule_remaining` and
`completed_selection_count` prove exactly `3*count.toNat+3` successful own selections through
completion, with arbitrary peer preemption. `completed_event_count` proves
exactly the published iteration count in actual events per completed worker.

For a finite well-formed entry-phase registry targeting one independently
observed address, `completed_counter` proves that every successful supplied
schedule completing all workers leaves initial plus the sum of their published
requests modulo 2^32. `collect_all` returns zeros and removes every worker while
preserving OS cells; `collect_revokes` establishes resource revocation.
`finish_collect_counter` constructs a finite completing schedule and collection
for every such registry. Infinite idle traces remain possible, so arbitrary
scheduler progress and numerical latency are not established.

`CounterCertificate.sound` packages constructive execution and the universal
completed-result contract for exact raw bytes or a complete restricted ELF.
`edsl-certify-counter` runs Lean checking and axiom auditing. Prepared resource
and private-context contracts remain explicit; ELF mode derives code through
modeled loading with freshness and actual shared-space/entry equalities.
The CLI does not infer a native lifecycle, ownership or publication proof.

Owned Lean regressions check all 924 instruction interleavings of two
one-increment workers against independent counter/event/flag/return expectations,
plus zero and unequal iteration workloads. The aggregate sum covers dispatch
schedules followed by checked collection, not arbitrary mixed histories with
unreserved ordinary-store gaps. IDs remain logical authority, batch collection
is a pure operation, and costs exclude runtime/kernel work. Native start/join,
context switching, publication, native locks and general weak
memory remain external. See [counter-worker contracts](counter-workers.md).

The counter-worker and mutex-worker integrations each include four raw/full-ELF
artifact certificates. The counter observer checks 42 sequential requests
and four eight-thread workloads per compiler; it independently rejects four
terminating semantic mutants. The Lean suites include symbolic admission
and completion witnesses for every initial word and pair of 64-bit counts.

## Protected payloads and mutex guards

`OS.Mutex` implements one registered lock word and a protected payload word in
different owned allocations. Registration requires writable contained operands,
an aligned supported lock address, no readers on either allocation, initial
lock zero and an independently chosen invariant on the actual payload. Both
entire allocations stay reserved, even while unlocked. Exact current guards
authorize protected loads/stores; only a successful observed-zero XCHG issues
a fresh guard. Busy and reentrant attempts retain actual 1→1 RMW events.

All admitted mixed histories preserve the resource/lock/holder invariant. The
payload invariant can open while held and must close before successful release.
`exclusive` proves unique authorized identity/actor; `released_for_history`
proves copied guards remain revoked across same-actor reacquisition and
unregister/register cycles. Unrelated allocations and surviving read loans are
framed. `critical_cycle` constructs acquire, arbitrary temporary/restoring
stores and release for every admitted unlocked state and invariant-satisfying
final value, with exact payload readback and revoked guard.

`tryAcquire_exchange32`, `release_exchange32`, `guardLoad_load32` and
`guardStore_store32` connect accepted operations to existing exact XCHG/MOV
compiler bytes and full projected machine results. Invariant/guard checks are
logical admission conditions; the bytes do not implement those checks. The
complete-worker architectural proof below adds client compliance for its fixed
routine. General weak-memory publication, blocking mutexes, fairness and native
runtime/kernel implementation remain open. This wrapper uses `Borrowing.State`
directly and is not an implicit merger with the distinct atomic-worker/handle histories.

Regressions cover wrong/stale guards, same-actor/re-registration reuse, invalid
closing values, contention, reader conflicts, reservations, unrelated resource
changes and denied final operand bytes. Symbolic witnesses cover checked
adoption/registration and finite cycles for arbitrary invariant-satisfying
words. Native checks re-certify nine existing raw artifacts, observe four
eight-thread workloads per compiler mode and reject a safe no-store mutant
against an independent total. Those reused artifacts add no new certificates. See
[the exact mutex scope and theorem contracts](mutex.md).

`OS.MutexReplay` additionally proves complete finite instruction interleavings
of a 37-byte worker, with full projected machine-step refinement, protocol
history composition, exact executable bytes and unchanged peer contexts.
The supplied schedule runs actual busy CMP/JNE retries, two guarded payload
stores and RET. Generic control/guard/payload invariants now prove modular +2
per original worker, zero machine returns and final unlocked invariant for every
completed admitted architectural schedule from an entry cohort, without the
endpoint checker. A credit sum tracks actual stores, and a separate potential proves `13*n + 4*busy`
instructions. Checked spawn establishes the initial cohort invariant and
`ExecutionReady`: current stored code/stack loans, actual executable bytes,
readable return word and canonical return target. Replay preserves their bytes
and permissions. Every existing unfinished worker has an enabled next step.

The separate `OS.MachineThreads` dispatcher selects an existing unreturned
worker and calls only `X86.step` on its private context and full current shared
memory. It has no mutex, phase, guard, loan or expected-code checks. Every
architectural prefix from an admitted state lifts to replay with the same
memory, contexts and events, retaining `Invariant` and `ExecutionReady`.
Completed architectural executions directly expose zero returns, unlocked state,
the modular total and exact instruction count. They admit collection that
revokes precisely the original cohort loans, retains unrelated records and
preserves resource cells.

Completion is constructive from any admitted intermediate state: finishing the
tracked holder first gives no new busy exchanges, exactly `potentialSum`
instructions and a bound of `15*n`. An entry cohort has a zero-busy `13*n`
schedule, attaining the matching lower bound for this fixed routine across
schedules. This does not establish completion for every scheduler or optimality
among alternative programs. Weak-memory/runtime correspondence remains open.

Symbolic adoption/registration/spawn witnesses admit every initial 32-bit word
under the unrestricted predicate. `Examples.MutexExecution` and
`tests/MutexExecution.lean` cover symbolic and paused-prefix completion, actual
contended architectural observations and precise fetch/return-stack faults.
The certifier's `MachineSpecification` includes architectural prefix lifting,
enabledness, completed observations/collection and entry completion; the older
checked-replay contracts remain. Four Clang/GCC raw/full-ELF
artifacts retain their byte bindings with these stronger certificates.
See [worker execution contracts and limitations](mutex-workers.md).

## Buffered machine execution

`OS.TSO` separately executes decoded supported bytes against FIFO store buffers.
Ordinary stores enqueue; ordinary loads forward from the issuing worker's queue.
Independent drains publish oldest writes. Locked XCHG/XADD block until their
own buffer is empty, then perform the existing exact indivisible operation.
RET retains pending stores, and draining returned workers remains possible.
Trace observations distinguish retired instructions, blocked issues and drains.

The buffer algebra proves latest-write forwarding, drain-view invariance,
permission/accessibility preservation, code/stack frames and disjoint-write
commutation. Ownership-derived mutex footprint lemmas establish separation of
payload, lock, executable code and saved return stack. The buffered profile adds
explicit payload alignment and non-executable lock/payload destinations beyond
the prior mutex admission.
Owned regressions exercise the both-zero store-buffer outcome, same-address
forwarding, RET before publication, and FIFO payload publication before a
blocked mutex release.

`OS.MutexTSO` now relates actual pending writes and exclusive guards to the
complete OS replay state. Every successful physical trace lifts to its canonical
retired selections and actual atomic events. Drains and stalls leave the entire
logical state unchanged; busy peer exchanges retire even while the holder
buffers payload. Every actual returning worker has an empty own queue, so all
returns imply quiescence for this routine.

Completed runs establish the modular total, full zero return registers,
unlocked state and `13*n + 4*busy` retired instructions. Checked collection is
constructed, preserves the entire physical memory projection, revokes exactly
the original cohort's loans and retains unrelated records. Current admission
also constructs publication and a completing physical continuation from any
paused prefix, with no new busy exchange or stall and at most `15*n` future
instructions. Entry completion attains `13*n`. Symbolic fixtures admit every
initial word. The generated separate `TSOSpecification` preserves the original
immediate-visibility and checked-replay contracts for the same artifacts.
Queue/credit conservation also proves exactly `2*n` physical drains and
`15*n + 4*busy + blockedCount` model actions for every completing entry trace.
A constructed no-busy/no-stall path attains `15*n` actions. These are abstract
scheduler actions, not hardware micro-operations or timing.
Physical hardware conformance, native identities and runtime refinement remain
open. See [buffered execution](store-buffers.md).

## Concurrent syscall lifecycle

`OS.Suspend` wraps the buffered scheduler with explicit pending invocations.
Actual decoded SYSCALL execution captures the complete userspace request and
continuation, allocates a fresh ID and retires once. Pending callers produce
whole-state parked observations; peers and FIFO drains can continue. Resume
consumes the exact current ID and installs the saved return fields against
current shared RAM, preserving every peer context, returned marker and queue.
The initial syscall profile rejects a nonempty caller FIFO, without flushing it;
peer FIFOs need not be empty.

`X86.ReturnsAt` is additive: the existing synchronous `Returns`/`resume` contract
is unchanged and agrees when current memory is entry memory. Prefix proofs
retain the full memory frame and current pending invariant, including private
contexts and immutable worker indices. A consumed identity cannot resume again
after arbitrary actual peer activity. Completion is available for every valid
pending call and permitted external return choice; infinite parked and idle
traces are also admitted, with no service-progress or fairness promise.

Owned-byte examples and `tests/Suspend.lean` check peer XCHG updates across
resumption, full raw results/private clobbers, return-stack behavior, retained
peer FIFOs and publication, lifecycle failures and real fetch errors. No new
native artifact certificate is added by this syscall wrapper.
Linux services, kernel transitions, native identities and composition with an
ownership/resource world remain separate obligations. See
[the exact boundary](concurrent-syscalls.md).

## Restricted ELF loading

The optional `--elf` path checks complete ELF64 little-endian x86-64 `ET_EXEC`
containers. It validates program headers, file/address bounds, readable supported
permissions, alignment congruence, ordered disjoint page ranges and file-backed
executable entry windows. Exact segment bytes and BSS zeros are installed in the
OS cell model after checking freshness over rounded pages. Existing cells are
preserved. Page padding and Linux process startup are not modeled.

`ELF.checked_entry_code` derives `CodeAt` from a checked initialized entry window.
Generated certificates contain all observed ELF bytes and a checked parser result;
their function theorem includes successful modeled loading and retains caller
freshness, stack/data and return-target conditions. It does not require an input
`CodeAt` premise. See [ELF scope and proofs](elf.md) for caps and unsupported forms.

## Live compiler-output certificates

`edsl-certify` reads a raw function-byte file, accepts only the selected profile's
exact bytes, emits a Lean theorem containing those observed bytes, and runs Lean
with warnings as errors plus transitive axiom auditing. Success requires kernel
checking; native equality-check execution alone is not correctness evidence.

`edsl-certify` is a narrow byte-pattern checker with machine-semantics soundness
theorems. Other correct encodings remain unsupported. It is not yet a general
symbolic executor, invariant generator or arbitrary-contract validator.

`scripts/verify-compilers.sh` builds each owned fixture with Clang C/C++ and GCC
C (twelve combinations), links static function containers, extracts `.text`,
checks certificates and executes certified bytes natively. Independent outcomes
cover arithmetic boundaries, known byte layouts, read-only loads, store/exchange
guard bytes and eight-thread exchange token conservation. Negative checks cover
changed immediates, truncation, trailing/unsupported bytes, empty files and
load/store/exchange contract mismatches. Lean regressions also cover unmapped/denied
operand bytes, atomic alignment restrictions and wrapping/noncanonical operands.

Provenance records compiler versions/arguments, linked ELF metadata/disassembly
and source/artifact hashes. GCC 13 uses `gnu2x`; Clang uses `gnu23`/`gnu++26`.
ELF containers are not standalone process proofs. Linux loader conformance,
relocation and startup remain unverified. Raw-mode `CodeAt` explicitly connects
certified bytes to executed memory; ELF mode derives it for the modeled image.
Binutils, transport, the native driver and physical
OS/hardware remain outside the proof. Hashes aid reproduction; the theorem names
exact bytes. CI preserves only owned fixture artifacts; never put real findings
or confidential material in the upload path.

## Standalone exit process

`edsl-certify-process` accepts a full restricted ELF with the twelve-byte entry
`bf 2a 00 00 00 b8 3c 00 00 00 0f 05`. The certificate derives executable-byte
binding from modeled loading and reaches raw exit60/status42 in exactly three
user instructions, independent of modeled initial registers/flags and without
caller stack/data/runtime requirements. `X86.Invokes` has evaluator soundness,
completeness, request/count determinism and user-divergence exclusion proofs.
The ordinary function evaluator reports `.syscallBoundary`; first-syscall
evaluation reports `.unexpectedReturn` for RET.

`OS.LinuxExit` permits unbounded waiting before completion. All completed admitted
traces have status 42. Eventual completion additionally requires abstract cleanup
progress (`Fair`), which is not inferred from scheduler fairness. Both an admitted
unfair infinite wait and an admitted fair completing trace are proved. The process
interpretation assumes one thread, no interception and no asynchronous interference.

`Exit42.zero_register_lower_bound` proves at least three instructions for any
supported first-syscall candidate requesting exit60/status42 from RAX=RDI=0; the
fixture attains it. It excludes loader/kernel work and says nothing about all-x86
optimality or timing. Full details and remaining kernel/loader/startup boundaries
are in [the process report](process-exit.md).

`scripts/verify-process.sh` certifies Clang/GCC assembly ELFs, then executes the
owned fixtures expecting status42. It rejects wrong-status and wrong-syscall
variants without executing them. Lean regressions independently check immediate
zero-extension, ABI R10 selection, low-bit number/status behavior, instruction
count/fuel and observation boundaries. No concrete Linux exit implementation or
resource cleanup is proved.

## Bounded stream write and exit

`edsl-certify-process write-exit 42` checks the 37-byte entry/code/data window of
a complete ELF at entry `0x400000`. Five user instructions request three bytes
from buffer `0x400022` on descriptor 1; after every admitted write return, three
more request exit60/status42. Initial modeled registers/flags are unrestricted;
no caller stack or runtime is required.

`BufferAt` binds the message to readable bytes derived from loaded executable
data. `LinuxWrite` admits any prefix count including zero or a raw negative
errno, plus arbitrary waiting. `X86.Returns` retains memory and ordinary registers,
sets raw RAX and continuation, and leaves flags/RCX/R11 unconstrained. It is an
external synchronous-write return contract, not privileged instruction semantics.

`Process.ViaWrite` composes both user fragments through a finite write-contract
execution and that return boundary. `viaWrite_results` proves exact user count8,
prefix output of at most three bytes, full output only for accepted count3, and
the exit result/progress conditions. `viaWrite_exists` exhibits an execution for
every permitted partial/error outcome. No write completion, kernel timing or
unconditional process termination is inferred. The stream has one stable sink
with no concurrent writers, descriptor mutation, signal delivery or interference.
Regular files, direct I/O, devices and durability are excluded.

Owned Clang/GCC ELFs are certified before a native C harness checks both a fresh
pipe's exact output and the full nonblocking-pipe failure path with existing
bytes preserved. Changed data/count/descriptor and profile mismatches reject.
Lean tests cover actual request decoding, buffer access, partial/error resume
paths and raw errors. See [the complete contract](process-write.md).

## Reproduce

```sh
lake build EDSL edsl-certify edsl-certify-process edsl-certify-counter edsl-certify-mutex-worker edsl-certify-futex edsl-certify-futex-client edsl-certify-sum32 edsl-cfg-import
lake env lean -DwarningAsError=true tests/X86.lean
lake env lean -DwarningAsError=true tests/Memory.lean
lake env lean -DwarningAsError=true tests/AddressSpace.lean
lake env lean -DwarningAsError=true tests/OSComposition.lean
lake env lean -DwarningAsError=true tests/WordStore.lean
lake env lean -DwarningAsError=true tests/ELF.lean
lake env lean -DwarningAsError=true tests/Process.lean
lake env lean -DwarningAsError=true tests/Write.lean
lake env lean -DwarningAsError=true tests/ControlFlow.lean
lake env lean -DwarningAsError=true tests/Ownership.lean
lake env lean -DwarningAsError=true tests/Borrowing.lean
lake env lean -DwarningAsError=true tests/Threads.lean
lake env lean -DwarningAsError=true tests/AtomicExchange.lean
lake env lean -DwarningAsError=true tests/OSAtomicExchange.lean
lake env lean -DwarningAsError=true tests/Atomics.lean
lake env lean -DwarningAsError=true tests/AtomicThreads.lean
lake env lean -DwarningAsError=true tests/FetchAdd.lean
lake env lean -DwarningAsError=true tests/CounterThreads.lean
lake env lean -DwarningAsError=true tests/CounterThreadsWitness.lean
lake env lean -DwarningAsError=true tests/Mutex.lean
lake env lean -DwarningAsError=true tests/MutexISA.lean
lake env lean -DwarningAsError=true tests/MutexReplay.lean
lake env lean -DwarningAsError=true tests/MutexInvariant.lean
lake env lean -DwarningAsError=true tests/MutexExecution.lean
lake env lean -DwarningAsError=true tests/StoreBuffer.lean
lake env lean -DwarningAsError=true tests/TSO.lean
lake env lean -DwarningAsError=true tests/MutexTSO.lean
lake env lean -DwarningAsError=true tests/Suspend.lean
lake env lean -DwarningAsError=true tests/FutexResources.lean
lake env lean -DwarningAsError=true tests/FutexStubs.lean
lake env lean -DwarningAsError=true tests/FutexService.lean
lake env lean -DwarningAsError=true tests/FutexPhysical.lean
lake env lean -DwarningAsError=true tests/FutexAdmission.lean
lake env lean -DwarningAsError=true tests/FutexClientFrames.lean
lake env lean -DwarningAsError=true tests/FutexClientControl.lean
lake env lean -DwarningAsError=true tests/FutexClientPhysical.lean
lake env lean -DwarningAsError=true tests/FutexClientCertificate.lean
lake env lean -DwarningAsError=true tests/FutexClientCoverage.lean
lake env lean -DwarningAsError=true tests/SequentialISA.lean
lake env lean -DwarningAsError=true tests/SequentialExecution.lean
lake env lean -DwarningAsError=true tests/SequentialMoves.lean
lake env lean -DwarningAsError=true tests/SequentialMoves64.lean
lake env lean -DwarningAsError=true tests/SequentialMoveResources.lean
lake env lean -DwarningAsError=true tests/ArrayResources.lean
lake env lean -DwarningAsError=true tests/Sum32Pointer.lean
lake env lean -DwarningAsError=true tests/Sum32Index.lean
lake env lean -DwarningAsError=true tests/Sum32Artifact.lean
lake env lean -DwarningAsError=true tests/CFG.lean
lake env lean -DwarningAsError=true tests/Stride32.lean
lake env lean -DwarningAsError=true tests/Pair32.lean
lake env lean -DwarningAsError=true tests/Pair32Resources.lean
bash scripts/check-audit.sh
lake env leanchecker --fresh EDSL
bash scripts/verify-compilers.sh
bash scripts/verify-process.sh
bash scripts/verify-loops.sh
bash scripts/verify-fetch-add.sh
bash scripts/verify-counter-workers.sh
bash scripts/verify-mutex.sh
bash scripts/verify-mutex-workers.sh
bash scripts/verify-futex.sh
bash scripts/verify-futex-clients.sh
EDSL_GCC=gcc-13 EDSL_CLANG=clang-18 bash scripts/verify-sum32.sh
EDSL_CLANG=clang-18 bash scripts/verify-sequential-moves.sh
EDSL_CLANG=clang-18 bash scripts/verify-sequential-arithmetic64.sh
EDSL_GCC=gcc-13 bash scripts/verify-cfg.sh
```

Integration needs Linux/x86-64, Clang accepting the named modes, GCC, binutils
and ordinary mmap/mprotect support. The sum32 fixture script selects GCC 13
and Clang 18 with the scalar optimization profiles above and writes to
`artifacts/sum32-fixtures/`. To certify function files:

```sh
lake exe edsl-certify increment FUNCTION.bin artifacts/Increment.lean
lake exe edsl-certify load32 FUNCTION.bin artifacts/Load.lean
lake exe edsl-certify store32 FUNCTION.bin artifacts/Store.lean
lake exe edsl-certify exchange32 FUNCTION.bin artifacts/Exchange.lean
lake exe edsl-certify --elf increment FUNCTION.elf artifacts/ELF.lean
lake exe edsl-certify --elf increment-loop FUNCTION.elf artifacts/ELFLoop.lean
lake exe edsl-certify-process PROCESS.elf artifacts/Process.lean
lake exe edsl-certify-process write-exit 42 PROCESS.elf artifacts/WriteProcess.lean
lake exe edsl-certify-counter WORKER.bin artifacts/CounterRaw.lean
lake exe edsl-certify-counter --elf WORKER.elf artifacts/CounterELF.lean
lake exe edsl-certify-mutex-worker WORKER.bin artifacts/MutexRaw.lean
lake exe edsl-certify-mutex-worker --elf WORKER.elf artifacts/MutexELF.lean
lake exe edsl-certify-futex wait WAIT.bin artifacts/FutexWait.lean
lake exe edsl-certify-futex --elf wake-one WAKE.elf artifacts/FutexWakeELF.lean
lake exe edsl-certify-futex-client publish-payload-wake PUBLISH.bin artifacts/FutexClientRaw.lean
lake exe edsl-certify-futex-client --elf publish-payload-wake PUBLISH.elf artifacts/FutexClientELF.lean
lake exe edsl-certify-sum32 FUNCTION.bin artifacts/Sum32Raw.lean
lake exe edsl-certify-sum32 --elf FUNCTION.elf artifacts/Sum32ELF.lean
lake exe edsl-cfg-import FUNCTION.bin artifacts/CFG.lean
lake exe edsl-cfg-import --elf 35 FUNCTION.elf artifacts/CFGELF.lean
```

For `edsl-certify`, the two-argument form retains the default `increment`
profile. Exit 0 means the emitted certificate checked; exit 3 means unsupported,
not a defect verdict; other nonzero results are failures to certify. Use the successful check result
and exact bytes, not the existence/name of an older certificate file.
The sum32 CLI also distinguishes malformed input (exit 4) from unsupported
code/layout (exit 3); its full status contract is in
[sum32](sum32.md#reproduce-and-rejection-behavior).
`edsl-cfg-import` status 0 means a checked static import, with local functional
and access proofs still required. Its statuses and explicit-span behavior are
documented in [the CFG interface](cfg.md#import-raw-bytes-or-an-explicit-elf-span).

## Private futex adapter

`OS.Futex` binds actual suspended requests to fresh mutable-word pins and a
one-word WAIT_PRIVATE/null-timeout/WAKE_PRIVATE/1 service. Current-word comparison
and enqueue are atomic service actions; every eligible wake choice, internal
retry, spurious readiness and typed resumption have checked contracts. Capture
checks the configured complete lower-userspace interval and non-executable W.
Accepted mixed physical/service prefixes preserve actual call/queue/pin
invariants, full physical/resource RAM equality, managed histories and existing
code/stack loan bytes. Cleanup waits for actual RETs and empty FIFOs and preserves
unlisted records and all identity frontiers.

Exact raw/full-ELF stub certificates separately prove the userspace ABI and
conditional current-RAM RET. Native-linked bytes are compared with the certified
stubs; raw EINVAL/EFAULT observations have no implemented bad-input service
counterpart. The model's tests use actual captured calls and peer machine effects.
Physical replay can explicitly reject executable effects without sufficient
managed authority. The separate `Clients.Admitted` predicate now states current
finite control, actual code and complete eight-byte return-stack loans, current
payload grants, authorization for every queued store, and fixed keeper/producer
handles even when no calls exist. Its preservation is proved from actual
transitions; no field assumes future replay or return success. Actual STORE
decoding derives enqueue authority, including the separate producer which may
return with its FIFO nonempty.

For this fixed WAIT/publisher/peer profile, `issue_lift` and `drain_lift` derive
enabled exact managed execution for every successful actual physical operation.
`MachineTrace.lift` constructs the managed lift of a whole finite physical
issue/drain prefix without a managed-success premise. Current typed service
guards also enable checked extension. An actual ready call enables resumption
and protected decoded RET with full raw RAX, arbitrary full flags/RCX/R11,
current RAM, RSP+8, and exact peer-state preservation. The nonempty checked
`Examples.FutexClient` witness includes distinct return targets and a returned
producer with buffered payload writes.

The publisher's actual STORE/XCHG-one/WAKE1/RET code establishes current payload
publication at XCHG. W=1 persists through later admitted mixed prefixes; current
FIFO authority and keeper separation exclude buffered reset writes, including
returned producers. This proves safety without claiming eventual readiness,
no-lost-wake for all schedules, or payload acquisition.

The new `edsl-certify-futex-client` recognizes exactly this publisher's 32-byte
profile, separately from the invocation-only WAIT/WAKE1 certificates. Literal
raw/full-ELF proofs connect its conditional semantic theorem to a selected
current cohort member's code, same-member XCHG publication and positive return.
The artifact specification also lifts actual finite issue/drain prefixes and
exposes later W=1 preservation. Current admission/member/code binding remains a
premise, not something the CLI constructs from the artifact. The owned native
integration compares the same bytes after final linking and checks current
P/W/raw results; its races and watchdogs supply observations, not scheduling
progress. Safety of a whole Linux kernel or distribution and kernel/runtime
refinement remain outside the claim. See [precise scope](futex.md).
