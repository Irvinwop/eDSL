# Locked fetch-add and modular counters

The `fetch-add32` certificate profile accepts exactly
`89 f0 f0 0f c1 07 c3`: MOV EAX,ESI; LOCK XADD DWORD PTR [RDI],EAX; RET.
It returns the previous 32-bit destination in zero-extended RAX and installs
`old + low32(RSI)` modulo 2^32, in three user instructions. An explicit singleton
RMW event retains the actual old and new words. This is direct verification of
final bytes against an independent arithmetic contract, without a source or
compiler-correctness assumption.

## Machine and arithmetic contracts

`X86.fetchAddDWord` is one indivisible checked operation on the existing aligned,
canonical, coherent-WB-RAM profile. It requires the complete four-byte operand
to be readable and writable; permissions and cells outside that footprint are
preserved. It rejects unsupported addresses and denied bytes. The decoder accepts
only the stated locked 32-bit encoding; unlocked, 16/64-bit, alternate-register,
extra-prefix and truncated encodings are unsupported.

`X86.addFlags32` writes CF, PF, AF, ZF, SF and OF from the addition result.
CF and OF use Lean's mathematical unsigned/signed overflow predicates; AF is
carry from bit 3, PF is even parity of the low result byte, ZF tests the full
32-bit result and SF observes bit 31. `addFlags32_bits`, `addFlags32_carry`,
`addFlags32_overflow` and `addFlags32_preserves` prove the bit positions,
arithmetic interpretations and preservation of every other abstract flag bit.
These proofs use ordinary kernel-checked Boolean/bitvector reasoning, with no
project axioms or unchecked solver results. This remains an abstract flag word,
not a complete model of debug/privilege/exception transitions.

`executeFetchAdd_sound` and `step_fetchAdd_sound` connect the memory operation,
actual old result, arithmetic flags and four-byte RIP advance. The older
`step_atomic_sound` is XCHG-specific and now requires its decoded instruction
as a premise; atomic steps no longer universally preserve flags or advance two
bytes. Existing global supported-ISA execution and cost bounds were rebuilt
with the additional instruction.

`Examples.Compiler.FetchAdd.correct` proves the exact complete routine's
singleton event, three-instruction execution, termination, unique result/count,
return-stack behavior and final state. Its hypotheses explicitly require exact
code, atomic/writable data, an independently observed old word, disjoint code
and return-stack footprints, a readable return address and canonical target.
`value_and_frame` states old-value return, final sum, flags and byte framing.

## OS resources and counter histories

`OS.Atomics.fetchAdd` uses the caller's stored actor handle and current shared
cells, then performs the checked modular update as one pure operation. Its
implementation projects to an existing guarded exchange history; there is no
exposed load/store interval between reading the old word and installing its sum.
It retains allocation reservations, read-loan exclusion, authority validation
and the existing history guarantees. `fetchAdd_wellFormed`, `fetchAdd_history`
and `fetchAdd_enabled` establish invariant preservation, composition and positive
operation paths under their explicit premises.

`fetchAdd_step` proves the actual locked XADD step implements the checked resource
operation. `fetchAdd32_updates_space` composes the complete compiler routine with
the OS update, including an explicit equality between final machine memory and
projected OS cells.

`AddTrace.counter` covers arbitrary finite successful same-address fetch-add
traces from an independently observed initial word. The final word is the initial
value plus every recorded delta, modulo 2^32. Each trace constructor names the
actual actor, handle, delta and returned old word; it requires successful checked
execution and matching handle address. `AddTrace.history` projects into managed
resource histories. This result has no fixed operation-count bound and makes no
scheduling or native thread-lifecycle assumption.

It does not admit unrecorded external stores or arbitrary administrative actions.
It does not itself establish natural-number counting without overflow,
fairness or native pthread/clone refinement. The separate
[`CounterThreads` worker protocol](counter-workers.md) now schedules an exact
locked-add increment loop, proves published per-worker iteration counts and
the whole-workload modular total, and provides checked completion/collection.
`AtomicThreads` retains its distinct exchange routine and old-value results.

## Evidence

```sh
lake build EDSL edsl-certify edsl-certify-process
lake env lean -DwarningAsError=true tests/FetchAdd.lean
bash scripts/verify-fetch-add.sh
bash scripts/check-audit.sh
lake env leanchecker --fresh EDSL
```

Owned Lean cases independently check signed overflow, carry/zero wraparound,
auxiliary carry, parity, preserved nonstatus bits, high source bits, stack/return
state, neighboring bytes, complete operand permissions, wrong actors and guarded
resource mutation. `every_input_executes` constructs a complete actual-byte
execution for every initial 32-bit word and full 64-bit source argument.
Symbolic checked-allocation/issuance witnesses separately cover every initial
word and delta in the OS operation.

Clang GNU23, Clang GNU++26 and GCC GNU2x produce six raw/full-ELF certificates.
A native assembly shim captures flags immediately after the certified routine
returns. Its 144 boundary-input pairs per compiler generate Lean checks whose
expected flags come from hardware, with no duplicate flag formula in the probe.
Eight native threads perform 800,000 increments per compiler; a separate atomic
bitmap checks every returned old value occurs exactly once, the final counter
is 800,000 and an adjacent guard survives. These observations supplement model
proofs; they do not establish physical CPU or general memory-model conformance.
Synthetic unlocked, wrong-width, exchange and truncated artifacts are rejected;
a native width mutant must also fail the independent result checks.

The semantic reference is Intel's [instruction-set manual, XADD, Vol. 2D 6-23](https://cdrdv2-public.intel.com/782156/325383-sdm-vol-2abcd.pdf).
Physical locked-operation ordering, translation stability, mixed-size overlaps,
unmanaged aliases and C/C++ memory-model preservation retain the existing
[atomic profile's assumptions](atomic-exchange.md).
