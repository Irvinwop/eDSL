# Complete mutex worker replay

`EDSL.OS.MutexReplay` checks finite instruction interleavings of an owned
37-byte x86-64 worker. The lock address is in RDI, the protected payload address
in RSI, and each worker requests a modular 32-bit increase of two:

```asm
retry:
    mov eax, 1
    xchg DWORD PTR [rdi], eax
    cmp eax, 0
    jne retry
    mov eax, DWORD PTR [rsi]
    lea eax, [rax + 1]
    mov DWORD PTR [rsi], eax
    lea eax, [rax + 1]
    mov DWORD PTR [rsi], eax
    mov eax, 0
    xchg DWORD PTR [rdi], eax
    mov eax, 0
    ret
```

The two stores deliberately allow an even payload invariant to be open while
the holder runs. A peer can attempt acquisition during that interval. Its
actual busy XCHG writes 1 over 1, returns the old word, changes CMP flags, and
branches back. The holder's guard is recorded at the successful XCHG, before
CMP or the branch. Release checks the actual payload invariant and revokes it.

## Implemented guarantee

`perform_refines` connects every successful admitted operation to one complete
`X86.step` result, including registers, flags, RIP, the RMW event, and the
entire memory projected from the resulting OS cells. It has no assumed machine
result premise. `dispatch_refines` also retains executable-byte binding and
unchanged peer contexts. `schedule_trace` composes those steps in the supplied
order; every dispatch projects current shared memory afresh.

`verify` requires a cohort at entry and an unlocked mutex, runs a supplied
finite schedule, and checks an independent endpoint:

- Every original worker has completed its actual RET with RAX zero and no guard.
- The original lock address contains zero and the registration is unheld.
- The original payload address contains `initial + 2 * workers` modulo 2^32.
- The original payload invariant holds on that final value.

`verify_sound` proves that successful validation establishes that endpoint and
the complete instruction trace. It is a checked finite execution certificate.
**It does not prove the endpoint for every completing schedule without running
the endpoint check.** Generic preservation of worker-private invariants,
symbolic completion, schedule-independent totals and enabledness are further
work. A rejected schedule or failing invariant is not a security finding.

Every accepted trace also projects to `Mutex.History`. From an initially
well-formed mutex/resource state, its final mutex/resource state is well formed.
The existing history theorems preserve live read loans and permanently revoke
released guards. The replay layer has no transitions for raw stores, external
guard release, unregister, arbitrary loan completion, or replacement OS state.

## Cohort and resources

`spawn` appends an immutable logical worker index, with principal `index + 1`.
It checks exact code, RDI/RSI operands, actual readable return stack and canonical
return address, then borrows executable code and stack allocations through the
mutex protocol. Workers can share read-only code and return-stack storage.
Creation is restricted to the pre-execution phase; nested spawn, detach and
individual join are unsupported.

`collect` requires the complete cohort, returns retained machine RAX values,
and closes its internal code/stack loans. Collection preserves all resource
cells and the mutex registration. Generic successful collection theorems prove
zero returns and well-formedness from the replayed resource contract. The
concrete handoff test also observes that code mutation is denied before
collection and enabled afterward.

The logical actor mapping is not authenticated pthread/kernel identity.
External users must supply initial ownership/registration and cannot interpret
an arbitrary hand-constructed state as a proved setup. The Lean fixture uses
actual checked adoption, registration and spawn operations.

## Artifacts and validation

`edsl-certify-mutex-worker [--elf] INPUT CERTIFICATE.lean` admits exactly this
worker. Generated certificates embed observed bytes, apply the validator's
soundness theorem, and run the axiom audit. ELF certificates additionally embed
the full file, prove parsing, check the executable entry window, and expose
fresh-loading/code-binding theorems. The CLI certifies the artifact profile;
a specific execution additionally needs a checked schedule. It does not claim
that the linked ELF is a standalone process or verify its start/runtime code.

```sh
lake build edsl-certify-mutex-worker
lake env lean -DwarningAsError=true tests/MutexISA.lean
lake env lean -DwarningAsError=true tests/MutexReplay.lean
bash scripts/verify-mutex-workers.sh
```

The owned assembly is assembled independently by Clang and GCC. Raw and full-ELF
certificates add four distinct artifacts. Native C observers execute both raw
artifacts across sequential wraparound cases and eight-thread workloads, checking
the public +2 contract, zero returns, unlocked final lock and adjacent guards.
They do not reconstruct or certify the observed native scheduler trace.
Four safe terminating semantic mutants independently fail those observations;
byte-profile checks also reject changed control flow, release and truncation.

The two-worker Lean regression executes 30 actual instructions, including one
busy retry and five RMW events. It observes the intermediate odd protected word,
the busy peer's retry, wraparound from `0xfffffffe` to 2, real stack returns,
loan pinning and reclamation. Partial schedules remain unverified.

The listing has 13 uncontended instructions, with four per failed attempt.
This count is descriptive here: there is no new generic cost or minimum-ops
theorem. Cycles, micro-ops, fairness, blocking/futex behavior and bounded waiting
are outside this model.

## Physical boundary

This remains the existing sequentially interleaved coherent-RAM profile. It
does not implement a store-buffer/weak-memory model, native client compliance,
pthread start/join, the Linux kernel, interrupts or exceptions. XCHG's physical
interpretation requires the [atomic profile](atomic-exchange.md). The guarded
invariant and ownership checks are admission conditions; these bytes do not
execute those checks. CMP/JNZ semantics follow the
[Intel instruction reference](https://cdrdv2-public.intel.com/868140/253666-089-sdm-vol-2a.pdf).
