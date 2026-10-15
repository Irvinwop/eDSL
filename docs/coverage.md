# Implemented coverage and remaining trust

Three exact compiler-output profiles verify unsigned 32-bit increment, load and
store functions. These are usable narrow slices, not a general binary verifier,
complete ISA, source-language frontend, Linux syscall implementation or verified OS.

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
- `C3`: near `ret`, reading an accessible little-endian stack word, checking
  canonical return address, advancing RSP by eight and preserving other state.
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

Only sequential ordinary RAM is modeled. A functional four-byte write is **not
an atomicity or concurrent-visibility theorem**. Concurrent code/data changes,
MMIO, page faults outside this interface and real exception delivery are out of
scope. Misaligned ordinary accesses are admitted under the disabled-alignment-
checking assumption; device-specific constraints are outside this profile.

The ISA definitions are a reviewed subset interpretation of the
[Intel manuals](https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html):
LEA, MOV and near RET in the instruction reference, 32-bit GPR writes/addressing
and alignment checking in the architecture/system reference. Their adequacy to
physical execution remains a model/physical-conformance boundary.

## Checked results

`EDSL.X86.Executes` is an unbounded finite transition closure. Theorems prove
soundness/completeness of the fuelled evaluator against it, deterministic
results/costs, and exclusion of an infinite next-step trace after a proved
terminating execution. The supported machine is deterministic and sequential.

| Profile | Exact bytes | Result for every admitted entry |
| --- | --- | --- |
| `increment` | `8d 47 01 c3` | Zero-extended modular increment of low 32 RDI bits in RAX |
| `load32` | `8b 07 c3` | Four-byte little-endian value at RDI, zero-extended into RAX |
| `store32` | `89 37 c3` | Low 32 RSI bits stored little-endian at RDI |

Every profile returns in exactly two modeled instructions, has no infinite
next-step execution, and has a unique completed result/count. RSP advances by
eight and RIP becomes the stack return address. Modeled flags and unrelated
registers are preserved. Increment/load preserve all memory; store preserves
permissions and bytes outside its four-byte footprint, with a readback theorem.

All profiles require exact executable bytes, a readable eight-byte return stack
and a canonical return target. Load additionally requires a successful data read.
Store requires mapped/writable data and disjointness from code and the return
stack, so the write cannot invalidate the next instruction or return address.
Nonempty entry witnesses cover every 32-bit load value and every old word/64-bit
store argument, as well as every increment input.

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
witnesses. These are still sequential byte-cell updates, not physical page,
aliasing, resource-identity or concurrent-atomicity proofs.

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

This is a narrow byte-pattern checker with machine-semantics soundness theorems.
Other correct encodings remain unsupported. It is not yet a general symbolic
executor, invariant generator or arbitrary-contract validator.

`scripts/verify-compilers.sh` builds each owned fixture with Clang C/C++ and GCC
C (nine combinations), links static function containers, extracts `.text`,
checks certificates and executes certified bytes natively. Independent outcomes
cover arithmetic boundaries, known byte layouts, read-only loads and store guard
bytes. Negative checks cover changed immediates, truncation, trailing/unsupported
bytes, empty files and load/store contract mismatches. Lean regressions also
cover unmapped/denied store bytes and wrapping/noncanonical operands.

Provenance records compiler versions/arguments, linked ELF metadata/disassembly
and source/artifact hashes. GCC 13 uses `gnu2x`; Clang uses `gnu23`/`gnu++26`.
ELF containers are not standalone process proofs. Linux loader conformance,
relocation and startup remain unverified. Raw-mode `CodeAt` explicitly connects
certified bytes to executed memory; ELF mode derives it for the modeled image.
Binutils, transport, the native driver and physical
OS/hardware remain outside the proof. Hashes aid reproduction; the theorem names
exact bytes. CI preserves only owned fixture artifacts; never put real findings
or confidential material in the upload path.

## Reproduce

```sh
lake build EDSL edsl-certify
lake env lean -DwarningAsError=true tests/X86.lean
lake env lean -DwarningAsError=true tests/Memory.lean
lake env lean -DwarningAsError=true tests/AddressSpace.lean
lake env lean -DwarningAsError=true tests/OSComposition.lean
lake env lean -DwarningAsError=true tests/WordStore.lean
lake env lean -DwarningAsError=true tests/ELF.lean
bash scripts/check-audit.sh
lake env leanchecker --fresh EDSL
bash scripts/verify-compilers.sh
```

Integration needs Linux/x86-64, Clang accepting the named modes, GCC, binutils
and ordinary mmap/mprotect support. To certify raw function files:

```sh
lake exe edsl-certify increment FUNCTION.bin artifacts/Increment.lean
lake exe edsl-certify load32 FUNCTION.bin artifacts/Load.lean
lake exe edsl-certify store32 FUNCTION.bin artifacts/Store.lean
lake exe edsl-certify --elf increment FUNCTION.elf artifacts/ELF.lean
```

The two-argument form retains the default `increment` profile. Exit 0 means the
emitted certificate checked; exit 3 means unsupported, not a defect verdict;
other nonzero results are failures to certify. Use the successful check result
and exact bytes, not the existence/name of an older certificate file.
