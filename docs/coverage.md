# Implemented coverage and remaining trust

The first concrete artifact profile verifies a compiler-generated unsigned
32-bit increment function. This is a usable narrow slice, not a general binary
verifier, complete ISA, source-language frontend, Linux model or verified OS.

## Supported machine profile

- x86-64 long-mode userspace, flat addressing and the 48-bit canonical-address
  profile. The physical interpretation requires valid architectural control
  state, no single-step/breakpoint interference, CET disabled and no asynchronous
  state changes during the modeled call. These facilities are not modeled.
- `8D 47 ib`: `lea eax, [rdi + signed_disp8]`, using 64-bit address calculation,
  a 32-bit destination and zero extension of EAX into RAX. Flags are preserved.
- `C3`: near `ret`, reading an accessible little-endian stack word, checking
  canonical return address, advancing RSP by eight and preserving other state.
- A memory interface with explicit accessible bytes and execute permission.
  Mapping the interface to real page tables/OS permissions is an assumption.
  Ordinary immutable code/stack data is used; concurrent modification, MMIO,
  faults outside this interface and real exception delivery are out of scope.
- Checked executable-byte binding and a nonwrapping code range. Invalid fetch,
  unavailable stack data, unsupported encodings and noncanonical returns produce
  explicit errors. A decode rejection is not automatically a hardware fault.

The ISA definitions are a reviewed subset interpretation of the
[Intel manuals](https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html):
LEA and near RET in the instruction reference, 32-bit GPR writes and addressing
in the architecture reference. Their adequacy to physical execution remains a
model/physical-conformance boundary, not a theorem about Intel silicon.

## Checked results

`EDSL.X86.Executes` is an unbounded finite transition closure. Theorems prove
soundness/completeness of the fuelled evaluator against it, deterministic
results/costs, and exclusion of an infinite next-step trace after a proved
terminating execution. This is not bounded exploration presented as unbounded
concurrency verification; the supported machine is deterministic and sequential.

For exact bytes `8d 47 01 c3`, the library proves for every admitted register,
flags, code/stack state and return address:

- RAX becomes the zero-extended 32-bit modular increment of the low 32 bits of
  the initial RDI, including wraparound and arbitrary upper RDI bits.
- RSP advances by eight, RIP becomes the stack return address, and all other
  registers, memory and modeled flags retain their initial values.
- The function returns in exactly two modeled instructions, has no infinite
  next-step execution, and every completed modeled execution has that result.
- Entry conditions have a concrete witness for every input, avoiding an empty
  admitted-state argument.
- Every successful execution in this supported instruction subset that changes
  RAX needs at least two instructions. An increment implementation on zero input
  and zero initial RAX therefore needs two; the fixture attains that bound.
  This is an instruction-subset bound, not an all-x86 or CPU-time optimum.

## Live compiler-output certificates

The `edsl-certify` Lean executable reads a raw function-byte file. Its first
profile accepts exactly the four bytes above, emits a Lean theorem containing
those observed bytes, and runs Lean with warnings as errors plus the transitive
axiom audit. Success requires kernel checking; native execution of the equality
checker is not by itself the correctness evidence.

This is an intentionally narrow byte-pattern checker with a machine-semantics
soundness theorem. Other correct encodings are unsupported. It is not yet a
general symbolic executor, invariant generator or arbitrary-contract validator.

`scripts/verify-compilers.sh` builds owned C/C++ fixtures with Clang and a C
fixture with GCC, links each into a static function container, extracts its
`.text` bytes, generates/checks the certificate and executes the certified
bytes on the native host for independent boundary outcomes. It records compiler
versions, arguments, linked ELF metadata/disassembly and source/artifact hashes.
GCC 13 uses `gnu2x`; Clang uses exact `gnu23`/`gnu++26` modes.

The ELF here is a function container, not a standalone process proof. ELF
parsing, relocation/loading and Linux startup are not formally verified yet.
`CodeAt` is the explicit premise connecting the certified byte snapshot to the
memory actually executed. Binutils, file transport, the native driver and the
physical OS/hardware are not silently added as proved components. Hashes aid
identity/reproduction; the theorem itself names exact bytes.

CI preserves only owned fixture artifacts. Never use that upload path for real
security findings or third-party confidential material.

## Reproduce

```sh
lake build EDSL edsl-certify
lake env lean -DwarningAsError=true tests/X86.lean
bash scripts/check-audit.sh
lake env leanchecker --fresh EDSL
bash scripts/verify-compilers.sh
```

The integration script currently needs Linux/x86-64, Clang accepting the named
modes, GCC, binutils and ordinary mmap/mprotect support. To certify a raw file:

```sh
lake exe edsl-certify FUNCTION.bin artifacts/Certificate.lean
```

Exit 0 means the emitted certificate checked; exit 3 means unsupported by this
profile, not a defect verdict; other nonzero results are failures to certify.
Consumers must use the successful check result and exact observed bytes, not
the existence/name of an older certificate file.
