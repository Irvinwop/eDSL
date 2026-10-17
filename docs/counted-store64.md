# Counted stores with evolving ownership

`EDSL.CountedStore64` verifies one exact GCC13 GNU C23 (`gnu2x`) `-Os`
function against an independent mathematical contract. RDI points to eight
owned writable bytes, RSI supplies a full64 argument, and RDX supplies a
full64 count. Every admitted count, including zero and `2^64-1`, terminates
in the sequential model. RAX returns `argument + count` modulo `2^64`.
Zero count retains the old target value; positive counts leave the returned
value in the target.

The postcondition also preserves every byte outside the target, both complete
permission maps, the SysV callee-saved registers and all nonarithmetic flags.
An actual RET reads the original eight-byte caller slot, checks the return
address and advances RSP by eight. Admission supplies current code, readable
and writable target bytes, a disjoint caller slot and their nonwrapping and
canonical-address facts. It contains no decoder success, future execution,
ranking certificate or successful ownership mutation.

The exact 20 bytes are:

```text
48 89 f0 48 85 d2 74 0b 48 ff c0 48 ff ca 48 89 07 eb f0 c3
```

They copy RSI to RAX, test RDX, exit on zero, increment RAX, decrement RDX,
store RAX through RDI, jump back to the test and return. The owned fixture
uses a volatile target and an explicit empty GNU asm count-register barrier.
The theorem verifies final bytes; it establishes no C/volatile/asm semantics
or source-to-binary preservation. Other compiler configurations and instruction
shapes remain unsupported by this convenience checker.

`GCC.raw_semantics` proves all-input, all-AF termination and `Post`.
`GCC.raw_policy` proves that actual prefixes fetch inside the admitted code,
write only the eight-byte target and read only the original caller slot.
`GCC.resource_semantics` additionally establishes a coherent current OS policy
and `ResourceReturn`. Every actual store uses the checked `Borrowing.store64`
mutation in the same evolved world. The returned world retains allocation
identities, owners and epochs, original loans and contents, all permissions,
outside cells and full machine RAM coupling. It can perform another checked
full64 store with an arbitrary next value.

The header invariant partitions the natural full64 count into completed
iterations and remaining RDX. It tracks the pending increment and decrement
separately from the completed store. The rank depends only on the actual
machine state: RDX's natural value, plus one at entry. Positive DEC strictly
decreases this value without modular underflow. No bound on the low32 count
or practical execution duration restricts admission.

`Grading.Trace.ResourceCutpoints.Certificate` is the reusable composition
layer. Local obligations require actual decoding, every AF choice, successful
authorized operand reads, registered effects and the same evolved ghost world
at the next node. Machine erasure supplies termination through the existing
cutpoint theorem; a separate policy proof retains the world on actual paths.
Ranks depending on ghost resources, atomic instructions and syscall outcomes
are outside this interface. The read-only CFG discovery/checker remains
unchanged and rejects stores; this instance supplies a direct layout.

The conservative instruction bound is `7 * (count.toNat + 2)`, including RET.
It is separate from the functional contract. Exact instruction/store counts,
minimum operations, concurrent visibility, timing and source preservation are
not established. Physical interpretation uses the existing ordinary-RAM
[machine assumptions](coverage.md#supported-machine-profile), including
stable code/data, disabled alignment checking/CET and no asynchronous changes.
This does not verify the implementation of Linux or another whole OS.

Run:

```sh
lake build edsl-certify-counted-store64
lake env lean -DwarningAsError=true tests/CountedStore64.lean
EDSL_GCC=gcc-13 bash scripts/verify-counted-store64.sh
lake env .lake/build/bin/edsl-certify-counted-store64 INPUT.bin CERTIFICATE.lean
lake env .lake/build/bin/edsl-certify-counted-store64 --elf INPUT.elf CERTIFICATE.lean
```

The CLI binds the literal raw file or restricted ELF and entry bytes, then
kernel-checks the generated all-input result/resource theorems and their
transitive axiom audit. ELF output also establishes the loaded-code theorem
and a callable result with explicit loader/caller facts. Status codes follow
the other direct certifiers: 0 certified, 1 proof failure, 2 usage, 3
unsupported, 4 malformed and 5 I/O failure. A stale output file does not
establish certification. The fixed-contract grader registry is unchanged.

The integration script compiles and links the owned fixture, checks both
generated certificates, and executes its exact extracted bytes through an
external SysV observer. A closed-form oracle checks 504 calls covering seven
full64 arguments, six practical counts, six aligned/unaligned/page-edge
targets above 4GiB and two old values, with complete data-page frames. Six
owned mutants test missing/narrow stores, incorrect iteration count/value,
neighbor writes and ABI damage. Timeout and unsupported analysis establish
no defect. Separate Lean regressions cover zero retention, high-half-only and
maximum counts, arbitrary frames, returned authority, and an admitted real
MOV EDX,EDX count-truncation counterexample.
