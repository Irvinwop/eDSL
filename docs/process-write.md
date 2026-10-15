# A bounded stream write followed by exit

`edsl-certify-process write-exit42` checks a complete restricted ELF whose entry
requests a three-byte write of `OK\n` to descriptor 1, then requests raw exit60
with status42. The proof covers every outcome permitted by the explicit stream
contract, including short writes, zero bytes accepted and raw negative errors.
It promises the whole message only when the write accepts all three bytes.

The entry has four MOV-immediate instructions and SYSCALL, followed by the
checked [exit42 entry](process-exit.md). The three message bytes follow that code
in the same file-backed executable segment. Current encodings use an absolute
32-bit buffer address, so this profile requires ELF entry `0x400000` and buffer
address `0x400022`. Its checked window is 37 bytes. It needs no startup stack,
caller return address, external runtime or initial register values.

## Proof composition

`WriteExit.reaches_write` proves the unique first request in five user
instructions and excludes infinite ordinary user execution before it.
`CodeAt.window` derives executable subranges without losing the nonwrapping
bound. `CodeAt.readable` then establishes `BufferAt` for the actual message
address. Buffer binding comes from modeled ELF loading of the observed file,
not an assertion about a separate source string or section extraction.

`LinuxWrite` supplies a deliberately restricted stream contract:

- Raw syscall number 1, an exactly bound byte count of at most 4096, and
  caller-supplied readable buffer and descriptor obligations.
- Any accepted count from zero through the payload length, or a positive errno
  from 1 through 4095 encoded as a negative 64-bit result.
- Completed accepted output is the corresponding byte prefix. In the admitted
  stream profile an error accepts no bytes. No full-transfer assumption is made.
- Arbitrary waiting before completion; every permitted outcome has an admitted
  completing trace, and an infinite waiting trace is also admitted.

Linux documents short transfers and interruption/error cases in
[`write(2)`](https://man7.org/linux/man-pages/man2/write.2.html). The raw result
encoding is distinct from the libc wrapper's `-1` plus `errno`; the model proves
the signed encoding for the entire admitted errno range. The x86-64 dispatch
number is pinned against the
[Linux 6.12 table](https://github.com/torvalds/linux/blob/v6.12/arch/x86/entry/syscalls/syscall_64.tbl).

`X86.Returns` is an external return-to-userspace contract. For this synchronous
write it retains userspace memory, returns the raw result in RAX and resumes at
the saved continuation. Other registers are preserved except RCX/R11; those
two registers and flags are unconstrained. `resume_returns` constructs a witness
for every raw value and every choice of the unconstrained state. No privileged
entry/return instructions or kernel implementation are proved by this contract.

`Process.ViaWrite` joins first-syscall execution, an admitted finite write
execution, that return contract and subsequent first-syscall execution.
`viaWrite_results` proves every such execution has exactly eight user
instructions, prefix output of at most three bytes, and an exit60 request with
status42. It proves full output separately for the accepted-three case.
`viaWrite_exists` supplies an execution for every permitted write outcome,
including errors, without requiring a mapped stack. The proof does not assume
particular return flags, RCX or R11 values to execute the exit suffix.

`Process.writeExit_standalone` composes these results with full-file ELF checking
and loading. For completed final exit-contract traces, status is 42; eventual
exit additionally requires the explicit completion-progress assumption described
in the [exit report](process-exit.md). The eight-instruction count is conditional
on write completion and excludes kernel work, waiting and loading. It is not an
unconditional process-termination or elapsed-time bound.

## Environment and limits

The descriptor denotes one externally owned stable byte-stream sink, with no
concurrent writers, descriptor replacement, buffer mutation or asynchronous
interference. The observation records accepted bytes after return. It does not
model their intermediate visibility or claim that the real write is atomic.
The return contract preserves userspace memory for this operation; it is not
a specification for arbitrary syscalls that modify user buffers.

Regular-file offsets/append races, direct I/O, devices, durability, descriptor
lookup/lifetime, signal delivery, SIGPIPE termination, cancellation and concrete
kernel resource behavior remain outside this profile. In particular, a generic
direct-I/O error need not imply that storage is unchanged. This restricted
stream assumption must not be exported as a theorem about every write target.
The current model does not retry a short transfer or an interrupted write.

The ELF and machine-control/physical-conformance limitations in
[coverage](coverage.md) still apply. All modeled initial flags values are
admitted mathematically; physical debug/privilege exceptions and asynchronous
changes are excluded by that platform contract.

## Evidence and reproduction

```sh
lake build EDSL edsl-certify-process
lake env lean -DwarningAsError=true tests/Write.lean
bash scripts/verify-process.sh
lake exe edsl-certify-process write-exit42 PROCESS.elf artifacts/WriteProcess.lean
```

The owned assembly fixture is assembled with Clang and GCC. Each exact linked
ELF gets a Lean certificate before native execution. A C harness executes it
with stdout bound to a fresh pipe and independently expects exactly `OK\n` plus
status42. A second case fills a nonblocking pipe, leaves its reader idle until
the child exits, and checks status42 with every preexisting byte preserved.
This exercises an actual unavailable-capacity write path. It does not observe
the child's overwritten RAX or prove universal kernel conformance.

Lean regressions exercise actual byte decoding, the fourth immediate destination,
buffer addressing, short/error returns followed by exit, raw errno encoding,
oversized-result rejection and unconstrained return state. Wrong message bytes,
count, descriptor and selected process contracts must reject in integration;
none of those negative ELFs is executed. Native partial success is not claimed
from the three-byte pipe fixture: the Lean theorem covers it under the contract.
All artifacts are owned fixtures stored under ignored `artifacts/process-fixtures/`.
