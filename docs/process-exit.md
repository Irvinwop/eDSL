# A standalone process with an explicit exit contract

`edsl-certify-process` checks one complete ELF entry profile:

```asm
mov edi, 42
mov eax, 60
syscall
```

The twelve entry bytes are `bf 2a 00 00 00 b8 3c 00 00 00 0f 05`.
The specification is a raw exit request with observable status 42. The Lean
proof connects the complete observed ELF, modeled loading, execution of these
bytes, the syscall register convention and an explicit OS exit contract.

## What is checked

The certificate embeds every observed file byte and checks `Process.checkExit42`
using ordinary kernel reduction. This establishes the restricted
[ELF loader](elf.md) result and executable entry binding. The generated
`certified` theorem applies `Process.exit42_standalone` to every modeled initial
register/flags state, starting with an empty OS address space.

No caller return address, stack bytes, data mapping or runtime is needed by this
entry. Existing machine-control and physical-conformance assumptions still
apply: arbitrary modeled flags do not admit physical debug traps, privileged
control configurations or asynchronous interference.

`X86.Invokes` is the unbounded finite execution relation to the first syscall
request. The fuelled evaluator is proved sound and complete for that relation.
`Exit42.reaches_request` establishes a unique request and count, exactly three
user instructions including SYSCALL, and excludes infinite ordinary user-step
execution. The count excludes loading, kernel work and waiting.

`Exit42.zero_register_lower_bound` proves that every successful candidate in the
currently supported ISA starting with RAX=RDI=0 and invoking raw exit60/status42
needs at least three user instructions. Each ordinary supported instruction
preserves at least one of RAX/RDI, and the final syscall adds a step. The fixture
attains that bound. This is a restricted candidate-class result, not an all-x86
minimum, micro-op count or elapsed-time bound.

## Where the OS contract starts

`SyscallRequest` retains the userspace state immediately before privileged
execution plus the next instruction address. Its Linux x86-64 ABI projection
uses the low 32 RAX bits as the syscall number, and arguments in RDI, RSI, RDX,
R10, R8 and R9. It is not a kernel entry-state model: MSRs, privilege changes,
RCX/R11 clobbers and SYSRET are outside this boundary.

`OS.LinuxExit` admits number 60 and observes the low eight argument bits.
Linux's [pinned syscall table](https://github.com/torvalds/linux/blob/v6.12/arch/x86/entry/syscalls/syscall_64.tbl)
distinguishes raw exit60 from exit_group231. The raw exit implementation masks
the status in [Linux 6.12](https://github.com/torvalds/linux/blob/v6.12/kernel/exit.c).
The [exit manual](https://man7.org/linux/man-pages/man2/_exit.2.html)
explains the raw calling-thread behavior and the libc wrapper distinction.
The process interpretation here requires exactly one thread, no interception,
and no asynchronous termination or other interference.

The contract allows any number of waiting transitions followed by completion,
then terminal observation stuttering. It establishes two separate facts:

- Every completed admitted trace has status 42.
- Every admitted trace satisfying `Fair` eventually completes with status 42.

`Fair` is an **abstract completion-progress assumption**. It is stronger than
ordinary CPU scheduler fairness when resource cleanup can block. It does not
prove that Linux cleanup completes, or put a numerical bound on its duration.
`indefinite_wait` proves that the contract also admits infinite waiting without
that assumption. `immediate_admitted` proves the fair contract has an execution,
so its termination statement is not vacuous.

No concrete kernel instructions, descriptor cleanup, resource revocation,
signals, seccomp/ptrace policy or Linux loader implementation have been verified.
The model installs exact segment intervals and BSS while leaving page padding
unmapped. It does not establish a full Linux startup stack/auxv/TLS contract.
The separate [bounded stream-write profile](process-write.md) handles one
synchronous output request with partial/error outcomes; broader I/O, threads,
locks and atomics remain required future work. This profile demonstrates checked
composition across the current boundaries rather than discharging those remaining
contracts.

## Reproduce

```sh
lake build EDSL edsl-certify-process
lake env lean -DwarningAsError=true tests/Process.lean
bash scripts/verify-process.sh
lake exe edsl-certify-process PROCESS.elf artifacts/Process.lean
```

Integration requires Linux/x86-64, Clang, GCC, GNU binutils and `timeout`.
The script assembles the project's owned fixture with both compilers, links each
ELF, checks its full-file certificate and then executes it expecting native
status 42. Changed-status and changed-syscall variants must reject and are never
executed. Native observations help detect model/interface mistakes but do not
prove kernel or hardware conformance. Certificates and provenance stay under
ignored `artifacts/process-fixtures/`; CI uploads only these owned fixtures.

Exit 0 means the generated Lean certificate checked and passed the axiom audit.
Exit 3 means unsupported or mismatched input, with no defect conclusion. Other
nonzero results mean failure to certify. A stale output path from a prior run
is not evidence that a new invocation succeeded.
