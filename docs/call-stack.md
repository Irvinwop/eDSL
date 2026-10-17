# Owned nested calls

The additive `X86.CallReturn` machine supports direct `E8 rel32` CALL, full64
register PUSH/POP and REX.W LEA with a signed byte displacement. It embeds the
existing sequential instructions without extending that decoder or its graders.
`OS.StackFrame.CPU` connects actual instructions to checked ownership mutations
and reads. `tests.fixtures.CallStack.Correctness` proves four whole linked GNU23
compiler outputs against the same independent unsigned `(input + 2) mod 2^64`
contract, for every 64-bit input and undefined-AF stream.

| Compiler/layout | Whole text bytes | Caller entry offset | Retired instructions |
| --- | ---: | ---: | ---: |
| GCC 13, same translation unit | 14 | 5 | 5 |
| GCC 13, separate translation units | 16 | 0 | 7 |
| Clang 18, same translation unit | 16 | 5 | 7 |
| Clang 18, separate translation units | 16 | 0 | 7 |

The helper returns `x + 1`; the caller adds one more. Compiler options and
linking are recorded by `scripts/verify-call-stack.sh`; GNU23 is spelled
`-std=gnu2x` for these compiler versions. Complete text includes the helper,
including helper bytes preceding the selected caller entry. Object call
relocations are resolved in the final ELF before text extraction. A different
compiler output fails this profile gate until it has a corresponding proof.
This does not prove the compiler or preservation of C source semantics.

## Current resource contract

`CallStack.ResourcePre` requires current, complete executable code and original
caller-slot loans, an unborrowed owner allocation below the original RSP,
current readable/writable permissions for every contained qword, at least 16
private bytes, the input register, entry metadata and external System V stack
alignment. Allocation identity, owner and epoch are checked. Admission contains
no future successful instruction or function-result premise.

CALL and PUSH have distinct stack-write effect tags. They do not acquire
ordinary DATA store authority. `StackFrame.CPU.Step`, `History` and `Execution`
thread the actual CPU and resource worlds through every instruction. Each
private store is the actual checked `Borrowing.mutate` result with full RAM
coupling. Owner reads do not create a loan that would freeze the allocation.
Code and original caller loans survive, as do allocation/loan metadata and all
permissions. These are sequential ownership transitions, with no atomicity or
concurrent visibility guarantee for the eight-byte stores.

CALL pushes the actual next RIP. RET always reads the current RAM word; there
is no trusted shadow stack. The execution driver freezes the initial caller
slot once. An actual RET whose pre-RSP is below that slot continues with the
actual post-CPU; RET from the original slot terminates. The general driver
compares slot equality, without imposing balance on arbitrary programs. The
compiler proofs establish the stack discipline needed by these four programs.

The postcondition proves the full64 result, actual return target, RSP+8, all
six callee-saved GPRs, nonarithmetic flags, unchanged permissions and every RAM
byte outside the private frame. Used private bytes remain dirty after return.
The exact instruction counts and stack-read traces describe these binaries;
they are not minimum-operation, timing or cycle theorems.

## Reproduce

With pinned Lean, GCC 13, Clang 18, binutils, ShellCheck, OpenSSL development
headers and the usual GNU/Linux tools installed:

```sh
bash scripts/verify-call-stack.sh
```

The default gate builds the four outputs, authenticates entire extracted and
embedded texts before any probe, checks independent native contracts, generates
Lean theorem instances from the actual extraction bytes and selected entries,
audits dependencies and replays the generated module through a fresh kernel.
Any incomplete gate returns failure. `--native-only` explicitly skips formal
checks and reports `formal=NOTRUN`. `CALL_STACK_EVIDENCE_ROOT` selects the
archive directory (default `.cache/call-stack-native`); optional
`CALL_STACK_PROBE` checks the pinned historical cold-probe archive as well.
Neither a historical archive nor a particular machine path is required.

The native observer enters by JMP with a preinstalled original return address
on a guarded owned stack; nested CALL/RET instructions actually execute. It
checks an independent byte-carry result oracle, full-page before/after framing,
ABI registers, effective flags and safe synthetic mutants. Finite observations
and universal machine proofs are separate evidence. Native register/page
observations are not replayed as Lean states. CI caches toolchain/build outputs
but always invokes Lake, checks contracts and performs fresh kernel replay.
CI retains compact receipts; local runs retain full raw observations on disk.

## Target and limits

Ordinary Linux x86-64 user-mode RAM, four-level canonical addressing, AC/CET
disabled and no asynchronous interference are explicit assumptions. Abstract
CALL faults check target canonicality before full stack-store preflight;
physical exception priority/delivery is outside this model. Target execution
permission is checked at the subsequent actual fetch. PUSH RSP uses old RSP;
POP RSP increments first and then writes the loaded value. LEA does modular
address arithmetic without a memory read.

Unsupported additions include indirect/far CALL, memory/16-bit PUSH/POP,
RET-immediate and broader LEA displacement/prefix forms. This sibling engine
is not registered in the existing sequential grader, CFG checker or concurrent
profiles. General interprocedural verification, source/IR preservation, system
startup, Linux/kernel refinement and whole-OS safety remain future work.
