# Shared logical right shift by one

The sequential profile has the constructor
`EDSL.X86.Sequential.Instruction.shrOne64 (destination : Register)` and the
flag function `EDSL.X86.Sequential.shrOneFlags64 (old value : Word) (af : Bool)`.
Its instruction length is three. Import
`EDSL.X86.Sequential.ShiftOne` for reusable decoder, step, arithmetic, flag,
frame and CallReturn lifting theorems. The production semantics remain in the
shared Model/Flags/Decode/Machine modules.

Exactly one REX.W prefix (`48` through `4f`), `d1`, and ModRM with mod=3 and
group `/5` are supported. REX.B selects the normal r/m bank, including RSP/R12
and RBP/R13. REX.R is ignored because ModRM.reg is an opcode extension, and
REX.X is ignored without a SIB. Consequently `48/4a/4c/4e d1 e8` all select
RAX; `49/4b/4d/4f d1 e8` all select R8. This deliberate alias policy does not
broaden any other instruction's prefix restrictions.

Other counts (including `c1 /5 01`), widths, groups, memory operands and extra
prefixes are unsupported. Recognized invalid forms return `unsupportedEncoding`;
unknown leading bytes retain the old `unsupportedOpcode` interface. Missing,
nonexecutable or noncanonical instruction bytes produce the precise existing
`inaccessibleInstruction` error. A suffix after the complete three-byte
instruction belongs to the next instruction and is not fetched by SHR.
The old deterministic/concurrent decoder retains its original subset.

The full64 prestate destination is read before being overwritten with logical
`value >>> 1`. This equals unsigned natural division by two for every Word,
including the high bit and all ones. CF is the old low bit, OF the old high
bit, and PF/ZF/SF describe the full64 result (SF is therefore false). AF is
the independent supplied Bool. All nonarithmetic flags, the complete RAM and
permission maps, and all other GPRs are preserved. The instruction has no
operand reads or store intents and produces a plain next observation, with
no atomic or syscall effect. RSP has the same register semantics as any GPR;
no stack/data permission or operand canonicality premise is introduced.

The main reusable contracts are:

- `decodeAt_shrOne64` and `step_shrOne64`, for authenticated instruction bytes.
- `execute_shrOne64_context`, for full-width unsigned division and complete
  register, memory, flags and RIP frames without an input restriction.
- `execute_shrOne64_flags`, for mathematical carry, zero, sign and overflow
  conditions, low-byte parity, and the chosen AF.
- `shrOneFlags64_admissible_iff`, `shrOneFlags64_observed_witness`,
  `shrOneFlags64_admits_both` and `shrOneFlags64_choice_injective`, for the
  exact independent AF-choice contract.
- `execute_shrOne64_choices`, for identical registers/RAM/RIP/reads and flags
  differing only at AF across both choices.
- `EDSL.X86.CallReturn.execute_shrOne64`, for the unchanged shared observation
  when lifted into the CallReturn profile.

These are kernel-checked local-model contracts. The environmental target is
64-bit mode, stable ordinary RAM without asynchronous/concurrent interference,
the existing four-level canonical-address/fetch rules, and CET/IBT/shadow
stacks disabled. Architectural reference: Intel SDM Vol.2
[SAL/SAR/SHL/SHR and REX encoding](https://cdrdv2-public.intel.com/789581/325383-sdm-vol-2abcd.pdf).
No physical CPU/OS, source/compiler, native ownership or loading refinement is
established by this instruction extension.

Physical AF is undefined. A capture that matches defined flags and its admitted
nonarithmetic frame has the exact model witness given by its observed AF. Both
abstract AF choices remain admitted without a claim that both occur physically.
AF-only differences are not defects. Physical register observations must be
distinguished from synthetic RIP, RAM/permissions and unobserved register data.
PUSHFQ masks saved RF/VM; arbitrary abstract RF/VM preservation is not a
physical observation. Debug, host, CET and asynchronous limits remain explicit
in any independently owned native evidence.

## Scoped acceptance

Run `bash scripts/verify-sequential-shift-one.sh`. It builds only the shared
instruction and required compatibility closures, runs the new independent
literal decoder/result/flags/fetch/CFG tests and existing ISA/execution/CFG/
CallReturn/counter/displacement/Sum32 regressions, and audits theorem axioms.
An intentional unapproved-axiom control must fail for its named dependency.
It then compiles the exact project import closure into a new directory with
no cached project objects on LEAN_PATH. Every direct Lean invocation has its
own `/tmp/edsl-lean-build.lock`, `-j1`, `LEAN_NUM_THREADS=1` and warnings as
errors. Lake invocations use the same lock and no `-j1`. Lean is pinned to
4.35.0; no proof-budget or linter changes are part of this extension.

Receipts preserve exact commands, environments, stdout/stderr, timestamps,
exits, failures and the owned source snapshot. Owned sources, actual imported
project/system sources and objects, and compiler/tool binaries are pinned and
rechecked after the fresh build. Unrelated worker files are not hashed. A
successful run writes its exact `CORE-READY`, `FREEZE.sha256` and separate
source/object/tool manifests under `.cache/shift-average/isa/acceptance.*`.
Check that API and source freeze before using the instruction in clients or
native replay. Mutable progress records are excluded from the source freeze.

This gate runs no EDSL.All build, full corpus, native capture/replay, grading
or publication workflow. It makes no average/parity/rotation binary claim.
Failure, timeout and unsupported code do not establish a security defect.
