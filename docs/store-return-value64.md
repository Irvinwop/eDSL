# Full64 store-result proof grading

The registered `storeReturnValue64` task requires the complete 64-bit argument
in both the eight-byte target and RAX. It also requires the outside-eight-byte
RAM frame, complete writable/executable maps, SysV saved registers, actual RET
and stack advance, and preserved nonarithmetic flags. Arithmetic flags and
volatile registers may change. Instruction selection, instruction count,
read order and the presence of a data load are not contract premises.

The independent contract is `Grading.StoreReturnValue64.Post`; registration uses
`sequentialOwnedWord64X86CallableV1`. The task reuses the present raw and current
resource admissions of `StoreLoad64`, rather than its stricter result contract.
Every admitted initial state and every modeled undefined-AF choice stream must
have an actual returning execution. Input admission contains no successful
decoder, shape, invariant, future mutation or execution assumption.

`StoreReturnValue64.Domain.candidate` constructs useful raw/current-resource
witnesses for every nonempty candidate span of at most 4096 bytes, including
unsupported `[0xff]`. Usefulness compares all 64 bits of the old and requested
values. `Domain.upperOnly` changes only the upper half. Already-equal inputs
are still included in the universal correctness domain.

The raw policy allows ordinary 64-bit stores at the target, and ordinary
32-bit stores whose complete footprint lies inside its eight bytes. It checks
actual enabled instructions, operand loads and code-span containment at every
reachable prefix. It excludes atomic RMWs and syscalls. A 32-bit store is not
relabeled as a 64-bit store; width-dependent faults and checked mutation
histories remain distinct.

The current-resource policy adds the corresponding owner/epoch ticket and
one allocation containing the entire target, with no live loan on that
allocation. DATA4 reads may use any complete four-byte subspan of the target;
DATA8 may use the complete target. Supported DATA4/8 reads may also use a
current held readonly loan, including unrelated allocations. Readonly loans
need no write permission. STACK8 uses the original complete caller-slot loan
and actual current stack binding. Readability alone grants no resource authority.

`OS.WordResources64.Span` derives actual contained 32-bit operations from
current eight-byte authority, preserving its eight-byte frame and full RAM
coupling. Each store advances the same checked OS world. The task's
`ResourceReturn` retains the actual lifted execution, current ownership,
allocation/epoch/permission/outside-cell frame, all original live loan contents
and authority for another arbitrary checked 64-bit store. An unrelated final
world cannot discharge this obligation. Existing 32-bit tasks and the strict
seven-byte `StoreLoad64` convenience API keep their original policies.

Three proved implementations exercise different effects:

| Export target | Executed implementation | Separate accounting |
| --- | --- | --- |
| `EDSL.Grading.Known.storeReturnValue64` | Store RSI, load RAX, RET | 3 instructions; DATA8 then STACK8 |
| `EDSL.StoreReturnValue64Mixed.claim` | XOR EAX; copy RSI to RAX; store64; store32; RET | 5 instructions; STACK8 only |
| `EDSL.StoreReturnValue64Upper.claim` | Copy pointer; add 4; read upper DATA4; copy argument; store64; RET | 6 instructions; DATA4 at target+4 then STACK8 |

The mixed client performs both actual checked mutations. Its second store
rewrites the low half with its current value while retaining the high half.
The upper-read client must prove the offset access succeeds with current owner
authority, even though that loaded value is volatile and unconstrained by the
result. Both permit real arithmetic-flag changes and lie outside the direct
seven-byte certifier. Neither client module enters the grader's trusted imports.

```sh
lake build edsl-grade edsl-proof-export GradingFixtures
lake env edsl-proof-export tests.fixtures.StoreReturnValue64Mixed EDSL.StoreReturnValue64Mixed.claim mixed.json
lake env edsl-grade storeReturnValue64 function.bin mixed.json
lake env edsl-grade --elf 11 storeReturnValue64 function.elf mixed.json
EDSL_GCC=gcc-13 EDSL_CLANG=clang-18 EDSL_CLANGXX=clang++-18 bash scripts/verify-store-return-value64-grading.sh
```

The integration builds fresh GCC13 GNU23 (`gnu2x`), Clang18 GNU23 and GNU++26
store/load output plus both assembled clients. It grades their exact raw and
full explicit-span ELF artifacts in reference and body packet modes under
unchanged default limits. Separate processes check each client's trusted
snapshot isolation. Changed task, code, span and width prevent proof reuse;
actual admitted narrow-store and truncated-result executions independently
refute the mathematical claim. Reduced-budget regression checks exercise
resource rejection without changing service defaults.

The independent native oracle executes those same five final artifacts in
420 calls, observing full64 values, pointers above 4 GiB, aligned/unaligned/
page-edge targets, complete data-page frames and the external SysV trampoline's
saved registers, stack balance/canary and DF. Six owned mutants must fail its
oracle. This callable observer does not inspect the other RFLAGS bits.
Evidence and provenance hashes go to `artifacts/store-return-value64-grading/`.

The model remains sequential ordinary RAM with no asynchronous interference.
CPU/kernel, canonical-address, alignment-control, loader and ABI assumptions
remain explicit in the [coverage report](coverage.md). No source preservation,
physical atomicity, hardware timing, global optimality, general verifier or
whole-OS safety follows. Failure, unsupported input and timeout establish no
security defect. Packet formats, bounded checking and exit statuses are the
same as the other [registered tasks](grading.md).
