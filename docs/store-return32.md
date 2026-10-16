# Pointer-returning stores

`EDSL.StoreReturn32` proves a callable machine-code contract for storing the
low32 argument through a pointer and returning that complete pointer in RAX.
The independent `Post` extends the existing mathematical `Write32.Post` with
`RAX = input.address`. It retains the complete outside-word RAM and permission
frame, actual return address and stack advance, six SysV callee-saved registers
and nonarithmetic flag bits. Instruction selection is absent from this post.

The existing raw `Write32.Pre` and current OS `Write32.ResourcePre` are reused.
These require present executable bytes, ABI arguments, complete target and
caller-stack permissions, disjoint target writes and canonical return/stack
conditions. No future-success premise, 32-bit pointer bound or new target
read loan is added. The input's high32 RSI bits remain arbitrary.

| Shape | Exact bytes | Operations |
| --- | --- | --- |
| `storeCopy` | `89 37 48 89 f8 c3` | store through RDI; copy RDI to RAX; RET |
| `copyStore` | `48 89 f8 89 37 c3` | copy RDI to RAX; store through RDI; RET |
| `copyStoreRax` | `48 89 f8 89 30 c3` | copy RDI to RAX; store through copied RAX; RET |

Selected GCC13 GNU23 (`gnu2x`) `-Os` output uses the first shape; Clang18
`gnu23 -Oz` uses the second. The third is a separately owned assembly variant.
GCC13 `-Oz` emits register XCHG in the selected profile and remains unsupported.
No valid output is silently rewritten into a supported window.

`raw_semantics` derives actual decoding and the three real machine transitions
for every modeled AF choice stream. `resource_policy` constructs the checked
owner mutation and chains the current OS world through each transition. For
store-first execution, the following copy uses that evolved world. RET uses
the actual preserved RSP binding and the original current stack loan.
`resource_semantics` couples the same execution/result to the retained world,
owner/epoch metadata, loans, permissions and all outside-word cells.

`ResultContract` separately records exactly three retired instructions,
including RET, and only the original stack8 operand read. This is accounting
for these implementations, without a global minimum-operations, micro-op or
cycle claim. Operand read lists exclude instruction fetches.

The CLI emits literal certificates checked by Lean's kernel:

```sh
lake build edsl-certify-store-return32
lake exe edsl-certify-store-return32 FUNCTION.bin artifacts/StoreReturnRaw.lean
lake exe edsl-certify-store-return32 --elf FUNCTION.elf artifacts/StoreReturnELF.lean
EDSL_GCC=gcc-13 EDSL_CLANG=clang-18 bash scripts/verify-store-return32.sh
```

A raw input must match the complete selected six-byte window. ELF uses the
existing restricted loader and decodes the entry through its first RET within
64 bytes/32 instructions, without skipping unsupported instructions. Literal
ELF parsing and file-backed executable bytes are kernel checked. The generated
`loadedCertified` theorem composes fresh installation, actual memory/entry
bindings and present caller premises with the functional result. Process
startup and resources are separate caller obligations.

Exit0 means the emitted certificate checked. Exit1 is certificate failure,
exit2 usage, exit3 an unsupported window/container, exit4 truncated/bad-magic ELF,
an incomplete executable instruction or empty raw input, and exit5 an IO failure. Segment/entry constraints outside
the restricted ELF profile, including valid segments above64KiB, use exit3.
Other nonmatching raw windows,
including truncated or trailing windows, are unsupported. An old output file,
proof rejection or timeout does not establish success or a defect. The CLI
owns its Lean-checking lock; do not wrap its invocation in the same lock.

The owned native observer executes the exact final ELF-extracted `.text` bytes
also certified as raw inputs. Three positive artifacts receive seven full64
arguments, six aligned/unaligned/page-edge targets and two sentinel fills:
252 calls. Pointers must be above4GiB. It checks the full returned pointer,
every data-page byte and the external SysV trampoline's saved-register, stack
balance/canary and DF observations. Six owned mutations must fail, including
pointer truncation, missing/overwide/wrong-source/wrong-target writes and a
wrong returned pointer. Other RFLAGS bits are not independently observed.
Evidence and provenance are retained in `artifacts/store-return32/`.

These are sequential ordinary-RAM contracts with explicit CPU/kernel and
caller-environment assumptions. Native observations are finite and do not
establish universal hardware behavior, concurrent visibility, timing, source
preservation or whole-program/OS safety. The existing registered `write32`
grader leaves RAX unconstrained; this stronger direct certificate API does
not relabel that task or register a new pointer-result grading task.
