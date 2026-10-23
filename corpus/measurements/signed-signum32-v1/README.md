# Signed low32 signum certificates v1

Source snapshot: `de9b803250efb70caed3801ae801417df5b639e3`.
Both unchanged `c_sign_i32` compiler outputs are now certified against an
independent integer-order contract. Conditional corpus coverage is **20/40
functions and 40/80 compiler artifacts**, including **three distinct concurrent
functions**; **20 functions / 40 artifacts** remain. Both compiler outputs must
satisfy the contract for a function to count. Historical measurements and the
original frozen inputs remain unchanged.

| Compiler | File extent | Virtual-address extent | Bytes |
| --- | --- | --- | --- |
| GCC | [11648, 11665) | [4205952, 4205969) | `f3 0f 1e fa 31 c0 85 ff 0f 9f c0 c1 ef 1f 29 f8 c3` |
| Clang | [4880, 4895) | [4199184, 4199199) | `89 f9 c1 f9 1f 31 c0 85 ff 0f 95 c0 09 c8 c3` |

The [independent contract](../../../EDSL/Scalar32/Signum.lean) requires the final
low32 RAX to represent −1, 0 or 1 according to the signed input's order relative
to zero. It includes every low32 value, including INT32_MIN, and permits arbitrary
incoming upper RDI bits. Actual installed-input checks also bind the supplied
value to RDI, preventing an argument-ignoring constructor from narrowing the
result silently. Universal admission and useful-domain witnesses remain separate.

Both bodies reuse the [vector VCG and shared resource adapters](../../../docs/shift-right32.md),
complete named-ELF checks and trusted execution/task registry. The contracts cover
all independent flag-choice streams. They preserve complete RAM and permissions,
return to the original caller with RSP advanced by eight, and retain current
code/caller resources at continuing prefixes. The actual observations additionally
establish zero-extended full RAX, seven retired instructions and the sole original
eight-byte stack return read. Seven is a modeled count, without a minimum-cost
or CPU-cycle claim.

The [validation record](validation.json) identifies all fourteen successful
original push workflows and 23 jobs. The full corpus gate checked 3,744 command
records, audited 37,829 declarations and replayed `CorpusFullReplay` in a fresh
kernel environment from 06:06:11 to 06:15:21 UTC on 2026-10-23. Independent receipt
review rehashed 24,619 sealed files, the three private proof objects, source and
frozen-input inventories, report and gate inputs. The external Lake build objects
were not downloaded; their sealed inventory and successful CI stability checks
were reviewed. Each registered multiplication/signum packet gate also passed
eight raw/ELF acceptances and twenty exact kernel rejection controls. Synthetic
packet containers are separate from the original named compiler artifacts.

The target assumes stable ordinary RAM, supplied current logical resource
authority, x86-64 long mode, four-level canonical addresses, disabled alignment
checking and CET/IBT/shadow stacks, and no asynchronous interference. Native
CPU/OS correspondence, compiler preservation, concurrency and whole-kernel
verification remain separate obligations.
