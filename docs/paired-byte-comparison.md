# Paired unsigned-byte comparison

Both frozen `c_memcmp_bytes` functions have Lean certificates for the fixed
`.lexicographicBytes` task. Their result's sign equals unsigned lexicographic
order of the two input snapshots. The C int ABI observes signed low32 RAX;
its upper32 and the magnitude of a nonzero result are unrestricted by the task.
`ByteOrder.Sign` uses independent `List.Lex` order, without invoking an executor,
subtraction implementation or checker result. Equal complete lists require zero.

| Compiler | Frozen row19 entry | File offset | Complete extent |
| --- | --- | ---: | ---: |
| GCC 13.3.0 | `0x402f90` | 12176 | 51 bytes |
| Clang 18.1.3 | `0x4014d0` | 5328 | 45 bytes |

[`ByteComparisonWindows`](../EDSL/Corpus/V1/ByteComparisonWindows.lean)
authenticates the unchanged complete ELF, exact name, unique symbol extent and
executable mapping. The complete function includes padding and every return
site. GCC retains ENDBR64 under the recorded CET-off profile. File/window
authentication alone establishes no execution result.

## Independent contract and current resources

RDI and RSI contain both full64 pointers; RDX contains the common full64 count
`n < 2^64`. Nonempty inputs require both entire nonwrapping readable snapshots
and their exact current loans. Read-only overlap and unaligned addresses are
allowed when snapshots agree on shared bytes. Either input may compatibly alias
code or original caller bytes. At `n=0`, both pointers and data-loan selectors
are unused: no data mapping, pointer validity or input authority is needed.
Current code and the original STACK8 return slot remain required.

[`ByteComparison`](../EDSL/Grading/ByteComparison.lean) fixes that mathematical
and ABI contract. The registry selects the whole specification; candidates
cannot substitute their own result or admission predicate.
[`ByteOrder`](../EDSL/Grading/ByteOrder.lean) connects independent unsigned order
to an equal prefix and the first unequal pair, including high unsigned bytes
and signed low32 differences.

## Shared proofs and exact final files

The [ISA extension](sequential-byte-order.md) supplies DATA1 MOVZX, register
CMP8 and register SUB32 through the existing production machine and CFG checker.
[`VCGen.ByteComparison`](../EDSL/X86/VCGen/ByteComparison.lean) shares paired
snapshot reads, full RAM/register/flag frames, equal-prefix progress, dynamic
rank and the independent sign bridge.
[`ByteComparisonBodies`](../EDSL/Corpus/V1/ByteComparisonBodies.lean) supplies
one sparse-cutpoint proof for each compiler layout. Entry rank is `n+1` and
loop rank is `n-i`; all intervening instructions belong to generated WPs using
the production executor. Admission has no execution-success premise, fixed
test fuel, disjointness restriction or small-count cap.

The universal body theorem covers all admitted snapshots, initial states,
relocations and AF streams. It retains complete RAM and permissions, return
RIP, RSP+8, callee-saved registers and nonarithmetic flags. The shared BufferCall
bridge retains current code, original caller and both exact input authorities
at every continuing prefix and return. `dynamic_bound` gives an output upper
bound of `9*(n+2)` retired model instructions. This is separate from minimum
operation counts, micro-ops, cycles or hardware performance.

The [actual useful resource witnesses](../EDSL/Corpus/V1/ByteComparisonResources.lean)
construct left `[0x41,0x42,0]` at `0x10000` and right `[0x42,0,0]` at `0x10001`
in the same original eight-byte allocation. Generic
[`ReadOnlyCalls.attach`](../EDSL/Corpus/ReadOnlyCalls.lean) and
[`ReadOnlyInputs.borrow`](../EDSL/Corpus/ReadOnlyInputs.lean) issue two new exact
loans and retain every prior loan/allocation, epoch, full installed ELF
cell/permission and original private caller. The right loan extends past the
old three-byte left loan; readability alone cannot authorize it. Both compiler
witnesses are constructible independently of body behavior or desired results.
[`ByteComparisonCertificates`](../EDSL/Corpus/V1/ByteComparisonCertificates.lean)
composes those witnesses and universal proofs through the fixed-task,
complete-file `Buffer.Certificate.ofLoadedCall` constructor.

## Validation and limitations

Regressions cover unsigned high-byte order, swapped operands, first/late
unequal pairs, equal exhaustion, full64 count, dirty scratch high bits,
final-byte guards, compatible overlap, code/caller aliases and empty
noncanonical pointers. Resource checks reject altered ABI fields/snapshots,
forged names/entries, substituted caller slots, old short authority and a
genuinely revoked right loan. They retain nontext BSS contents and permissions
and deny owner writes to the original borrowed caller.

The independent native probe compares actual CPU results/flags and rejects
malformed captures and corrupted observations. Its 15,648 observations and
real guard-page/read-only controls are finite conformance evidence; they supply
no proof oracle or universal hardware theorem.

Reproduce the checks with the pinned Lean toolchain:

```sh
LEAN_NUM_THREADS=1 flock /tmp/edsl-lean-build.lock lake build EDSL.All ByteComparisonTests
bash scripts/check-sequential-byte-order-native.sh
bash scripts/verify-corpus-certificates.sh --full-project
```

The gate locks its own Lean invocations. Ordinary stable RAM, modeled
borrowing/ownership, no asynchronous interference, canonical address assumptions
and the sequential callable target profile remain explicit. These sequential
certificates establish no source/LLVM preservation, dynamic Linux loader,
physical CPU, whole-kernel safety, concurrent buffer access, scheduling
fairness or minimum hardware cost theorem.
