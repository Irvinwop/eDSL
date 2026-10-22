# Managed plain64 load/store certificates v1

Source snapshot: `958e099bf34e55108920c11d63ce5edae8611ff4`.
The milestone adds both unchanged row-35 `c_atomic_load_acquire64` and row-36
`c_atomic_store_release64` outputs: **18/40 functions, 36/80 compiler artifacts,
three distinct concurrent functions**, with **22 functions / 44 artifacts**
remaining. Both compilers must pass for function credit. Fetch-add is the third
concurrent identity; a mixed witness adds no function. The
[byte-equality record](../byte-equality-v1/) retains its historical 16/40, 32/80,
one-concurrent result and receipts. Frozen v1 sources, options, manifests, ELFs
and baseline diagnostics remain unchanged.

## Exact final-byte extents

Decimal half-open file/address extents include RET and GCC's original ENDBR64;
intersymbol padding is excluded. Complete-file/name/extent binding is required.

| Compiler / function | File extent | Virtual-address extent | Size | Exact bytes |
| --- | --- | --- | ---: | --- |
| GCC `c_atomic_load_acquire64` | [12944, 12952) | [4207248, 4207256) | 8 | `f3 0f 1e fa 48 8b 07 c3` |
| GCC `c_atomic_store_release64` | [12960, 12968) | [4207264, 4207272) | 8 | `f3 0f 1e fa 48 89 37 c3` |
| Clang `c_atomic_load_acquire64` | [6848, 6852) | [4201152, 4201156) | 4 | `48 8b 07 c3` |
| Clang `c_atomic_store_release64` | [6864, 6868) | [4201168, 4201172) | 4 | `48 89 37 c3` |

## Contract and reuse

Plain uses `managed-tso64-plain64-cohort-v1`; fetch-add retains the distinct
`managed-tso64-closed-batch-v1`. Acquire/release are declared interface annotations.
MOV decoding establishes no source intent; modeled synchronization requires a
qualifying selected source.

The [independent contract](../../../EDSL/Grading/ConcurrentTask/Plain64/Claim.lean) separates present-only
admission from static shapes. Its universal `Plain64.Claim` covers prefix safety,
current resources, completed behavior, closed output, either-AF enabledness,
chosen completion from every successful finite prefix, actual drain closure and
a positive own-issue bound. Loads return the selected full64 word in RAX; stores
enqueue full64 RSI at the RDI-selected cell with a logical unit reply, without
promising a machine RAX result.

General prefix/return results permit valid incoming FIFOs and pending stores at
RET. Constructed closed legal histories require initialized resources and
**initially and finally empty queues**. They retain the same run's calls,
scanner events, complete live registry/RAM manifest, actual writer identities
and legal graph. The shared resource adapter preserves current code/caller/target
authority, original caller reads, ABI frames, complete outside-footprint cells
and permissions. Targets are fresh from the entire retained loaded image.

Both compilers reuse one production decoder/scheduler and checked padding/MOV64/RET
method family. The generic body bound, **64 own issues per worker**, establishes no
physical timing, minimum cost or fairness. Witness AF
indices are local to each execution block.

[Homogeneous witnesses](../../../EDSL/Corpus/PlainWitnesses.lean) place both
workers' accesses before either return, using high words `0x100000001`,
`0x200000003` and `0x300000005`. These samples do not restrict universal inputs.
[Mixed witnesses](../../../EDSL/Corpus/PlainMixedWitnesses.lean) retain
`writer RET < publication < reader access`: `UsefulMixed.delayed` identifies the
actual writer's `AtomicTrace.Graph.Publication`, and `selectedRF` selects that
writer in the same `ClosedPost`. Rows retain initializer offsets and actual
access order; machine counters differ from logical labels.
[Independent equal-word regressions](../../../tests/PlainCallHistory64.lean)
check literal initializer/writer RF rows and publication ranks despite equal
payloads, and reject substituted writer keys.

The [CLI](../../Certify.lean) projects `plainNamedCertificate` from each same-file
`plainCohortCertificate`, retaining all universal, homogeneous and mixed
[certificate gates](../../../EDSL/Corpus/PlainCertificate.lean). See the
[method guide](../../../docs/managed-plain-methods.md) and
[exact-window API](../../../EDSL/Corpus/V1/PlainWindows.lean).

## Validation

The original [frozen-corpus workflow](https://github.com/Irvinwop/eDieSeL/actions/runs/39845526164)
passed for the source above on 2026-10-22. All **14 original push workflows and
23 jobs** passed; no rerun or other-branch result was substituted.

| Full-project certificate gate | Recorded result |
| --- | --- |
| Scope | `full-project-and-corpus-cli`, READY, exit 0 |
| Build | 1,298 jobs passed; Lean 4.35.0, warnings as errors |
| Transitive audit | 36,524 declarations; only `propext`, `Quot.sound`, `Classical.choice` permitted |
| Command expectations | 3,183 passed, including intended negative exits |
| Actual fresh replay | `CorpusFullReplay`, exit 0; 2026-10-22T20:32:13Z–2026-10-22T20:40:13Z |
| Closing checks | Source, frozen files, modules, gate inputs, binaries and receipt manifest stable |
| Independent evidence checks | 20,490 receipt hashes and 1,530 source hashes verified; sources match the Git commit |

The replay imports `EDSL.All`, the corpus CLI and the regression modules.
[report.json](report.json), [proof-sources.sha256](proof-sources.sha256) and
[frozen-files.sha256](frozen-files.sha256) retain the actual accepted outputs.
[validation.json](validation.json) records the run identities, archive/manifest
digests and separate local gate and production-CI results. The downloaded
archive matched GitHub's digest. Receipt verification did not execute downloaded
commands or independently rehash hosted Lake objects absent from that archive.

A separate local full gate passed, including actual fresh replay from
2026-10-22T20:20:22Z to 2026-10-22T20:33:48Z. Its report and source/input
manifests are byte-identical to CI. The separate production CI passed a
1,661-job build, approved-only audit and fresh `EDSL.All` replay.
These results identify this source snapshot; later documentation edits do not
extend its proof scope. Native, CFG and scalar-packet observations retain
separate scopes. Reproduce the certificate gate with:

```sh
bash scripts/verify-corpus-certificates.sh --full-project
```

Assumptions include stable scalar RAM/translations without hidden aliases,
current managed authority, fixed workers, long mode and CET off. Source/compiler
ordering, physical/published x86-TSO, Linux/kernel refinement, full C23, repeated
invocations, broader incoming-queue graph construction and fairness remain open.
Failure, unsupported code or timeout establishes no defect. Broader program,
kernel and OS verification remains the goal.
