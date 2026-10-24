# Complete-file counted-worker certificates

`EDSL.Corpus.Counted.CountedCertificate file name maxBytes` connects an exact
complete ELF file to the independent concurrent counted-call contract. A call
requests the low32 value of RSI individual increments of a shared uint64 word.
Other workers can increment between those operations. The whole call is not
one atomic fetch-add.

Import `EDSL.Corpus.CountedCertificate` to use the reusable interface. Import
`EDSL.Corpus.V1.CountedCertificates` for the frozen GCC and Clang examples.
These imports are separate from the sequential `EDSL` entry point.

## What a certificate establishes

A certificate has three obligations:

1. A checked named image binds the complete external file, exact requested
   symbol name, real address, entire symbol extent and explicit byte cap.
2. The unrestricted independent `Counted64.Claim` covers every admitted finite
   population and its supplied requests, every successful prefix and every
   successful returned execution. It also supplies enabledness, chosen finite
   completion after any successful cut, and separate positive per-worker
   own-issue budgets for all successful finite interleavings.
3. A separately inhabited loaded batch supplies a completed overlapping run.
   Both workers are still running and unfinished at its cut. Three original
   observation positions show own/peer/own increments before both actual RETs.

The useful witness does not restrict the universal Claim to two workers or to
its chosen inputs. File bytes outside the function remain part of the
certificate's type. A claim about a selected byte window alone does not supply
this certificate.

`LoadedBatch` records actual full-file admission, independent current entry
resources and target freshness relative to every installed cell. Its retention
theorems preserve complete optional memory cells, including inaccessible bytes
and permission records. `UsefulRun` connects the actual prefix, cut, suffix,
whole observation list and independent Post from one execution. Its
`returns_after_cut` theorem derives return order from actual RET provenance and
the workers still running at the cut.

## Reuse the interface for another program

Prove `Counted64.Claim` for the new function's exact image using the reusable
machine and scheduling infrastructure. Supply an `ELF.FunctionInput` and its
`checkWith` proof against the complete file, exact name and selected cap. Then
construct one admitted `LoadedBatch` and a `UsefulRun` of that batch. These fill
`named`, `claim` and `inhabited`; no additional generic binding, original-index
or RET-order proof is needed.

Apply `certificate.resource` to any matching loaded batch and actual returned
schedule to obtain its full independent Post. Apply
`certificate.retained_image` to any successful prefix for its complete-cell
frame. `certificate.useful_interleaving` extracts the actual completed witness,
its original RMW positions and its actual return ordering.

The implementation is split by responsibility:

| Module | Responsibility |
| --- | --- |
| `EDSL.Corpus.CountedCertificate` | Generic exact-file contract and extraction theorems |
| `EDSL.Corpus.V1.CountedCertificates.Inputs` | Frozen named images, independent loaded admission and supplied-input totals |
| `EDSL.Corpus.V1.CountedCertificates.OverlapPositions` | Ordered issuer lists to original observation indices |
| `EDSL.Corpus.V1.CountedCertificates.Overlap` | Completed same-run overlaps, cleanup retention and example certificates |
| `EDSL.Corpus.V1.CountedCertificates` | Public example facade |

## Frozen examples

| Constructor | Complete file | Entire symbol | Cap |
| --- | ---: | --- | ---: |
| `CountedCertificates.gcc` | 41,016 bytes | `c_counter_worker`, 49 bytes at 4,207,440 | 64 |
| `CountedCertificates.clang` | 44,240 bytes | `c_counter_worker`, 86 bytes at 4,201,344 | 128 |

`loaded_useful_with_cleanup` constructs the same loaded overlap, completion and
logical cleanup for each compiler, every initial word, every upper RSI pair,
every DF-clear modeled flag pair and every per-thread AF stream. Requests are
3 and 9. `SameOutput` retains the exact output, including its complete memory
frame and cleanup. `wrapping_useful` specializes the initial word to UINT64_MAX
and proves that both the independent Post's current word and that cleanup's
actual read are 11. Upper RSI halves are nonzero and distinct in this example.

Build the proof support with `lake build CounterContractSupport`. The full
catalogue and fresh replay gate includes these modules through
`scripts/verify-corpus-certificates.sh --full-project`.

## Scope and remaining integration

These are conditional model theorems. They retain the existing long-mode,
CET-off, represented CPU features, coherent scalar RAM, stable translation
without hidden aliases, protected resource and ownership assumptions. Logical
cleanup does not prove native thread joining. They establish no physical CPU
or Linux correspondence, source/compiler preservation, scheduler fairness,
wall-clock termination or minimum operation count.

The installed data-only grader has no Counted64 route yet. Full-file packet
export, resource-limit feasibility, isolated installed acceptance, mutation
controls and corpus registration remain separate work. Current corpus coverage
stays at **20/40 functions**, **40/80 artifacts** and **three concurrent
functions**. See [the independent contract](counter-contracts.md) for the
behavior and progress quantifiers.
