# Build and validation

Run from the repository root. For the reusable API and new-function checks:

```sh
lake build EDSL VerificationTests UnaryTests PopcountTests AverageTests
```

For named-function extraction, generated-module composition, independent
functional/current-resource verification and exact-file rejection checks on an
owned real compiler output:

```sh
bash scripts/check-named-elf-import.sh
```

This gate executes the independent parser regressions and checks generated
artifact/CFG proofs, return-slot regressions, stale proof rejection and a fresh
kernel replay of the combined closure. The newly imported `twice` module is
composed with an independent mathematical specification, a universal functional
proof, and an actual modeled current-resource wraparound call. It takes its own
Lean locks; do not add an outer lock. It imports the owned ELF without executing
it. The [import guide](named-elf-import.md) states the accepted profile and the
client proof obligations; extraction alone supplies no functional proof.
Reusable parser tests expose a namespaced runner; the script generates its own
private `main` driver, allowing the test module and corpus CLI to share an aggregate.

For full final-file binding, rejection controls, axiom audit and a fresh replay
of the entire proof catalogue, reusable verification regressions and corpus CLI:

```sh
bash scripts/verify-corpus-certificates.sh --full-project
```

The gate takes its own Lean locks; do not wrap it in another lock. It records
current source and module identities and never executes an input ELF. The
full-project closure includes the raw-function, final-ELF and import-boundary
regressions built through `VerificationTests`, plus the shared unary ISA,
scalar-body and current-resource regressions built through `UnaryTests` and
the counter/displacement, sparse scalar-loop, popcount body, current-resource
and grading regressions built through `PopcountTests`. `AverageTests` adds
shared logical-shift semantics, generated average bodies, full64 overflow and
current-resource checks, fixed-task packet rejection controls and independent
arithmetic regressions at standard and nonstandard bit widths.

For owned finite logical-right-shift observations with independently chosen
undefined AF and ordinary-kernel production replay:

```sh
bash scripts/verify-sequential-shift-one.sh
bash scripts/verify-shift-one.sh
```

The [shift guide](shift-one.md) distinguishes fresh source compilation from
stored-object replay. The [native runner](../fixtures/native/shift-one/README.md)
states the observed registers, synthetic model data, compiler prerequisites
and finite matrix. These checks are separate from the universal
[unsigned-average contract](unsigned-average.md).

For owned finite ADD32 imm8/INC32/signed disp8 LEA native observations and
production decode/step replay for both AF choices:

```sh
bash scripts/verify-counter-displacement.sh
```

The [runner guide](../fixtures/native/counter-displacement/README.md) states
prerequisites, closure readiness and capture/replay modes. `--native-only`
does not run Lean replay. This finite evidence does not establish universal
physical CPU or native Linux refinement; the symbolic full64 popcount and
exact-file/resource contracts are [separate obligations](popcount.md).

The complete historical validation checklist follows. Compiler/native integrations
need their recorded compiler versions and Linux/x86-64 dependencies.

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake build EDSL.All edsl-certify edsl-certify-process edsl-certify-counter edsl-certify-mutex-worker edsl-certify-futex edsl-certify-futex-client edsl-certify-futex-predicate edsl-certify-sum32 edsl-cfg-import
lake build edsl-grade-call-stack edsl-proof-export tests.fixtures.CallStack.CoveredAudit tests.fixtures.CallStack.FoundationAudit tests.fixtures.CallStack.Inline.Accounting
lake env lean -DwarningAsError=true tests/X86.lean
lake env lean -DwarningAsError=true tests/Memory.lean
lake env lean -DwarningAsError=true tests/AddressSpace.lean
lake env lean -DwarningAsError=true tests/OSComposition.lean
lake env lean -DwarningAsError=true tests/WordStore.lean
lake env lean -DwarningAsError=true tests/ELF.lean
lake env lean -DwarningAsError=true tests/Process.lean
lake env lean -DwarningAsError=true tests/Write.lean
lake env lean -DwarningAsError=true tests/ControlFlow.lean
lake env lean -DwarningAsError=true tests/Ownership.lean
lake env lean -DwarningAsError=true tests/Borrowing.lean
lake env lean -DwarningAsError=true tests/Threads.lean
lake env lean -DwarningAsError=true tests/AtomicExchange.lean
lake env lean -DwarningAsError=true tests/OSAtomicExchange.lean
lake env lean -DwarningAsError=true tests/Atomics.lean
lake env lean -DwarningAsError=true tests/AtomicThreads.lean
lake env lean -DwarningAsError=true tests/FetchAdd.lean
lake env lean -DwarningAsError=true tests/CounterThreads.lean
lake env lean -DwarningAsError=true tests/CounterThreadsWitness.lean
lake env lean -DwarningAsError=true tests/Mutex.lean
lake env lean -DwarningAsError=true tests/MutexISA.lean
lake env lean -DwarningAsError=true tests/MutexReplay.lean
lake env lean -DwarningAsError=true tests/MutexInvariant.lean
lake env lean -DwarningAsError=true tests/MutexExecution.lean
lake env lean -DwarningAsError=true tests/StoreBuffer.lean
lake env lean -DwarningAsError=true tests/MixedStoreBuffer.lean
lake env lean -DwarningAsError=true tests/PureCall.lean
lake env lean -DwarningAsError=true tests/CompilerArithmetic.lean
lake env lean -DwarningAsError=true tests/CorpusArithmetic.lean
lake env lean -DwarningAsError=true tests/GradingArithmetic.lean
lake env lean -DwarningAsError=true tests/TSO.lean
lake env lean -DwarningAsError=true tests/MutexTSO.lean
lake env lean -DwarningAsError=true tests/Suspend.lean
lake env lean -DwarningAsError=true tests/FutexResources.lean
lake env lean -DwarningAsError=true tests/FutexStubs.lean
lake env lean -DwarningAsError=true tests/FutexService.lean
lake env lean -DwarningAsError=true tests/FutexPhysical.lean
lake env lean -DwarningAsError=true tests/FutexAdmission.lean
lake env lean -DwarningAsError=true tests/FutexClientFrames.lean
lake env lean -DwarningAsError=true tests/FutexClientControl.lean
lake env lean -DwarningAsError=true tests/FutexClientPhysical.lean
lake env lean -DwarningAsError=true tests/FutexClientCertificate.lean
lake env lean -DwarningAsError=true tests/FutexClientCoverage.lean
lake env lean -DwarningAsError=true tests/FutexNotification.lean
lake env lean -DwarningAsError=true tests/FutexNotificationCertificate.lean
lake env lean -DwarningAsError=true tests/FutexPredicate.lean
lake env lean -DwarningAsError=true tests/FutexPredicateCertificate.lean
lake env lean -DwarningAsError=true tests/FutexPredicateAccounting.lean
lake env lean -DwarningAsError=true tests/SequentialISA.lean
lake env lean -DwarningAsError=true tests/SequentialExecution.lean
lake env lean -DwarningAsError=true tests/SequentialMoves.lean
lake env lean -DwarningAsError=true tests/SequentialMoves64.lean
lake env lean -DwarningAsError=true tests/SequentialMoveResources.lean
lake env lean -DwarningAsError=true tests/SequentialAddMemory64.lean
lake env lean -DwarningAsError=true tests/SequentialAddMemory64Resources.lean
lake env lean -DwarningAsError=true tests/CallStackDomain.lean
lake env lean -DwarningAsError=true tests/CallStackCoverage.lean
lake env lean -DwarningAsError=true tests/GradingCallStackContract.lean
lake env lean -DwarningAsError=true tests/StoreReturn32Raw.lean
lake env lean -DwarningAsError=true tests/StoreReturn32Resources.lean
lake env lean -DwarningAsError=true tests/GradingStoreReturn.lean
lake env lean -DwarningAsError=true tests/StoreReturnRcx.lean
lake env lean -DwarningAsError=true tests/StoreReturnAccounting.lean
lake env lean -DwarningAsError=true tests/ArrayResources.lean
lake env lean -DwarningAsError=true tests/ArraySum64.lean
lake env lean -DwarningAsError=true tests/Sum32Pointer.lean
lake env lean -DwarningAsError=true tests/Sum32Index.lean
lake env lean -DwarningAsError=true tests/Sum32Artifact.lean
lake env lean -DwarningAsError=true tests/CFG.lean
lake env lean -DwarningAsError=true tests/Stride32.lean
lake env lean -DwarningAsError=true tests/Pair32.lean
lake env lean -DwarningAsError=true tests/Pair32Resources.lean
bash scripts/check-audit.sh
lake env leanchecker --fresh EDSL.All
bash scripts/verify-compilers.sh
bash scripts/verify-process.sh
bash scripts/verify-loops.sh
bash scripts/verify-fetch-add.sh
bash scripts/verify-counter-workers.sh
bash scripts/verify-mutex.sh
bash scripts/verify-mutex-workers.sh
bash scripts/verify-futex.sh
bash scripts/verify-futex-clients.sh
bash scripts/verify-futex-predicate.sh
EDSL_GCC=gcc-13 EDSL_CLANG=clang-18 bash scripts/verify-sum32.sh
EDSL_CLANG=clang-18 bash scripts/verify-sequential-moves.sh
EDSL_CLANG=clang-18 bash scripts/verify-sequential-arithmetic64.sh
EDSL_CLANG=clang-18 bash scripts/verify-sequential-logical64.sh
EDSL_GCC=gcc-13 EDSL_CLANG=clang-18 bash scripts/verify-logical64.sh
EDSL_CLANG=clang-18 bash scripts/verify-sequential-add-memory64.sh
EDSL_GCC=gcc-13 EDSL_CLANG=clang-18 bash scripts/verify-array-sum64.sh
EDSL_GCC=gcc-13 EDSL_CLANG=clang-18 bash scripts/verify-call-stack.sh
bash scripts/verify-call-memory-loop64.sh
EDSL_GCC=gcc-13 EDSL_CLANG=clang-18 bash scripts/verify-counted-store-direct64.sh
EDSL_GCC=gcc-13 EDSL_CLANG=clang-18 bash scripts/verify-store-return32.sh
EDSL_GCC=gcc-13 EDSL_CLANG=clang-18 bash scripts/verify-store-return-grading.sh
EDSL_GCC=gcc-13 bash scripts/verify-store-return-xchg.sh
EDSL_GCC=gcc-13 EDSL_CLANG=clang-18 EDSL_CLANGXX=clang++-18 bash scripts/verify-store-load64.sh
EDSL_GCC=gcc-13 bash scripts/verify-counted-store64.sh
EDSL_CLANG=clang-18 bash scripts/verify-counted-store64-clang.sh
EDSL_GCC=gcc-13 EDSL_CLANG=clang-18 bash scripts/verify-counted-store64-grading.sh
EDSL_GCC=gcc-13 EDSL_CLANG=clang-18 bash scripts/verify-counted-store-final64.sh
EDSL_GCC=gcc-13 EDSL_CLANG=clang-18 EDSL_CLANGXX=clang++-18 bash scripts/verify-store-return-value64-grading.sh
EDSL_GCC=gcc-13 bash scripts/verify-cfg.sh
```

`lean-toolchain` pins Lean 4.35.0. The library currently needs no third-party
Lean packages. The audit rejects transitive axiom dependencies outside Lean's
standard `propext`, `Quot.sound`, and `Classical.choice`; it also rejects proof
holes. Its negative check injects an untrusted transitive dependency and
requires rejection. The bundled `leanchecker` replays the stored proofs in a
fresh kernel environment. These check the current declarations, not the adequacy of a future
language, OS, or hardware model. The compiler integration command also needs
Linux/x86-64, Clang, GCC and binutils; it uses only owned synthetic fixtures.
CI caches the pinned Lean toolchain and Lake build outputs. Compatible previous
builds supply incremental inputs; Lake still checks source and dependency traces.
Every run retains the contract tests, axiom audit, fresh kernel replay, and native
integration checks. Cache misses build normally. Bump the workflow's cache
version strings to discard old entries when diagnosing a cache problem.
The sum32 integration selects GCC 13 (`-Os -fno-ivopts`, GNU23 spelled `gnu2x`)
and Clang 18 (`-Oz`, `gnu23`), with scalar code and LTO/CET disabled. Its
certificates, native observations and provenance use `artifacts/sum32-fixtures/`.
The CFG integration uses GCC 13 and `flock`, checks complete raw/explicit-span
ELF imports, and separately proves the stride function's independent contract.
Its owned native observations and generated proofs use `artifacts/cfg-fixtures/`.
The array-sum integration uses GCC 13/Clang 18 GNU23 `-Os` outputs and writes
owned evidence to `artifacts/array-sum64/`. Its parallel workflow keeps a separate
partial build cache. Default success requires every model/proof and native gate;
`--native-only` explicitly leaves universal Lean validation `NOTRUN`.
The counted DATA8 default gate requires native and formal validation of the
complete nested GCC/Clang texts, plus nested and closed-form raw/full-ELF proof
grading at default budgets. `--native-only` reports both `formal=NOTRUN` and
`grading=NOTRUN`. It retains source/provenance snapshots and fresh kernel replay;
native observations cover nested clients only. See the
[proof scope and reproduction commands](call-memory-loop64.md).

The optional native compiler probes are separate from proofs:

```sh
cmake -S . -B build -G Ninja \
  -DCMAKE_C_COMPILER=clang \
  -DCMAKE_CXX_COMPILER=clang++
cmake --build build
```

These require exact `-std=gnu23` and `-std=gnu++26` acceptance, checked with
Clang 18.1.3 for the bootstrap. They establish language-mode/syntax availability,
not complete language support or semantic preservation.
