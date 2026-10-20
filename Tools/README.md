# Command-line tools

These Lean entrypoints wrap the reusable library in [`EDSL/`](../EDSL/).
The executable names below are the stable interface; their source locations
are separate from the proofs and specifications they invoke.

For a new program, start with the [verification workflow](../docs/verify-a-function.md).
`edsl-cfg-import` checks exact bytes and a finite control-flow graph. An
independent contract, permissions and any loop invariants are still required.
The profile-specific certifiers below support their documented byte shapes;
adding another program does not require adding another executable.

| Command | Entrypoint | Purpose |
| --- | --- | --- |
| `edsl-cfg-import` | [CFG.lean](CFG.lean) | Import raw bytes, an ELF entry span or a named ELF function and generate checked bindings/CFG obligations. |
| `edsl-proof-export` | [ProofExport.lean](ProofExport.lean) | Export a client theorem packet for a fixed-contract grader. |
| `edsl-grade` | [Grade/Function.lean](Grade/Function.lean) | Grade registered scalar, memory and array contracts. |
| `edsl-grade-call-stack` | [Grade/CallStack.lean](Grade/CallStack.lean) | Grade callable stack-frame contracts. |
| `edsl-grade-call-memory64` | [Grade/CallMemory64.lean](Grade/CallMemory64.lean) | Grade callable DATA8 contracts. |
| `edsl-grade-call-memory-loop64` | [Grade/CallMemoryLoop64.lean](Grade/CallMemoryLoop64.lean) | Grade counted DATA8 calls. |
| `edsl-grade-atomic-logical64` | [Grade/AtomicLogical64.lean](Grade/AtomicLogical64.lean) | Grade locked logical-update contracts. |
| `edsl-grade-atomic-set64` | [Grade/AtomicSet64.lean](Grade/AtomicSet64.lean) | Grade locked set-operation contracts. |
| `edsl-certify` | [Certify/Function.lean](Certify/Function.lean) | Certify the original scalar and memory profiles. |
| `edsl-certify-process` | [Certify/Process.lean](Certify/Process.lean) | Certify the restricted process exit/write profiles. |
| `edsl-certify-counter` | [Certify/Counter.lean](Certify/Counter.lean) | Certify the fixed counter-worker profile. |
| `edsl-certify-mutex-worker` | [Certify/MutexWorker.lean](Certify/MutexWorker.lean) | Certify the fixed mutex-worker profile. |
| `edsl-certify-futex` | [Certify/Futex.lean](Certify/Futex.lean) | Certify the restricted futex operation profiles. |
| `edsl-certify-futex-client` | [Certify/FutexClient.lean](Certify/FutexClient.lean) | Certify the fixed publishing futex client. |
| `edsl-certify-futex-predicate` | [Certify/FutexPredicate.lean](Certify/FutexPredicate.lean) | Certify the fixed predicate/recheck profile. |
| `edsl-certify-sum32` | [Certify/Sum32.lean](Certify/Sum32.lean) | Certify the supported sum32 layouts. |
| `edsl-certify-store-return32` | [Certify/StoreReturn32.lean](Certify/StoreReturn32.lean) | Certify the supported store/return layouts. |
| `edsl-certify-store-load64` | [Certify/StoreLoad64.lean](Certify/StoreLoad64.lean) | Certify the supported store/load layouts. |
| `edsl-certify-atomic-logical64` | [Certify/AtomicLogical64.lean](Certify/AtomicLogical64.lean) | Certify the fixed locked logical-update profile. |
| `edsl-certify-atomic-set64` | [Certify/AtomicSet64.lean](Certify/AtomicSet64.lean) | Certify the fixed locked set-operation profile. |
| `edsl-certify-counted-store64` | [Certify/CountedStore64.lean](Certify/CountedStore64.lean) | Certify the supported GCC counted-store layout. |
| `edsl-certify-counted-store64-clang` | [Certify/CountedStore64Clang.lean](Certify/CountedStore64Clang.lean) | Certify the supported Clang counted-store layout. |

Build only the tool you need, then run it through Lake:

```sh
lake build edsl-cfg-import
lake exe edsl-cfg-import function.bin artifacts/Imported.lean
lake exe edsl-cfg-import --elf-symbol function_name program.elf artifacts/Imported.lean
```

See [named ELF imports](../docs/named-elf-import.md),
[CFG imports](../docs/cfg.md), [fixed-contract grading](../docs/grading.md)
and the [trust boundary](../docs/trust.md) for limits and failure behavior.
