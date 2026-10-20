# Frozen compiler corpus v1

This version contains 40 project-owned representative C functions and two final
Linux x86-64 ELF executables, compiled with GCC and Clang at ordinary `-O2`.
These are real compiled algorithms, not extracts of an upstream libc or kernel.
The final ELF includes the native contract harness and its dynamic dependencies.
`manifest.json` records the exact selected final ELF function bytes, addresses,
and file offsets. The ELF and compiler provenance are frozen by SHA-256.

`specifications.tsv` defines independent behavioral contracts and the required
memory, ABI, synchronization, and OS obligations. These are proof targets,
**not established theorems**. `coverage.tsv` starts at **0/40 functions and 0/80
compiler artifacts certified end-to-end**. Compilation, native tests, ELF
extraction, disassembly, and successful instruction decoding do not increase
that count.

From the repository root:

```sh
bash scripts/verify-corpus-v1.sh --frozen
bash scripts/verify-corpus-v1.sh --rebuild
```

`--frozen` checks source/artifact hashes, re-extracts the exact windows with Lean,
and runs the frozen native harness on Linux x86-64. `--rebuild` additionally
requires identical compiler provenance and identical final ELF bytes. A compiler
or libc change may make reproducibility fail without indicating a program defect.
`--freeze` is the one-time version creation command; it refuses an existing v1.
Changed functions, specifications, options, or compiler outputs require a new
corpus version. Generated scratch, native logs, disassembly, and individual raw
windows remain under ignored `artifacts/compiler-corpus-v1/`.

The Lean extractor uses ELF symbol tables only to select a function interval. It
also checks that the section and one executable file-backed PT_LOAD agree on
every selected interval's file mapping. It does not prove the ELF loader, resolve
external calls, execute instructions, establish memory permissions at runtime,
or certify the selected function. See `docs/compiler-corpus.md` for the checker
integration and milestone rules.
