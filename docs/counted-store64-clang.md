# Clang counted stores with current ownership

`EDSL.CountedStore64.Clang` verifies this complete 20-byte Clang18 GNU23
(`gnu2x`) `-O1 -falign-loops=1` output:

```text
48 89 f0 48 85 d2 74 0b 48 ff c0 48 89 07 48 ff ca 75 f5 c3
```

It satisfies the same independent `CountedStore64.Pre`, `Post`, `ResourcePre`
and `ResourceReturn` contracts as the [GCC profile](counted-store64.md).
RDI supplies the owned eight-byte target, RSI the full64 argument and RDX the
full64 count. All admitted counts and modeled undefined AF choices terminate.
RAX returns `argument + count` modulo `2^64`; zero retains the old target,
and positive counts leave the returned value there. Complete outside-byte,
permission, SysV register and nonarithmetic flag frames are preserved.
Actual RET reads the original caller slot and advances RSP by eight.

This loop stores before decrementing RDX, then JNZ branches directly to INC.
The entry TEST and JE run once. Immediately after STORE, RAX and the target
have advanced while RDX has not. Only DEC restores the settled invariant
`completed + RDX.toNat = count.toNat`. Its full64 zero flag controls JNZ.
The cutpoint is INC, with machine-only rank `RDX.toNat`; entry adds one.
The final branch reaches RET with a settled zero counter.

`Clang.resource_semantics` composes actual instructions through
`ResourceCutpoints.Certificate`. Every STORE carries the same evolved OS
world into DEC, JNZ, subsequent iterations and RET. `ResourceReturn` retains
current RAM, allocation identities, owners/epochs, original live loans,
permissions and outside contents, with authority for an arbitrary next full64
checked store. Future execution and mutation success are not admission facts.

Separate accounting gives one original STACK8 operand read and the exact
natural instruction cost, including RET. Totality precedes exact fuel:

| Exact profile | Retired model instructions |
| --- | --- |
| GCC13 `-Os` | `6 * count.toNat + 4` |
| Clang18 `-O1 -falign-loops=1` | `4 * count.toNat + 4` |

The separate artifact checkers retain each profile's formula. Generated raw
and ELF files expose `exactCertified` and `resourceExactCertified`; bounded
entrypoints use `5 * (count.toNat + 2)` for Clang. Costs do not wrap at 64 bits.
No global minimum, physical timing, micro-op cost, intermediate store count,
concurrent visibility or source-preservation theorem follows. The owned source
has an explicit empty GNU asm count-register barrier. Only these final bytes
are verified; C/volatile/asm semantics and compiler preservation are separate.
The existing ordinary-RAM [environment assumptions](coverage.md#supported-machine-profile)
remain explicit. Linux and Arch implementations are not verified here.

```sh
lake build edsl-certify-counted-store64-clang
lake env lean -DwarningAsError=true tests/CountedStore64Clang.lean
EDSL_CLANG=clang-18 bash scripts/verify-counted-store64-clang.sh
lake env .lake/build/bin/edsl-certify-counted-store64-clang INPUT.bin CERTIFICATE.lean
lake env .lake/build/bin/edsl-certify-counted-store64-clang --elf INPUT.elf CERTIFICATE.lean
```

The CLI kernel-checks literal artifact binding, generated result/resource
theorems and their axiom audit. ELF additionally binds the parsed restricted
container and loaded entry with explicit caller facts. Status codes remain
0 certified, 1 proof failure, 2 usage, 3 unsupported, 4 malformed and 5 I/O
failure. Other shapes remain unsupported. Failure or a stale file establishes
no certification or defect. The fixed-contract grader registry is unchanged.

Lean regressions cover arbitrary zero-count old values, symbolic high-half
and maximum counts, seven-fuel rejection for a single iteration, returned
ownership and a genuinely admitted JZ-for-JNZ semantic counterexample.
Integration regenerates the compiler output, certifies raw/ELF artifacts and
runs 504 independent native calls over practical counts, full64 arguments,
above-4GiB aligned/unaligned/page-edge targets, complete data-page frames and
SysV observations. Six generic GCC-shaped owned mutants check the unchanged
oracle; they are not mutations of the Clang artifact. These finite native
observations do not establish the all-full64-count theorem.
