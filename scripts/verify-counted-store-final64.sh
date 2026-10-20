#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
native_only=false
case "$#:${1:-}" in
    0:) ;;
    1:--native-only) native_only=true ;;
    *) echo 'usage: verify-counted-store-final64.sh [--native-only]' >&2; exit 2 ;;
esac
if [[ $(uname -sm) != 'Linux x86_64' ]]; then
    echo 'Final-store client evidence requires Linux x86_64' >&2
    exit 2
fi
# Owned public fixtures only; no private binaries or findings belong here.
output=artifacts/counted-store-final64
mkdir -p "$output"
gcc=${EDSL_GCC:-gcc-13}
clang=${EDSL_CLANG:-clang-18}
if [[ $("$gcc" -dumpversion) != 13 ]]; then
    echo 'Final-store client evidence selects GCC13' >&2
    exit 2
fi
"$clang" --version > "$output/clang.txt"
if ! grep -q 'clang version 18\.' "$output/clang.txt"; then
    echo 'Final-store client evidence selects Clang18' >&2
    exit 2
fi
uname -srmo > "$output/platform.txt"
ld --version > "$output/linker.txt"
objcopy --version > "$output/objcopy.txt"
prepare() {
    local compiler=$1 name=$2
    shift 2
    local directory="$output/$name"
    mkdir -p "$directory"
    "$compiler" --version > "$directory/compiler.txt"
    local compile=(-std=gnu2x -Wall -Wextra -Werror -fno-lto -fcf-protection=none
        -ffunction-sections "$@" -c fixtures/counted-store-final64.c -o "$directory/function.o")
    local link=(-m elf_x86_64 --build-id=none --gc-sections -z noexecstack
        -e publish_final -Ttext=0x401000 -o "$directory/function.elf" "$directory/function.o")
    {
        printf '%q ' "$compiler" "${compile[@]}"; printf '\n'
        printf '%q ' ld "${link[@]}"; printf '\n'
    } > "$directory/arguments.txt"
    "$compiler" "${compile[@]}"
    ld "${link[@]}"
    objcopy --dump-section ".text=$directory/function.bin" "$directory/function.elf"
    readelf -h -l -r -W "$directory/function.elf" > "$directory/elf.txt"
    readelf -rW "$directory/function.elf" > "$directory/relocations.txt"
    if ! grep -q '^There are no relocations in this file\.' "$directory/relocations.txt"; then
        echo "Relocated compiler window is outside this evidence profile: $name" >&2
        exit 2
    fi
    objdump -d -Mintel "$directory/function.elf" > "$directory/disassembly.txt"
    wc -c < "$directory/function.bin" > "$directory/span.txt"
    # Identity is a transparent gate for this one configuration, not a proof.
    local actual
    actual=$(od -An -tx1 -v "$directory/function.bin" | tr -d ' \n')
    if [[ "$actual" != 4889f04885d2740b48ffc048ffca75f8488907c3 ]]; then
        echo "Unsupported final-store byte shape ($name): $actual" >&2
        exit 3
    fi
}
prepare "$gcc" gcc -Os
prepare "$clang" clang -O1 -falign-loops=1
observer=(-std=gnu2x -O2 -Wall -Wextra -Werror -fcf-protection=none -fno-lto
    fixtures/counted-store64-check.c fixtures/cfg/trampoline.S -o "$output/native-check")
printf '%q ' "$gcc" "${observer[@]}" > "$output/observer-arguments.txt"
printf '\n' >> "$output/observer-arguments.txt"
"$gcc" "${observer[@]}"
timeout 45 "$output/native-check" "$output/gcc/function.bin" "$output/clang/function.bin" \
    > "$output/native.txt" 2>&1
cat "$output/native.txt"
cat > "$output/native-scope.txt" <<'SCOPE'
Owned Linux x86-64 final-store native evidence: GCC13 GNU23 (gnu2x) -Os and
Clang18 GNU23 (gnu2x) -O1 -falign-loops=1, LTO/CET disabled. Each linked ELF's
complete .text is extracted, checked against the same literal 20-byte identity
gate, and executed. arguments.txt records each full fixture compile/link command;
observer-arguments.txt records the independent observer compilation command.
The unchanged closed-form oracle checks full64 modular RAX, zero-count target
retention and positive-count final target value, every byte outside the target
on its complete data page, and the external SysV saved-register/stack/DF checks.
There are 504 calls per compiler output (1008 total): seven arguments, six
practical counts {0,1,2,3,31,257}, six aligned/unaligned/page-edge targets above
4GiB and two old values. Huge full64 counts and intermediate stores are not
observed. The other nonarithmetic flags are not independently observed.
Six unchanged generic owned synthetic defects use GCC-shaped loop windows:
missing/narrow stores, wrong iteration count, wrong increment, neighboring write
and saved-register clobber. They check the oracle, not mutations of this final-
store implementation. Timeout or an unexpected signal is inconclusive and fails
the run. Guard mappings and core-dump suppression apply to the owned children.
This is finite native evidence, not a Lean proof, source/volatile/asm preservation,
physical CPU/kernel validation, concurrent visibility, timing or global optimum.
SCOPE
write_hashes() {
    {
        sha256sum fixtures/counted-store-final64.c fixtures/counted-store64-check.c \
            fixtures/cfg/trampoline.S scripts/verify-counted-store-final64.sh
        if [[ $native_only == false ]]; then
            sha256sum tests/fixtures/CountedStoreFinal64.lean \
                tests/fixtures/CountedStoreFinal64/*.lean tests/CountedStoreFinal64.lean \
                tests/GradingIsolation.lean EDSL/Grading/Task.lean EDSL/Grading/Known.lean \
                EDSL/Grading/Driver.lean EDSL/Grading/Export.lean lean-toolchain lakefile.lean
            sha256sum EDSL/Grading/Runtime/Types.lean EDSL/Grading/Runtime/Checker.lean \
                EDSL/CountedStore64/Frame.lean EDSL/CountedStore64/Invariant.lean
        fi
        find "$output" -type f ! -name SHA256SUMS -print0 | sort -z | xargs -0 sha256sum
    } > "$output/SHA256SUMS"
}
if [[ $native_only == true ]]; then
    write_hashes
    echo 'Final-store exact compiler bytes and finite native oracle checks passed; proof checks not run'
    exit 0
fi

lean=(flock /tmp/edsl-lean-build.lock lake)
"${lean[@]}" build edsl-grade edsl-proof-export edsl-certify-counted-store64 \
    edsl-certify-counted-store64-clang tests.fixtures.CountedStoreFinal64
"${lean[@]}" env lean -DwarningAsError=true tests/CountedStoreFinal64.lean \
    > "$output/contract-audit.txt" 2>&1
"${lean[@]}" env leanchecker --fresh tests.fixtures.CountedStoreFinal64 \
    > "$output/fresh-kernel.txt" 2>&1
"${lean[@]}" env lean -DwarningAsError=true --run tests/GradingIsolation.lean \
    tests.fixtures.CountedStoreFinal64 EDSL.CountedStoreFinal64.claim \
    > "$output/isolation.txt" 2>&1
exporter=("${lean[@]}" env .lake/build/bin/edsl-proof-export)
grader=("${lean[@]}" env .lake/build/bin/edsl-grade)
expect_status() {
    local expected=$1 name=$2
    shift 2
    local status=0
    "$@" > "$output/$name.txt" 2>&1 || status=$?
    if [[ $status -ne $expected ]]; then
        cat "$output/$name.txt"
        echo "Unexpected final-store status for $name: wanted $expected, got $status" >&2
        exit 1
    fi
}
for mode in reference body; do
    options=()
    if [[ $mode == body ]]; then options=(--body); fi
    "${exporter[@]}" tests.fixtures.CountedStoreFinal64 EDSL.CountedStoreFinal64.claim \
        "$output/$mode.json" "${options[@]}" > "$output/export-$mode.txt" 2>&1
    for name in gcc clang; do
        span=$(cat "$output/$name/span.txt")
        expect_status 0 "$name/raw-$mode" "${grader[@]}" countedStore64 \
            "$output/$name/function.bin" "$output/$mode.json"
        expect_status 0 "$name/elf-$mode" "${grader[@]}" --elf "$span" countedStore64 \
            "$output/$name/function.elf" "$output/$mode.json"
    done
done
for name in gcc clang; do
    span=$(cat "$output/$name/span.txt")
    expect_status 5 "$name/changed-task" "${grader[@]}" storeReturnValue64 \
        "$output/$name/function.bin" "$output/reference.json"
    expect_status 5 "$name/changed-span" "${grader[@]}" --elf "$((span - 1))" countedStore64 \
        "$output/$name/function.elf" "$output/body.json"
    cp "$output/$name/function.bin" "$output/$name/changed.bin"
    printf '\220' >> "$output/$name/changed.bin"
    expect_status 5 "$name/changed-bytes" "${grader[@]}" countedStore64 \
        "$output/$name/changed.bin" "$output/body.json"
done
# The direct convenience CLIs acquire their own Lean lock. Their unchanged
# byte enumerations stay narrower than the fixed-contract proof grader.
expect_status 3 gcc-direct-shape-api lake env .lake/build/bin/edsl-certify-counted-store64 \
    "$output/gcc/function.bin" "$output/GCCDirect.lean"
expect_status 3 clang-direct-shape-api lake env .lake/build/bin/edsl-certify-counted-store64-clang \
    "$output/clang/function.bin" "$output/ClangDirect.lean"
cat > "$output/scope.txt" <<'SCOPE'
Owned fresh-client countedStore64 grading of GCC13 and Clang18 outputs with
identical final 20 bytes. EDSL.CountedStoreFinal64.claim is outside the trusted
snapshot and Known registry. The client proves the unchanged independently
registered all-full64-count result, zero-count retention, target/permission/ABI
frames and real RET, plus coherent current OS effects and usable returned
ownership. Every actual ordinary contained store uses the checked owner-world
mutation. Source code, loop layout, intermediate store count and exact cost
are absent from the registered task contract.
Separate checked accounting proves four model instructions for zero count,
3*N+5 for positive count, and the singleton original STACK8 operand read.
The same resource execution retains that accounting and returned authority.
The concrete cost comparison with the GCC/Clang loops is not a global minimum.
Both reference/body proof packets grade raw and complete restricted ELF
artifacts for each compiler. A separate client-isolation check, transitive
axiom audit and fresh stored-proof kernel replay are required. Changed task,
bytes and selected ELF span reject these packets; both unchanged GCC and Clang
convenience shape APIs reject this different window. Rejection establishes no
semantic or security defect. native-scope.txt describes the separate 1008 finite
native calls and six generic owned oracle mutants; it is not an all-input proof.
Ordinary RAM, stable code/data, disabled alignment checking/CET and the existing
CPU/kernel environment assumptions apply. No source/volatile preservation,
physical timing, concurrent visibility, whole-OS safety or global optimum is
claimed. Instruction accounting is separate from fixed-task acceptance.
SCOPE
write_hashes
echo 'Fresh final-store client, raw/ELF proof grading and native oracle checks passed'
