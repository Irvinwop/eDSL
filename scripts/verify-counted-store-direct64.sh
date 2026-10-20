#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
native_only=false
case "$#:${1:-}" in
    0:) ;;
    1:--native-only) native_only=true ;;
    *) echo 'usage: verify-counted-store-direct64.sh [--native-only]' >&2; exit 2 ;;
esac
if [[ $(uname -sm) != 'Linux x86_64' ]]; then
    echo 'Direct-add compiler clients require Linux x86_64' >&2
    exit 2
fi
output=artifacts/counted-store-direct64
mkdir -p "$output"
gcc=${EDSL_GCC:-gcc-13}
clang=${EDSL_CLANG:-clang-18}
[[ $("$gcc" -dumpversion) == 13 ]] || { echo 'This fixture selects GCC13' >&2; exit 2; }
"$clang" --version > "$output/clang.txt"
grep -q 'clang version 18\.' "$output/clang.txt" || { echo 'This fixture selects Clang18' >&2; exit 2; }
uname -srmo > "$output/platform.txt"
ld --version > "$output/linker.txt"
objcopy --version > "$output/objcopy.txt"
prepare() {
    local compiler=$1 name=$2 expected=$3
    local directory="$output/$name"
    mkdir -p "$directory"
    "$compiler" --version > "$directory/compiler.txt"
    local compile=(-std=gnu2x -Os -Wall -Wextra -Werror -fno-lto -fcf-protection=none
        -ffunction-sections -c fixtures/counted-store-direct64.c -o "$directory/function.o")
    local link=(-m elf_x86_64 --build-id=none --gc-sections -z noexecstack
        -e publish_direct -Ttext=0x401000 -o "$directory/function.elf" "$directory/function.o")
    {
        printf '%q ' "$compiler" "${compile[@]}"; printf '\n'
        printf '%q ' ld "${link[@]}"; printf '\n'
    } > "$directory/arguments.txt"
    "$compiler" "${compile[@]}"
    ld "${link[@]}"
    objcopy --dump-section ".text=$directory/function.bin" "$directory/function.elf"
    readelf -h -l -r -W "$directory/function.elf" > "$directory/elf.txt"
    readelf -rW "$directory/function.elf" > "$directory/relocations.txt"
    grep -q '^There are no relocations in this file\.' "$directory/relocations.txt" || {
        echo "Relocated compiler window is outside this profile: $name" >&2; exit 2;
    }
    objdump -d -Mintel "$directory/function.elf" > "$directory/disassembly.txt"
    wc -c < "$directory/function.bin" > "$directory/span.txt"
    local actual
    actual=$(od -An -tx1 -v "$directory/function.bin" | tr -d ' \n')
    if [[ "$actual" != "$expected" ]]; then
        echo "Unsupported direct-add byte shape ($name): $actual" >&2
        exit 3
    fi
}
prepare "$gcc" gcc 488d04164885d27403488907c3
prepare "$clang" clang 4889f04801d04885d27403488907c3
observer=(-std=gnu2x -O2 -Wall -Wextra -Werror -fcf-protection=none -fno-lto
    fixtures/counted-store64-check.c fixtures/cfg/trampoline.S -o "$output/native-check")
printf '%q ' "$gcc" "${observer[@]}" > "$output/observer-arguments.txt"
printf '\n' >> "$output/observer-arguments.txt"
"$gcc" "${observer[@]}"
timeout 45 "$output/native-check" "$output/gcc/function.bin" "$output/clang/function.bin" \
    > "$output/native.txt" 2>&1
cat "$output/native.txt"
cat > "$output/native-scope.txt" <<'SCOPE'
Owned GNU23 (gnu2x) -Os GCC13/Clang18 direct-add outputs, LTO/CET disabled.
Complete final linked .text bytes are extracted, compared to exact13/15-byte
identity gates and executed. The unchanged closed-form counted-store observer
checks full64 RAX, zero-count old-target retention, positive-count publication,
all bytes on the owned data page and SysV saved registers/stack/DF.
There are504calls per output (1008total):7arguments,6practical counts
{0,1,2,3,31,257},6aligned/unaligned/page-edge targets above4GiB,2old values.
Large counts are covered by Lean's all-input proof and concrete evaluator
regressions, not these finite native workloads. The six unchanged generic
oracle mutants are loop-shaped owned examples, not direct-client mutations.
Timeout/unexpected signals are inconclusive and fail the run. Guard mappings
and core-dump suppression apply to owned children. No intermediate store trace,
arbitrary nonarithmetic flags, source/volatile preservation, physical ISA/kernel
correctness, concurrency, timing or optimality is established by these runs.
SCOPE
write_hashes() {
    {
        sha256sum fixtures/counted-store-direct64.c fixtures/counted-store64-check.c \
            fixtures/cfg/trampoline.S scripts/verify-counted-store-direct64.sh
        if [[ $native_only == false ]]; then
            sha256sum tests/fixtures/CountedStoreDirect64.lean tests/fixtures/CountedStoreDirect64/*.lean \
                tests/CountedStoreDirect64.lean tests/GradingIsolation.lean \
                EDSL/Grading/StoreReturnValue64/StackOnly.lean EDSL/Grading/Task.lean \
                EDSL/Grading/Known.lean EDSL/Grading/Driver.lean EDSL/Grading/Export.lean \
                EDSL/Grading/Runtime/Types.lean EDSL/Grading/Runtime/Checker.lean \
                lean-toolchain lakefile.lean
        fi
        find "$output" -type f ! -name SHA256SUMS -print0 | sort -z | xargs -0 sha256sum
    } > "$output/SHA256SUMS"
}
if [[ $native_only == true ]]; then
    write_hashes
    echo 'Exact direct-add compiler bytes and finite native checks passed; proof checks not run'
    exit 0
fi
lean=(flock /tmp/edsl-lean-build.lock lake)
"${lean[@]}" build edsl-grade edsl-proof-export edsl-certify-counted-store64 \
    edsl-certify-counted-store64-clang tests.fixtures.CountedStoreDirect64
"${lean[@]}" env lean -DwarningAsError=true tests/CountedStoreDirect64.lean > "$output/contract-audit.txt" 2>&1
"${lean[@]}" env leanchecker --fresh tests.fixtures.CountedStoreDirect64 > "$output/fresh-kernel.txt" 2>&1
exporter=("${lean[@]}" env .lake/build/bin/edsl-proof-export)
grader=("${lean[@]}" env .lake/build/bin/edsl-grade)
expect_status() {
    local expected=$1 name=$2
    shift 2
    local status=0
    "$@" > "$output/$name.txt" 2>&1 || status=$?
    if [[ $status -ne $expected ]]; then
        cat "$output/$name.txt"
        echo "Unexpected direct-add status for $name: wanted $expected, got $status" >&2
        exit 1
    fi
}
for name in gcc clang; do
    theorem="EDSL.CountedStoreDirect64.${name}Claim"
    "${lean[@]}" env lean -DwarningAsError=true --run tests/GradingIsolation.lean \
        tests.fixtures.CountedStoreDirect64 "$theorem" > "$output/$name/isolation.txt" 2>&1
    span=$(cat "$output/$name/span.txt")
    for mode in reference body; do
        options=()
        if [[ $mode == body ]]; then options=(--body); fi
        "${exporter[@]}" tests.fixtures.CountedStoreDirect64 "$theorem" \
            "$output/$name/$mode.json" "${options[@]}" > "$output/$name/export-$mode.txt" 2>&1
        expect_status 0 "$name/raw-$mode" "${grader[@]}" countedStore64 \
            "$output/$name/function.bin" "$output/$name/$mode.json"
        expect_status 0 "$name/elf-$mode" "${grader[@]}" --elf "$span" countedStore64 \
            "$output/$name/function.elf" "$output/$name/$mode.json"
    done
    expect_status 5 "$name/changed-task" "${grader[@]}" storeReturnValue64 \
        "$output/$name/function.bin" "$output/$name/reference.json"
    expect_status 5 "$name/changed-span" "${grader[@]}" --elf "$((span - 1))" countedStore64 \
        "$output/$name/function.elf" "$output/$name/body.json"
    cp "$output/$name/function.bin" "$output/$name/changed.bin"
    printf '\220' >> "$output/$name/changed.bin"
    expect_status 5 "$name/changed-bytes" "${grader[@]}" countedStore64 \
        "$output/$name/changed.bin" "$output/$name/body.json"
done
expect_status 5 gcc-wrong-compiler-packet "${grader[@]}" countedStore64 \
    "$output/gcc/function.bin" "$output/clang/body.json"
expect_status 5 clang-wrong-compiler-packet "${grader[@]}" countedStore64 \
    "$output/clang/function.bin" "$output/gcc/body.json"
# Convenience CLIs lock internally and keep their original shape profiles.
expect_status 3 gcc-direct-shape-api lake env .lake/build/bin/edsl-certify-counted-store64 \
    "$output/gcc/function.bin" "$output/GCCDirect.lean"
expect_status 3 clang-direct-shape-api lake env .lake/build/bin/edsl-certify-counted-store64-clang \
    "$output/clang/function.bin" "$output/ClangDirect.lean"
cat > "$output/scope.txt" <<'SCOPE'
Two fresh compiler clients outside Known prove the same countedStore64 task
as the counted loops: full64 result, zero retention, positive publication,
complete memory/permission/ABI frames and actual RET. Present current owner
authority derives the actual checked store and coherent evolved OS world;
returned allocation/epoch/loan frames and a further arbitrary checked store
remain usable. The generic StackPolicy bridge preserves actual effect widths
and original caller-slot authority; it grants no arbitrary raw DATA authority.
Separate accounting includes RET: GCC4zero/5positive, Clang5zero/6positive,
with singleton original STACK8 read for every full64 count and AF stream.
Acceptance does not constrain counts, instruction shape or intermediate stores.
Reference/body packets bind their own complete raw/ELF outputs. Changed task,
bytes/span and cross-compiler packets reject; convenience shape APIs stay
unsupported. Client isolation, approved-axiom audit and fresh stored-proof
kernel replay are mandatory. No rejection establishes a security defect.
Concrete cost comparisons establish no global optimum, micro-op/cycle/timing,
source/volatile preservation, concurrency or whole-kernel safety claim.
The documented ordinary RAM/stable-code/disabled alignment-checking and CET
CPU/OS environmental assumptions still apply. See native-scope.txt for the
separate finite native workloads and generic owned oracle mutants.
SCOPE
write_hashes
echo 'Fresh direct-add clients, raw/ELF proof grading and native oracle checks passed'
