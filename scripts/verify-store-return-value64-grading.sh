#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
if [[ $(uname -sm) != 'Linux x86_64' ]]; then
    echo 'Full64 result grading evidence requires Linux x86_64' >&2
    exit 2
fi
# Owned public fixtures only; never put private programs or findings here.
output=artifacts/store-return-value64-grading
mkdir -p "$output"
gcc=${EDSL_GCC:-gcc-13}
clang=${EDSL_CLANG:-clang-18}
clangxx=${EDSL_CLANGXX:-clang++-18}
if [[ $("$gcc" -dumpversion) != 13 ]]; then
    echo 'Full64 result grading evidence selects GCC13' >&2
    exit 2
fi
for compiler in "$clang" "$clangxx"; do
    if ! "$compiler" --version | head -n 1 | grep -q 'clang version 18\.'; then
        echo 'Full64 result grading evidence selects Clang18 for C and C++' >&2
        exit 2
    fi
done
uname -srmo > "$output/platform.txt"
ld --version > "$output/linker.txt"
objcopy --version > "$output/objcopy.txt"

prepare() {
    local compiler=$1 dialect=$2 name=$3 source=$4 symbol=$5
    shift 5
    local directory="$output/$name"
    mkdir -p "$directory"
    "$compiler" --version > "$directory/compiler.txt"
    local compile=("-std=$dialect" -Oz -Wall -Wextra -Werror -fno-lto
        -fcf-protection=none -ffunction-sections "$@" -c "$source" -o "$directory/function.o")
    if [[ $source == *.S ]]; then compile=(-c "$source" -o "$directory/function.o"); fi
    local link=(-m elf_x86_64 --build-id=none --gc-sections -z noexecstack
        -e "$symbol" -Ttext=0x401000 -o "$directory/function.elf" "$directory/function.o")
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
        echo "Relocated native window is outside this evidence profile: $name" >&2
        exit 2
    fi
    objdump -d -Mintel "$directory/function.elf" > "$directory/disassembly.txt"
    wc -c < "$directory/function.bin" > "$directory/span.txt"
}
prepare "$gcc" gnu2x gcc fixtures/store-load64.c store_load64 \
    -fno-tree-vectorize -fno-tree-slp-vectorize -fno-unroll-loops
prepare "$clang" gnu23 clang fixtures/store-load64.c store_load64 \
    -fno-vectorize -fno-slp-vectorize -fno-unroll-loops
prepare "$clangxx" gnu++26 clang-cpp fixtures/store-load64.cpp store_load64 \
    -fno-vectorize -fno-slp-vectorize -fno-unroll-loops
prepare "$clang" gnu23 mixed fixtures/store-return-value64-mixed.S edsl_store_return_value64_mixed
prepare "$clang" gnu23 upper fixtures/store-return-value64-upper.S edsl_store_return_value64_upper

flock /tmp/edsl-lean-build.lock lake build edsl-grade edsl-proof-export edsl-certify-store-load64 GradingFixtures
for client in Mixed Upper; do
    flock /tmp/edsl-lean-build.lock lake env lean -DwarningAsError=true --run tests/GradingIsolation.lean \
        "tests.fixtures.StoreReturnValue64$client" "EDSL.StoreReturnValue64$client.claim" \
        > "$output/isolation-$client.txt" 2>&1
done
# These theorems refute actual returning narrow-store/truncated-result programs,
# beyond merely rejecting a proof bound to other bytes. Admission includes ff.
flock /tmp/edsl-lean-build.lock lake env lean -DwarningAsError=true tests/GradingStoreReturnValue64.lean \
    > "$output/semantic-rejections.txt" 2>&1
exporter=(lake env .lake/build/bin/edsl-proof-export)
grader=(lake env .lake/build/bin/edsl-grade)
expect_status() {
    local expected=$1 name=$2
    shift 2
    local status=0
    "$@" > "$output/$name.txt" 2>&1 || status=$?
    if [[ $status -ne $expected ]]; then
        cat "$output/$name.txt"
        echo "Unexpected full64 grading status for $name: wanted $expected, got $status" >&2
        exit 1
    fi
}
for name in gcc clang clang-cpp mixed upper; do
    module=EDSL.Grading.Known
    theorem=EDSL.Grading.Known.storeReturnValue64
    case "$name" in
        mixed) module=tests.fixtures.StoreReturnValue64Mixed; theorem=EDSL.StoreReturnValue64Mixed.claim ;;
        upper) module=tests.fixtures.StoreReturnValue64Upper; theorem=EDSL.StoreReturnValue64Upper.claim ;;
    esac
    span=$(cat "$output/$name/span.txt")
    for mode in reference body; do
        options=()
        if [[ $mode == body ]]; then options=(--body); fi
        "${exporter[@]}" "$module" "$theorem" "$output/$name/$mode.json" "${options[@]}" \
            > "$output/$name/export-$mode.txt" 2>&1
        expect_status 0 "$name/raw-$mode" "${grader[@]}" storeReturnValue64 \
            "$output/$name/function.bin" "$output/$name/$mode.json"
        expect_status 0 "$name/elf-$mode" "${grader[@]}" --elf "$span" storeReturnValue64 \
            "$output/$name/function.elf" "$output/$name/$mode.json"
    done
done
expect_status 5 gcc/wrong-task "${grader[@]}" storeReturn32 "$output/gcc/function.bin" "$output/gcc/body.json"
expect_status 5 mixed/changed-code "${grader[@]}" storeReturnValue64 "$output/upper/function.bin" "$output/mixed/body.json"
span=$(cat "$output/upper/span.txt")
expect_status 5 upper/changed-span "${grader[@]}" --elf "$((span - 1))" storeReturnValue64 \
    "$output/upper/function.elf" "$output/upper/reference.json"
mkdir -p "$output/rejections"
printf '\211\067\110\213\007\303' > "$output/rejections/narrow-store.bin"
printf '\110\211\067\213\007\303' > "$output/rejections/narrow-result.bin"
for name in narrow-store narrow-result; do
    expect_status 5 "rejections/$name" "${grader[@]}" storeReturnValue64 \
        "$output/rejections/$name.bin" "$output/gcc/body.json"
done
# The old direct seven-byte API stays narrower than independent proof grading.
for name in mixed upper; do
    expect_status 3 "$name/direct-shape-api" lake env .lake/build/bin/edsl-certify-store-load64 \
        "$output/$name/function.bin" "$output/$name/Direct.lean"
done
"$clang" -std=gnu23 -O2 -Wall -Wextra -Werror -fcf-protection=none -fno-lto \
    fixtures/store-load64-check.c fixtures/cfg/trampoline.S -o "$output/native-check"
timeout 20 "$output/native-check" "$output/gcc/function.bin" "$output/clang/function.bin" \
    "$output/clang-cpp/function.bin" "$output/mixed/function.bin" "$output/upper/function.bin" \
    > "$output/native.txt" 2>&1
cat "$output/native.txt"
cat > "$output/scope.txt" <<'SCOPE'
Owned storeReturnValue64 grading evidence, profile sequentialOwnedWord64X86CallableV1.
The independent result requires the complete64-bit argument in RAM and RAX,
outside8/permissions/SysV/RET frames and nonarithmetic flags. Present raw and
current-resource inputs do not require a shape, count, read order or load.
Useful domains include upper-half-only changes and unsupported code. Actual
ordinary32/64 effects retain their widths and checked mutations, with complete
footprints inside the owned8-byte target. DATA4/8 reads use target containment
or current held-loan authority; STACK8 uses the original complete caller slot.
Atomics and syscalls need separate authority and remain excluded here.
Fresh GCC13 GNU23(gnu2x), Clang18 GNU23/GNU++26 outputs and two assembled clients
are graded as exact raw/full explicit-span ELF artifacts, reference/body modes,
under unchanged default limits and packet formats. The two fresh modules stay
outside the trusted snapshot. One performs both actual64/32 stores and no data
read; the other reads DATA4 at target+4 before its64store. Arithmetic flags may
change. Both fall outside the unchanged direct seven-byte certifier.
Changed code/task/span and narrow width proof reuse reject. Separate theorems
refute admitted actual narrow-store and truncated-result executions. Reduced
budget regression checks exercise controller limits separately from semantics.
Native observations execute the same five final artifacts:420 calls with full64
values and distinct halves, pointers above4GiB, aligned/unaligned/page-edge
targets, full data-page frames, saved registers, stack balance/canary and DF.
Six owned mutants must fail the independent oracle. Other flags are not observed
by that callable harness. Evidence is finite under the documented ordinary RAM,
CPU/kernel and alignment/CET assumptions. No source preservation, concurrent
atomicity, timing, global optimality, general verifier or whole-OS claim follows.
Rejection, unsupported code and timeout do not establish a security defect.
SCOPE
{
    sha256sum fixtures/store-load64.c fixtures/store-load64.cpp fixtures/store-load64-check.c \
        fixtures/store-return-value64-mixed.S fixtures/store-return-value64-upper.S fixtures/cfg/trampoline.S \
        scripts/verify-store-return-value64-grading.sh GradeMain.lean EDSL/Grading/Driver.lean \
        EDSL/Grading/Task.lean EDSL/Grading/Known.lean EDSL/Grading/Trace.lean EDSL/OS/WordResources64/Span.lean \
        EDSL/Grading/StoreReturnValue64/*.lean tests/fixtures/StoreReturnValue64Mixed.lean \
        tests/fixtures/StoreReturnValue64Upper.lean tests/StoreReturnValue64Mixed.lean \
        tests/StoreReturnValue64Upper.lean tests/GradingStoreReturnValue64.lean tests/GradingIsolation.lean \
        lean-toolchain lakefile.lean
    find "$output" -type f ! -name SHA256SUMS -print0 | sort -z | xargs -0 sha256sum
} > "$output/SHA256SUMS"
echo 'Full64 result grading, fresh width-aware clients and native contracts passed'
