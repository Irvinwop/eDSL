#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
if [[ $(uname -sm) != 'Linux x86_64' ]]; then
    echo 'Full64 store/load evidence requires Linux x86_64' >&2
    exit 2
fi
# Owned public fixtures only; no private binaries or findings belong here.
output=artifacts/store-load64
mkdir -p "$output"
gcc=${EDSL_GCC:-gcc-13}
clang=${EDSL_CLANG:-clang-18}
clangxx=${EDSL_CLANGXX:-clang++-18}
if [[ $("$gcc" -dumpversion) != 13 ]]; then
    echo 'Full64 store/load evidence selects GCC13' >&2
    exit 2
fi
for compiler in "$clang" "$clangxx"; do
    if ! "$compiler" --version | head -n 1 | grep -q 'clang version 18\.'; then
        echo 'Full64 store/load evidence selects Clang18 for C and C++' >&2
        exit 2
    fi
done
uname -srmo > "$output/platform.txt"
ld --version > "$output/linker.txt"
objcopy --version > "$output/objcopy.txt"

prepare() {
    local compiler=$1 dialect=$2 name=$3 source=$4
    shift 4
    local directory="$output/$name"
    mkdir -p "$directory"
    "$compiler" --version > "$directory/compiler.txt"
    local compile=("-std=$dialect" -Oz -Wall -Wextra -Werror -fno-lto
        -fcf-protection=none -ffunction-sections "$@" -c "$source" -o "$directory/function.o")
    local link=(-m elf_x86_64 --build-id=none --gc-sections -z noexecstack
        -e store_load64 -Ttext=0x401000 -o "$directory/function.elf" "$directory/function.o")
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
}
prepare "$gcc" gnu2x gcc fixtures/store-load64.c \
    -fno-tree-vectorize -fno-tree-slp-vectorize -fno-unroll-loops
prepare "$clang" gnu23 clang fixtures/store-load64.c -fno-vectorize -fno-slp-vectorize -fno-unroll-loops
prepare "$clangxx" gnu++26 clang-cpp fixtures/store-load64.cpp -fno-vectorize -fno-slp-vectorize -fno-unroll-loops

flock /tmp/edsl-lean-build.lock lake build edsl-certify-store-load64
certifier=(lake env .lake/build/bin/edsl-certify-store-load64)
expect_status() {
    local expected=$1 name=$2
    shift 2
    local status=0
    "$@" > "$output/$name.txt" 2>&1 || status=$?
    if [[ $status -ne $expected ]]; then
        cat "$output/$name.txt"
        echo "Unexpected full64 store/load status for $name: wanted $expected, got $status" >&2
        exit 1
    fi
}
for name in gcc clang clang-cpp; do
    expect_status 0 "$name/raw" "${certifier[@]}" "$output/$name/function.bin" "$output/$name/Raw.lean"
    expect_status 0 "$name/elf" "${certifier[@]}" --elf "$output/$name/function.elf" "$output/$name/ELF.lean"
done
mkdir -p "$output/rejections"
printf '\211\067\110\213\007\303' > "$output/rejections/narrow-store.bin"
printf '\110\211\067\213\007\303' > "$output/rejections/narrow-load.bin"
printf '\110\211\007\110\213\007\303' > "$output/rejections/wrong-source.bin"
printf '\110\213\007\303' > "$output/rejections/missing-store.bin"
printf '\110\211\067\110\213\007' > "$output/rejections/truncated.bin"
printf '\110\211\067\110\213\007\303\220' > "$output/rejections/trailing.bin"
for name in narrow-store narrow-load wrong-source missing-store truncated trailing; do
    expect_status 3 "rejections/$name" "${certifier[@]}" "$output/rejections/$name.bin" \
        "$output/rejections/$name.lean"
done
: > "$output/rejections/empty.bin"
printf 'bad magic%055d' 0 > "$output/rejections/bad-magic.elf"
printf '\177ELF' > "$output/rejections/short.elf"
expect_status 4 rejections/empty "${certifier[@]}" "$output/rejections/empty.bin" "$output/rejections/empty.lean"
expect_status 4 rejections/bad-magic "${certifier[@]}" --elf "$output/rejections/bad-magic.elf" "$output/rejections/bad-magic.lean"
expect_status 4 rejections/short "${certifier[@]}" --elf "$output/rejections/short.elf" "$output/rejections/short.lean"
expect_status 2 rejections/usage "${certifier[@]}"
expect_status 5 rejections/io "${certifier[@]}" "$output/rejections/not-present.bin" "$output/rejections/io.lean"

"$clang" -std=gnu23 -O2 -Wall -Wextra -Werror -fcf-protection=none -fno-lto \
    fixtures/store-load64-check.c fixtures/cfg/trampoline.S -o "$output/native-check"
timeout 20 "$output/native-check" "$output/gcc/function.bin" "$output/clang/function.bin" \
    "$output/clang-cpp/function.bin" > "$output/native.txt" 2>&1
cat "$output/native.txt"
cat > "$output/scope.txt" <<'SCOPE'
Owned Linux x86-64 full64 store/load/RET compiler evidence: GCC13 GNU23(gnu2x),
Clang18 GNU23 and Clang18 GNU++26, all -Oz scalar with LTO/CET disabled.
Certificates kernel-check the literal raw or ELF artifact, selected final
entry bytes, and full64 stored/returned value with full RAM/permission/ABI
frames for every admitted input/AF stream. The actual3 instructions read
DATA8 then STACK8. Current OS certificates retain the same checked owner
mutation and evolved world through the load and caller return, all live loans,
allocation/owner/epoch metadata and current RAM coupling. Ordinary8-byte
authority requires one complete allocation; existing32 tasks/policies retain
their4-byte meanings. This direct profile does not add a grader registry task.
The volatile source pointer retains the compiler fixture's load; no C/C++
volatile semantics, source preservation or physical atomicity is proved.
Native calls execute the same ELF-extracted raw bytes:252 calls across3
artifacts, full64 values with distinct high/low halves, addresses above4GiB,
aligned/unaligned/page-edge8byte targets and complete data-page frames.
The external SysV trampoline observes saved registers, stack balance/canary
and DF. Other flags are covered by the separate one-instruction observer,
not independently observed by this callable harness. Six owned synthetic
width/missing-store/source/endian/neighbor mutants must fail its oracle.
Evidence is finite under the ordinary RAM/CPU/kernel profile with alignment
checking/CET disabled. It establishes no universal CPU or Linux correctness,
concurrency, timing, whole-program/whole-OS safety or unrestricted optimality.
Unsupported windows, malformed inputs and proof failure establish no defect;
an old output file alone never establishes successful certification.
SCOPE
{
    sha256sum fixtures/store-load64.c fixtures/store-load64.cpp fixtures/store-load64-check.c \
        fixtures/cfg/trampoline.S scripts/verify-store-load64.sh Tools/Certify/StoreLoad64.lean \
        EDSL/StoreLoad64/Artifact.lean EDSL/StoreLoad64/Contract.lean \
        EDSL/X86/Memory64.lean EDSL/OS/WordResources64.lean lean-toolchain lakefile.lean
    find "$output" -type f ! -name SHA256SUMS -print0 | sort -z | xargs -0 sha256sum
} > "$output/SHA256SUMS"
echo 'Full64 store/load raw/ELF certificates, current OS contracts and native observations passed'
