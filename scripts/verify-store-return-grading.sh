#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
if [[ $(uname -sm) != 'Linux x86_64' ]]; then
    echo 'Pointer-result grading evidence requires Linux x86_64' >&2
    exit 2
fi
# Owned fixtures only. Never send private programs, findings or packets to CI.
output=artifacts/store-return-grading
mkdir -p "$output"
gcc=${EDSL_GCC:-gcc-13}
clang=${EDSL_CLANG:-clang-18}
if [[ $("$gcc" -dumpversion) != 13 ]] ||
    ! "$clang" --version | head -n 1 | grep -q 'clang version 18\.'; then
    echo 'Pointer-result evidence selects GCC13 and Clang18' >&2
    exit 2
fi
uname -srmo > "$output/platform.txt"
ld --version > "$output/linker.txt"
objcopy --version > "$output/objcopy.txt"

prepare() {
    local compiler=$1 dialect=$2 name=$3 source=$4 symbol=$5
    shift 5
    local directory="$output/$name"
    mkdir -p "$directory"
    "$compiler" --version > "$directory/compiler.txt"
    local compile=("-std=$dialect" -Wall -Wextra -Werror -fno-lto
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
prepare "$gcc" gnu2x gcc fixtures/store-return.c store_return32 -Os \
    -fno-tree-vectorize -fno-tree-slp-vectorize -fno-unroll-loops
prepare "$clang" gnu23 clang fixtures/store-return.c store_return32 -Oz \
    -fno-vectorize -fno-slp-vectorize -fno-unroll-loops
prepare "$clang" gnu23 copied fixtures/store-return-copy.S store_return32_copied
prepare "$clang" gnu23 rcx fixtures/store-return-rcx.S edsl_store_return_rcx
prepare "$gcc" gnu2x void fixtures/cfg/write.c write_word -Os

flock /tmp/edsl-lean-build.lock lake build edsl-grade edsl-proof-export edsl-certify-store-return32 GradingFixtures
flock /tmp/edsl-lean-build.lock lake env lean -DwarningAsError=true --run tests/GradingIsolation.lean \
    tests.fixtures.StoreReturnRcx EDSL.StoreReturnRcx.claim \
    > "$output/packet-isolation.txt" 2>&1
exporter=(lake env .lake/build/bin/edsl-proof-export)
grader=(lake env .lake/build/bin/edsl-grade)
expect_status() {
    local expected=$1 name=$2
    shift 2
    local status=0
    "$@" > "$output/$name.txt" 2>&1 || status=$?
    if [[ $status -ne $expected ]]; then
        cat "$output/$name.txt"
        echo "Unexpected pointer-result grading status for $name: wanted $expected, got $status" >&2
        exit 1
    fi
}
for name in gcc clang copied rcx; do
    module=EDSL.Grading.Known
    case "$name" in
        gcc) theorem=EDSL.Grading.Known.storeReturnStoreCopy ;;
        clang) theorem=EDSL.Grading.Known.storeReturnCopyStore ;;
        copied) theorem=EDSL.Grading.Known.storeReturnCopyStoreRax ;;
        rcx) module=tests.fixtures.StoreReturnRcx; theorem=EDSL.StoreReturnRcx.claim ;;
    esac
    span=$(cat "$output/$name/span.txt")
    for mode in reference body; do
        options=()
        if [[ $mode == body ]]; then options=(--body); fi
        "${exporter[@]}" "$module" "$theorem" "$output/$name/$mode.json" "${options[@]}" \
            > "$output/$name/export-$mode.txt" 2>&1
        expect_status 0 "$name/raw-$mode" "${grader[@]}" storeReturn32 \
            "$output/$name/function.bin" "$output/$name/$mode.json"
        expect_status 0 "$name/elf-$mode" "${grader[@]}" --elf "$span" storeReturn32 \
            "$output/$name/function.elf" "$output/$name/$mode.json"
    done
done
# A valid void-store proof is insufficient on the SAME bytes: pointer return
# is a separate mathematical obligation, rather than a filename or shape flag.
"${exporter[@]}" EDSL.Grading.Known EDSL.Grading.Known.write "$output/void/proof.json" \
    > "$output/void/export.txt" 2>&1
expect_status 0 void/original-task "${grader[@]}" write32 "$output/void/function.bin" "$output/void/proof.json"
expect_status 5 void/stronger-task "${grader[@]}" storeReturn32 "$output/void/function.bin" "$output/void/proof.json"
expect_status 5 gcc/wrong-task "${grader[@]}" write32 "$output/gcc/function.bin" "$output/gcc/body.json"
printf '\211\067\211\370\303' > "$output/truncated-pointer.bin"
printf '\211\067\110\215\107\004\303' > "$output/wrong-pointer.bin"
expect_status 5 truncated-pointer "${grader[@]}" storeReturn32 "$output/truncated-pointer.bin" "$output/gcc/body.json"
expect_status 5 wrong-pointer "${grader[@]}" storeReturn32 "$output/wrong-pointer.bin" "$output/gcc/reference.json"
expect_status 5 rcx/changed-code "${grader[@]}" storeReturn32 "$output/gcc/function.bin" "$output/rcx/body.json"
span=$(cat "$output/gcc/span.txt")
expect_status 5 gcc/changed-span "${grader[@]}" --elf "$((span - 1))" storeReturn32 \
    "$output/gcc/function.elf" "$output/gcc/reference.json"
# Direct certification is a narrower convenience API. General proof grading
# accepts the fresh four-instruction client outside its three known shapes.
expect_status 3 rcx/direct-shape-api lake env .lake/build/bin/edsl-certify-store-return32 \
    "$output/rcx/function.bin" "$output/rcx/Direct.lean"
"$clang" -std=gnu23 -O2 -Wall -Wextra -Werror -fcf-protection=none -fno-lto \
    fixtures/store-return-check.c fixtures/cfg/trampoline.S -o "$output/native-check"
timeout 20 "$output/native-check" "$output/gcc/function.bin" "$output/clang/function.bin" \
    "$output/copied/function.bin" "$output/rcx/function.bin" > "$output/native.txt" 2>&1
cat "$output/native.txt"
cat > "$output/scope.txt" <<'SCOPE'
Owned pointer-result proof-grading evidence, using the distinct storeReturn32
task and unchanged present raw/current ownership domains and effects. The task
requires low32 storage, full64 returned target pointer, RAM/permission/ABI frames
and actual current OS resource return. Shape and exact instruction count are
not admission premises. Three known implementations and one fresh RCX client
are graded as raw/full explicit-span ELF artifacts, in reference/body packet
modes, under unchanged default limits. Client modules stay outside the trusted
snapshot. The fresh four-instruction RCX client is outside the direct shape API.
A valid original write32 proof on the SAME void-store bytes is accepted for
write32 and rejected for storeReturn32. Changed code, task and ELF span reject.
Native observations execute those same extracted final bytes:336 positive calls,
full pointers above4GiB, full64 RSI, aligned/unaligned/page-edge targets, complete
data-page frames, saved registers, stack balance/canary and DF. Six owned mutants
are rejected by the independent oracle. Other RFLAGS bits are not observed.
Observations are finite, under the documented ordinary-RAM/CPU/kernel profile;
there is no source preservation, timing, global optimality, concurrency or
whole-program/whole-OS claim. Rejection does not establish a security defect.
SCOPE
{
    sha256sum fixtures/store-return.c fixtures/store-return-copy.S fixtures/store-return-rcx.S \
        fixtures/store-return-check.c fixtures/cfg/trampoline.S fixtures/cfg/write.c \
        scripts/verify-store-return-grading.sh GradeMain.lean EDSL/Grading/Driver.lean \
        EDSL/Grading/Task.lean EDSL/Grading/Known.lean EDSL/StoreReturn32/Contract.lean \
        tests/fixtures/StoreReturnRcx.lean tests/GradingIsolation.lean lean-toolchain lakefile.lean
    find "$output" -type f ! -name SHA256SUMS -print0 | sort -z | xargs -0 sha256sum
} > "$output/SHA256SUMS"
echo 'Distinct pointer-result grading, fresh client proofs and native contracts passed'
