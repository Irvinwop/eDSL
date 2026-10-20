#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
if [[ $(uname -sm) != 'Linux x86_64' ]]; then
    echo 'Counted-store grading evidence requires Linux x86_64' >&2
    exit 2
fi
output=artifacts/counted-store64-grading
mkdir -p "$output"
gcc=${EDSL_GCC:-gcc-13}
clang=${EDSL_CLANG:-clang-18}
if [[ $("$gcc" -dumpversion) != 13 ]]; then
    echo 'Counted-store grading selects GCC13' >&2
    exit 2
fi
"$clang" --version > "$output/clang.txt"
if ! grep -q 'clang version 18\.' "$output/clang.txt"; then
    echo 'Counted-store grading selects Clang18' >&2
    exit 2
fi
uname -srmo > "$output/platform.txt"
prepare() {
    local compiler=$1 name=$2
    shift 2
    local directory="$output/$name"
    mkdir -p "$directory"
    "$compiler" --version > "$directory/compiler.txt"
    local compile=(-std=gnu2x -Wall -Wextra -Werror -fno-lto -fcf-protection=none
        -ffunction-sections "$@" -c fixtures/counted-store64.c -o "$directory/function.o")
    local link=(-m elf_x86_64 --build-id=none --gc-sections -z noexecstack
        -e publish_counted -Ttext=0x401000 -o "$directory/function.elf" "$directory/function.o")
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
prepare "$gcc" gcc -Os
prepare "$clang" clang -O1 -falign-loops=1
flock /tmp/edsl-lean-build.lock lake build edsl-grade edsl-proof-export
exporter=(lake env .lake/build/bin/edsl-proof-export)
grader=(lake env .lake/build/bin/edsl-grade)
expect_status() {
    local expected=$1 name=$2
    shift 2
    local status=0
    "$@" > "$output/$name.txt" 2>&1 || status=$?
    if [[ $status -ne $expected ]]; then
        cat "$output/$name.txt"
        echo "Unexpected counted-store grade for $name: wanted $expected, got $status" >&2
        exit 1
    fi
}
for name in gcc clang; do
    theorem=EDSL.Grading.Known.countedStore64GCC
    if [[ $name == clang ]]; then theorem=EDSL.Grading.Known.countedStore64Clang; fi
    span=$(cat "$output/$name/span.txt")
    for mode in reference body; do
        options=()
        if [[ $mode == body ]]; then options=(--body); fi
        "${exporter[@]}" EDSL.Grading.Known "$theorem" "$output/$name/$mode.json" "${options[@]}" \
            > "$output/$name/export-$mode.txt" 2>&1
        expect_status 0 "$name/raw-$mode" "${grader[@]}" countedStore64 \
            "$output/$name/function.bin" "$output/$name/$mode.json"
        expect_status 0 "$name/elf-$mode" "${grader[@]}" --elf "$span" countedStore64 \
            "$output/$name/function.elf" "$output/$name/$mode.json"
    done
    expect_status 5 "$name/wrong-task" "${grader[@]}" storeReturnValue64 \
        "$output/$name/function.bin" "$output/$name/reference.json"
    expect_status 5 "$name/short-span" "${grader[@]}" --elf "$((span - 1))" countedStore64 \
        "$output/$name/function.elf" "$output/$name/body.json"
done
expect_status 5 gcc/wrong-compiler-proof "${grader[@]}" countedStore64 \
    "$output/gcc/function.bin" "$output/clang/reference.json"
cp "$output/gcc/function.bin" "$output/changed.bin"
printf '\220' >> "$output/changed.bin"
expect_status 5 gcc/changed-bytes "${grader[@]}" countedStore64 \
    "$output/changed.bin" "$output/gcc/body.json"
"$gcc" -std=gnu2x -O2 -Wall -Wextra -Werror -fcf-protection=none -fno-lto \
    fixtures/counted-store64-check.c fixtures/cfg/trampoline.S -o "$output/native-check"
timeout 45 "$output/native-check" "$output/gcc/function.bin" "$output/clang/function.bin" \
    > "$output/native.txt" 2>&1
cat "$output/native.txt"
cat > "$output/scope.txt" <<'SCOPE'
Owned countedStore64 fixed-task grading of fresh GCC13 and Clang18 outputs.
The registered contract fixes all-full64-count termination, independent modular
result and zero-count retention, complete target/permission/ABI frames, actual
RET, checked current OS effects and same-world usable returned authority.
The task selects no byte shape, loop layout or instruction formula. Two known
compiler proofs are exported in reference/body mode and graded against raw and
complete restricted ELF artifacts with explicit selected spans. Wrong tasks,
proofs bound to other compiler bytes, changed bytes and shortened spans reject
these packets; those rejections alone do not establish semantic defects.
No new client implementation outside the two known windows is demonstrated here.
Separate native evidence makes 504 finite closed-form/frame/ABI calls per output
and rejects six generic owned synthetic mutants. It does not execute huge counts,
prove physical CPU/OS conformance, source/volatile preservation, concurrent
visibility, store count, physical timing, whole-OS safety or global optimality.
SCOPE
{
    sha256sum fixtures/counted-store64.c fixtures/counted-store64-check.c fixtures/cfg/trampoline.S \
        EDSL/Grading/Task.lean EDSL/Grading/Known.lean EDSL/Grading/Driver.lean Tools/Grade/Function.lean \
        EDSL/CountedStore64/*.lean EDSL/CountedStore64/Clang/*.lean \
        scripts/verify-counted-store64-grading.sh lean-toolchain lakefile.lean
    find "$output" -type f ! -name SHA256SUMS -print0 | sort -z | xargs -0 sha256sum
} > "$output/SHA256SUMS"
echo 'Counted-store fixed-task raw/ELF proof grading and native observations passed'
