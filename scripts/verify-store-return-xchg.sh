#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
if [[ $(uname -sm) != 'Linux x86_64' ]]; then
    echo 'Register-exchange compiler evidence requires Linux x86_64' >&2
    exit 2
fi
# Owned public fixture only; never put private binaries/findings in CI output.
output=artifacts/store-return-xchg
mkdir -p "$output"
gcc=${EDSL_GCC:-gcc-13}
if [[ $("$gcc" -dumpversion) != 13 ]]; then
    echo 'Register-exchange compiler evidence selects GCC13' >&2
    exit 2
fi
"$gcc" --version > "$output/compiler.txt"
uname -srmo > "$output/platform.txt"
ld --version > "$output/linker.txt"
objcopy --version > "$output/objcopy.txt"
compile=(-std=gnu2x -Oz -Wall -Wextra -Werror -fno-lto -fcf-protection=none
    -ffunction-sections -fno-tree-vectorize -fno-tree-slp-vectorize -fno-unroll-loops
    -c fixtures/store-return.c -o "$output/function.o")
link=(-m elf_x86_64 --build-id=none --gc-sections -z noexecstack
    -e store_return32 -Ttext=0x401000 -o "$output/function.elf" "$output/function.o")
{
    printf '%q ' "$gcc" "${compile[@]}"; printf '\n'
    printf '%q ' ld "${link[@]}"; printf '\n'
} > "$output/arguments.txt"
"$gcc" "${compile[@]}"
ld "${link[@]}"
objcopy --dump-section ".text=$output/function.bin" "$output/function.elf"
readelf -h -l -r -W "$output/function.elf" > "$output/elf.txt"
readelf -rW "$output/function.elf" > "$output/relocations.txt"
if ! grep -q '^There are no relocations in this file\.' "$output/relocations.txt"; then
    echo 'Relocated compiler window is outside this evidence profile' >&2
    exit 2
fi
objdump -d -Mintel "$output/function.elf" > "$output/disassembly.txt"
span=$(wc -c < "$output/function.bin")
printf '%s\n' "$span" > "$output/span.txt"

lean=(flock /tmp/edsl-lean-build.lock lake)
"${lean[@]}" build edsl-grade edsl-proof-export edsl-certify-store-return32 GradingFixtures
"${lean[@]}" env lean -DwarningAsError=true tests/StoreReturnXchg.lean \
    > "$output/contract.txt" 2>&1
"${lean[@]}" env lean -DwarningAsError=true --run tests/GradingIsolation.lean \
    tests.fixtures.StoreReturnXchg EDSL.StoreReturnXchg.claim > "$output/isolation.txt" 2>&1
exporter=("${lean[@]}" env .lake/build/bin/edsl-proof-export)
grader=("${lean[@]}" env .lake/build/bin/edsl-grade)
expect_status() {
    local expected=$1 name=$2
    shift 2
    local status=0
    "$@" > "$output/$name.txt" 2>&1 || status=$?
    if [[ $status -ne $expected ]]; then
        cat "$output/$name.txt"
        echo "Unexpected register-exchange status for $name: wanted $expected, got $status" >&2
        exit 1
    fi
}
for mode in reference body; do
    options=()
    if [[ $mode == body ]]; then options=(--body); fi
    "${exporter[@]}" tests.fixtures.StoreReturnXchg EDSL.StoreReturnXchg.claim \
        "$output/$mode.json" "${options[@]}" > "$output/export-$mode.txt" 2>&1
    expect_status 0 "raw-$mode" "${grader[@]}" storeReturn32 "$output/function.bin" "$output/$mode.json"
    expect_status 0 "elf-$mode" "${grader[@]}" --elf "$span" storeReturn32 \
        "$output/function.elf" "$output/$mode.json"
done
# A different valid implementation cannot borrow the exact-XCHG proof packet.
printf '\110\211\370\211\060\303' > "$output/move-instead.bin"
expect_status 5 changed-code "${grader[@]}" storeReturn32 "$output/move-instead.bin" "$output/body.json"
expect_status 5 changed-task "${grader[@]}" write32 "$output/function.bin" "$output/reference.json"
expect_status 5 changed-span "${grader[@]}" --elf "$((span - 1))" storeReturn32 \
    "$output/function.elf" "$output/reference.json"
# This CLI owns its own Lean lock. The generic grader is intentionally broader
# than its unchanged enumeration of three convenient direct-adapter shapes.
expect_status 3 direct-shape-api lake env .lake/build/bin/edsl-certify-store-return32 \
    "$output/function.bin" "$output/Direct.lean"
"$gcc" -std=gnu2x -O2 -Wall -Wextra -Werror -fcf-protection=none -fno-lto \
    fixtures/store-return-check.c fixtures/cfg/trampoline.S -o "$output/native-check"
timeout 20 "$output/native-check" "$output/function.bin" > "$output/native.txt" 2>&1
cat "$output/native.txt"
cat > "$output/scope.txt" <<'SCOPE'
Owned GCC13 GNU23 (gnu2x spelling) -Oz scalar/Linux x86-64 evidence. The fresh
client proves the extracted final five-byte XCHG RAX,RDI; MOV [RAX],ESI; RET
window against the independently registered storeReturn32 contract under the
unchanged raw/current-resource domains and default grading limits. Both raw
and explicit-span ELF artifacts grade with fresh reference/body packets. The
client remains outside the trusted snapshot and direct shape enumeration.
Theorems prove the full returned pointer, low32 store, complete memory/ABI and
current OS frames, the old RAX value in volatile RDI, three actual modeled
instructions including RET, and the original stack-only eight-byte read.
Conditional modeled-instruction minimum uses the existing useful-input and
initial-RAX-differs premises; it is not a CPU-cycle or unrestricted optimum.
Native checks execute the same extracted bytes for 84 pointer/page-frame/ABI
calls and reject six owned synthetic mutants. The native pointer oracle does
not observe the volatile RDI value; separate register-exchange native evidence
checks both exchange outputs. Ordinary RAM, disabled alignment checking/CET
and the existing CPU/kernel profile apply. No source preservation, physical
timing, concurrency or whole-OS result is claimed. Rejection establishes no
security defect. Changed exact bytes, task and ELF span reject the packet.
SCOPE
{
    sha256sum fixtures/store-return.c fixtures/store-return-check.c fixtures/cfg/trampoline.S \
        scripts/verify-store-return-xchg.sh tests/fixtures/StoreReturnXchg.lean \
        tests/StoreReturnXchg.lean tests/GradingIsolation.lean EDSL/Grading/Task.lean \
        EDSL/Grading/Driver.lean EDSL/Grading/Export.lean lean-toolchain lakefile.lean
    find "$output" -type f ! -name SHA256SUMS -print0 | sort -z | xargs -0 sha256sum
} > "$output/SHA256SUMS"
echo 'Fresh XCHG compiler client, raw/ELF proof grading and native contracts passed'
