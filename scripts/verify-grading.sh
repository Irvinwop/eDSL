#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

if [[ $(uname -sm) != 'Linux x86_64' ]]; then
    echo 'Grading fixture native evidence requires Linux x86_64' >&2
    exit 2
fi

# All inputs here are owned synthetic fixtures. Never point CI at private
# findings or upload an arbitrary user's binary, packet or rejection log.
output=artifacts/grading-fixtures
mkdir -p "$output"
gcc=${EDSL_GCC:-gcc-13}
if [[ $("$gcc" -dumpversion) != 13 ]]; then
    echo 'Grading fixture evidence requires the selected GCC 13 profile' >&2
    exit 2
fi
lake build edsl-grade edsl-proof-export GradingFixtures
lake env lean -DwarningAsError=true tests/GradingExportClient.lean > "$output/client-tests.txt"
lake env lean -DwarningAsError=true tests/GradingPacket.lean > "$output/packet-tests.txt"
"$gcc" --version > "$output/compiler.txt"
ld --version > "$output/linker.txt"

prepare() {
    local name=$1 source=$2 symbol=$3
    shift 3
    mkdir -p "$output/$name"
    "$gcc" -std=gnu2x -Os -fno-ivopts -fno-tree-vectorize -fno-tree-slp-vectorize \
        -fno-unroll-loops -ffunction-sections -fcf-protection=none -fno-lto \
        -Wall -Wextra -Werror "$@" -c "$source" -o "$output/$name/function.o"
    ld -m elf_x86_64 --build-id=none --gc-sections -z noexecstack \
        -e "$symbol" -Ttext=0x401000 -o "$output/$name/function.elf" "$output/$name/function.o"
    objcopy --dump-section ".text=$output/$name/function.bin" "$output/$name/function.elf"
    wc -c < "$output/$name/function.bin" > "$output/$name/span.txt"
}
prepare pair fixtures/cfg/pair.c sum_pair
prepare stride fixtures/cfg/stride.c sum_stride
prepare write fixtures/cfg/write.c write_word
prepare stride-mov fixtures/cfg/stride-mov.S sum_stride_mov
prepare wrong-stride fixtures/cfg/stride.c sum_stride -DEDSL_CFG_STRIDE=1

expect_status() {
    local expected=$1 name=$2
    shift 2
    local status=0
    "$@" > "$output/$name.txt" 2>&1 || status=$?
    if [[ $status -ne $expected ]]; then
        cat "$output/$name.txt"
        echo "Unexpected grader status for $name: wanted $expected, observed $status" >&2
        exit 1
    fi
}
exporter=(lake env .lake/build/bin/edsl-proof-export)
grader=(lake env .lake/build/bin/edsl-grade)
for task in pair stride write; do
    "${exporter[@]}" EDSL.Grading.Known "EDSL.Grading.Known.$task" \
        "$output/$task/reference.json" > "$output/$task/export-reference.txt"
    "${exporter[@]}" EDSL.Grading.Known "EDSL.Grading.Known.$task" \
        "$output/$task/body.json" --body > "$output/$task/export-body.txt"
    span=$(cat "$output/$task/span.txt")
    expect_status 0 "$task/raw-reference" "${grader[@]}" "${task}32" \
        "$output/$task/function.bin" "$output/$task/reference.json"
    expect_status 0 "$task/raw-body" "${grader[@]}" "${task}32" \
        "$output/$task/function.bin" "$output/$task/body.json"
    expect_status 0 "$task/elf-reference" "${grader[@]}" --elf "$span" "${task}32" \
        "$output/$task/function.elf" "$output/$task/reference.json"
done

# This task permits a checked owned-word mutation while retaining every other
# RAM byte and the ABI frame. The native oracle ignores void RAX and observes
# the complete data page, unaligned/page-edge targets, and full RSI arguments.
"$gcc" -std=gnu2x -O2 -Wall -Wextra -Werror -fcf-protection=none -fno-lto \
    fixtures/cfg/check-write.c fixtures/cfg/trampoline.S -o "$output/native-write-check"
timeout 15 "$output/native-write-check" "$output/write/function.bin" > "$output/write/native.txt" 2>&1
printf '\303' > "$output/write/no-op.bin"
expect_status 5 write/no-op "${grader[@]}" write32 \
    "$output/write/no-op.bin" "$output/write/reference.json"
expect_status 5 write/wrong-task "${grader[@]}" stride32 \
    "$output/write/function.bin" "$output/write/body.json"

# A new implementation proof is exported from a client-only compiled module.
# No known-byte equality or candidate module import is used by the grader.
for mode in reference body; do
    options=()
    if [[ $mode == body ]]; then options=(--body); fi
    "${exporter[@]}" tests.fixtures.StrideMov EDSL.StrideMov.claim \
        "$output/stride-mov/$mode.json" "${options[@]}" > "$output/stride-mov/export-$mode.txt"
    expect_status 0 "stride-mov/raw-$mode" "${grader[@]}" stride32 \
        "$output/stride-mov/function.bin" "$output/stride-mov/$mode.json"
done
span=$(cat "$output/stride-mov/span.txt")
expect_status 0 stride-mov/elf-reference "${grader[@]}" --elf "$span" stride32 \
    "$output/stride-mov/function.elf" "$output/stride-mov/reference.json"
expect_status 5 stride-mov/changed-code "${grader[@]}" stride32 \
    "$output/wrong-stride/function.bin" "$output/stride-mov/reference.json"
cp "$output/stride-mov/function.bin" "$output/stride-mov/mutated.bin"
printf '\004' | dd of="$output/stride-mov/mutated.bin" bs=1 seek=18 count=1 conv=notrunc status=none
expect_status 5 stride-mov/mutated-step "${grader[@]}" stride32 \
    "$output/stride-mov/mutated.bin" "$output/stride-mov/body.json"
"$gcc" -std=gnu2x -O2 -Wall -Wextra -Werror -fcf-protection=none -fno-lto \
    fixtures/cfg/check.c fixtures/cfg/trampoline.S -o "$output/native-check"
timeout 15 "$output/native-check" stride "$output/stride-mov/function.bin" > "$output/stride-mov/native.txt" 2>&1

# Prior clients' v1 packets still bind the same registered binary/OS claim.
printf '%s\n' '["edsl-proof-v1",[],["const",["EDSL","Grading","Known","stride"],[]]]' \
    > "$output/stride/legacy.json"
expect_status 0 stride/raw-legacy "${grader[@]}" stride32 \
    "$output/stride/function.bin" "$output/stride/legacy.json"

# Fresh client helpers include a parameterized header recursor, opaque body,
# safe definitions, proof chain and mutual inductive group. They are data in
# the grading process; the grader does not import the client module.
for mode in reference body; do
    options=()
    if [[ $mode == body ]]; then options=(--body); fi
    "${exporter[@]}" tests.fixtures.GradingClient GradingExportClientFixture.pair \
        "$output/client-$mode.json" "${options[@]}" > "$output/client-$mode-export.txt"
    expect_status 0 "client-$mode" "${grader[@]}" pair32 \
        "$output/pair/function.bin" "$output/client-$mode.json"
done
"${exporter[@]}" tests.fixtures.GradingClient GradingExportClientFixture.extraHypothesis \
    "$output/extra-hypothesis.json" > "$output/extra-hypothesis-export.txt"
expect_status 5 extra-hypothesis "${grader[@]}" pair32 \
    "$output/pair/function.bin" "$output/extra-hypothesis.json"
expect_status 5 wrong-task "${grader[@]}" stride32 \
    "$output/stride/function.bin" "$output/pair/reference.json"
expect_status 5 wrong-program "${grader[@]}" stride32 \
    "$output/wrong-stride/function.bin" "$output/stride/reference.json"

# Equal-length one-byte mutation rejects reuse of a proof for other code.
cp "$output/pair/function.bin" "$output/mutated.bin"
printf '\377' | dd of="$output/mutated.bin" bs=1 count=1 conv=notrunc status=none
expect_status 5 mutated-byte "${grader[@]}" pair32 "$output/mutated.bin" "$output/pair/reference.json"
printf '\377' > "$output/unsupported.bin"
expect_status 5 unsupported-byte "${grader[@]}" pair32 "$output/unsupported.bin" "$output/pair/reference.json"
span=$(cat "$output/pair/span.txt")
expect_status 5 wrong-span "${grader[@]}" --elf "$((span-1))" pair32 \
    "$output/pair/function.elf" "$output/pair/reference.json"
expect_status 3 empty-span "${grader[@]}" --elf 0 pair32 \
    "$output/pair/function.elf" "$output/pair/reference.json"
printf '["edsl-proof-v1",[],["mvar","0"]]' > "$output/metavariable.json"
expect_status 4 metavariable "${grader[@]}" pair32 "$output/pair/function.bin" "$output/metavariable.json"
printf '\377' > "$output/non-utf8.json"
expect_status 4 non-utf8 "${grader[@]}" pair32 "$output/pair/function.bin" "$output/non-utf8.json"
dd if=/dev/zero of="$output/oversized.json" bs=1 count=4194305 status=none
expect_status 6 oversized-packet "${grader[@]}" pair32 "$output/pair/function.bin" "$output/oversized.json"
rm "$output/oversized.json"

cat > "$output/scope.txt" <<'EOF'
Owned fixture evidence only. The grader fixes the registered mathematical task,
all-input termination, current OS authority and registered actual-prefix
effects. Pair/stride remain read-only. Write32 permits ordinary stores only at
the fixed target through checked current ownership, evolving the OS state
along the actual execution while framing all loans, allocations and outside
memory. Raw and complete restricted ELF artifacts are independently bound by
the kernel. Packet checking imports only trusted installed modules; fresh client
helpers arrive as checked data. No native CPU/kernel/source preservation or
whole-program/whole-OS claim is made. The separate CFG/native integration checks
observable ABI behavior; this script exercises the objective proof boundary.
Rejection, unsupported code and resource exhaustion establish no security defect.
The different 22-byte MOV-initialized stride implementation carries a fresh
client-only universal proof. Shared expression packets preserve logical syntax;
default decoder, audit and kernel quotas remain in force. A separate native
oracle checks modular sums, odd-word independence, guard pages and ABI frames.
The write oracle observes full-width input arguments, all data-page bytes,
unaligned/page-edge targets and ABI frames, and rejects six owned mutants.
EOF
find "$output" -type f ! -name SHA256SUMS -print0 | sort -z | xargs -0 sha256sum > "$output/SHA256SUMS"
echo 'Fixed task/artifact grading, fresh client helpers and owned rejection cases passed'
