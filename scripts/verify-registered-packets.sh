#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
# Shared packet gate for registered scalar tasks; build clients and tools first.
set -euo pipefail
export LC_ALL=C
if [[ $# -ne 7 ]]; then
    echo 'usage: verify-registered-packets.sh TASK CLIENT_MODULE PROOF_NAMESPACE GCC_OFFSET GCC_SIZE CLANG_OFFSET CLANG_SIZE' >&2
    exit 2
fi
task=$1
client=$2
proof_namespace=$3
gcc_offset=$4
gcc_size=$5
clang_offset=$6
clang_size=$7
if [[ ! $task =~ ^[A-Za-z][A-Za-z0-9]*$ ||
      ! $client =~ ^[A-Za-z][A-Za-z0-9_.]*$ ||
      ! $proof_namespace =~ ^[A-Za-z][A-Za-z0-9_.]*$ ||
      ! $gcc_offset =~ ^[1-9][0-9]*$ || ! $clang_offset =~ ^[1-9][0-9]*$ ||
      ! $gcc_size =~ ^[1-9][0-9]*$ || ! $clang_size =~ ^[1-9][0-9]*$ ]]; then
    echo 'invalid registered packet gate arguments' >&2
    exit 2
fi
wrong_task=multiplyModulo64
if [[ $task == multiplyModulo64 ]]; then wrong_task=signumSigned32; fi
cd "$(dirname "${BASH_SOURCE[0]}")/.."
archive=${EDSL_REGISTERED_PACKET_OUTPUT:-artifacts/registered-packets/$task}
mkdir -p "$archive"
archive=$(cd "$archive" && pwd -P)
output=$(mktemp -d "$archive/run.XXXXXXXX")
printf 'Registered packet evidence: %s\n' "$output"
mkdir -p "$output/logs" "$output/packets" "$output/inputs"
finish() {
    local status=$?
    trap - EXIT
    printf '%s\n' "$status" > "$output/status.txt"
    (cd "$output" && find . -type f ! -path ./SHA256SUMS -print0 | sort -z | xargs -0 sha256sum) > "$output/SHA256SUMS"
    if ! (cd "$output" && sha256sum --quiet --check SHA256SUMS); then exit 1; fi
    exit "$status"
}
trap finish EXIT
expect_status() {
    local expected=$1 label=$2 actual=0
    shift 2
    printf '%q ' "$@" > "$output/logs/$label.command"
    printf '\n' >> "$output/logs/$label.command"
    "$@" > "$output/logs/$label.stdout" 2> "$output/logs/$label.stderr" || actual=$?
    printf '%s\n' "$actual" > "$output/logs/$label.status"
    if [[ $actual -ne $expected ]]; then
        tail -n 40 "$output/logs/$label.stderr" >&2
        printf 'Expected %s for %s, got %s\n' "$expected" "$label" "$actual" >&2
        exit 1
    fi
}
# These are the unchanged complete named extents in the frozen -O2 corpus.
# Their named-ELF resource certificates are checked separately in ChoiceTests.
sha256sum corpus/v1/gcc/final.elf corpus/v1/clang/final.elf > "$output/input-SHA256SUMS"
lean=(env LEAN_NUM_THREADS=1 flock /tmp/edsl-lean-build.lock lake)
write_word64() {
    local value=$1 octal index
    for ((index=0; index<8; index++)); do
        printf -v octal '\\%03o' "$((value & 255))"
        printf '%b' "$octal"
        value=$((value >> 8))
    done
}
# Minimal ET_EXEC/RX adapter for the existing entry-based artifact API. The
# complete original corpus ELF is bound separately by its named certificate.
wrap_elf() {
    local raw=$1 size=$2
    printf '\x7fELF\x02\x01\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00'
    printf '\x02\x00\x3e\x00\x01\x00\x00\x00'
    write_word64 4194432
    write_word64 64
    write_word64 0
    printf '\x00\x00\x00\x00\x40\x00\x38\x00\x01\x00\x00\x00\x00\x00\x00\x00'
    printf '\x01\x00\x00\x00\x05\x00\x00\x00'
    write_word64 128
    write_word64 4194432
    write_word64 0
    write_word64 "$size"
    write_word64 "$size"
    write_word64 4096
    write_word64 0
    cat "$raw"
}
while read -r compiler offset size; do
    raw="$output/inputs/$compiler.bin"
    expect_status 0 "$compiler-extract" dd "if=corpus/v1/$compiler/final.elf" "of=$raw" bs=1 "skip=$offset" "count=$size" status=none
    expect_status 0 "$compiler-complete-extent" test "$(wc -c < "$raw")" -eq "$size"
    changed="$output/inputs/$compiler-changed.bin"
    cp "$raw" "$changed"
    printf '\x90' | dd of="$changed" bs=1 "seek=$((size - 1))" count=1 conv=notrunc status=none
    short="$output/inputs/$compiler-short.bin"
    head -c "$((size - 1))" "$raw" > "$short"
    expect_status 0 "$compiler-isolation" "${lean[@]}" env lean -j1 -DwarningAsError=true \
        --run tests/GradingIsolation.lean --registered "$client" "$proof_namespace.raw_$compiler"
    # Synthetic wrapper exercises the existing ELF entry API; it is not a
    # compiler-produced corpus artifact and does not add corpus coverage.
    elf="$output/inputs/$compiler-entry.elf"
    wrap_elf "$raw" "$size" > "$elf"
    changed_elf="$output/inputs/$compiler-changed.elf"
    wrap_elf "$changed" "$size" > "$changed_elf"
    for mode in reference body; do
        options=()
        if [[ $mode == body ]]; then options=(--body); fi
        label="$compiler-$mode"
        packet="$output/packets/$label.json"
        expect_status 0 "$label-export" "${lean[@]}" env edsl-proof-export --registered \
            "$client" "$proof_namespace.raw_$compiler" "$packet" "${options[@]}"
        expect_status 0 "$label-grade" "${lean[@]}" env edsl-grade "$task" "$raw" "$packet"
        expect_status 5 "$label-wrong-task" "${lean[@]}" env edsl-grade "$wrong_task" "$raw" "$packet"
        expect_status 0 "$label-wrong-task-reason" grep -F 'kernel declTypeMismatch' "$output/logs/$label-wrong-task.stderr"
        expect_status 0 "$label-elf-grade" "${lean[@]}" env edsl-grade --elf "$size" "$task" "$elf" "$packet"
        expect_status 5 "$label-elf-changed" "${lean[@]}" env edsl-grade --elf "$size" "$task" "$changed_elf" "$packet"
        expect_status 0 "$label-elf-changed-reason" grep -F 'kernel declTypeMismatch' "$output/logs/$label-elf-changed.stderr"
        expect_status 5 "$label-elf-short" "${lean[@]}" env edsl-grade --elf "$((size - 1))" "$task" "$elf" "$packet"
        expect_status 0 "$label-elf-short-reason" grep -F 'kernel declTypeMismatch' "$output/logs/$label-elf-short.stderr"
        for fault in changed short; do
            candidate=$changed
            if [[ $fault == short ]]; then candidate=$short; fi
            expect_status 5 "$label-$fault" "${lean[@]}" env edsl-grade "$task" "$candidate" "$packet"
            expect_status 0 "$label-$fault-reason" grep -F 'kernel declTypeMismatch' "$output/logs/$label-$fault.stderr"
        done
    done
done <<EXTENTS
gcc $gcc_offset $gcc_size
clang $clang_offset $clang_size
EXTENTS
sha256sum --quiet --check "$output/input-SHA256SUMS"
printf 'PASS: eight raw/ELF packet acceptances; twenty wrong-task/changed-byte/extent rejections. No corpus score or native execution claim.\n' > "$output/result.txt"
