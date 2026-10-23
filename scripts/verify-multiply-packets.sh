#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
# Run after building ChoiceTests, edsl-grade and edsl-proof-export.
set -euo pipefail
export LC_ALL=C
if [[ $# -ne 0 ]]; then
    echo 'usage: verify-multiply-packets.sh' >&2
    exit 2
fi
cd "$(dirname "${BASH_SOURCE[0]}")/.."
archive=${EDSL_MULTIPLY_OUTPUT:-artifacts/multiply-packets}
mkdir -p "$archive"
archive=$(cd "$archive" && pwd -P)
output=$(mktemp -d "$archive/run.XXXXXXXX")
printf 'Multiplication packet evidence: %s\n' "$output"
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
    for index in {0..7}; do
        printf -v octal '\\%03o' "$((value & 255))"
        printf '%b' "$octal"
        value=$((value >> 8))
    done
}
while read -r compiler offset size entry; do
    raw="$output/inputs/$compiler.bin"
    expect_status 0 "$compiler-extract" dd "if=corpus/v1/$compiler/final.elf" "of=$raw" bs=1 "skip=$offset" "count=$size" status=none
    expect_status 0 "$compiler-complete-extent" test "$(wc -c < "$raw")" -eq "$size"
    changed="$output/inputs/$compiler-changed.bin"
    cp "$raw" "$changed"
    printf '\x90' | dd of="$changed" bs=1 "seek=$((size - 1))" count=1 conv=notrunc status=none
    short="$output/inputs/$compiler-short.bin"
    head -c "$((size - 1))" "$raw" > "$short"
    expect_status 0 "$compiler-isolation" "${lean[@]}" env lean -j1 -DwarningAsError=true \
        --run tests/GradingIsolation.lean --registered tests.GradingMultiply "EDSL.Tests.GradingMultiply.raw_$compiler"
    # Adapter controls: retain the frozen file except for its ELF entry field,
    # selecting the function already certified separately by exact symbol name.
    # These copies are not the unchanged frozen artifacts and do not add coverage.
    elf="$output/inputs/$compiler-entry.elf"
    cp "corpus/v1/$compiler/final.elf" "$elf"
    write_word64 "$entry" | dd of="$elf" bs=1 seek=24 count=8 conv=notrunc status=none
    changed_elf="$output/inputs/$compiler-changed.elf"
    cp "$elf" "$changed_elf"
    printf '\x90' | dd of="$changed_elf" bs=1 "seek=$((offset + size - 1))" count=1 conv=notrunc status=none
    for mode in reference body; do
        options=()
        if [[ $mode == body ]]; then options=(--body); fi
        label="$compiler-$mode"
        packet="$output/packets/$label.json"
        expect_status 0 "$label-export" "${lean[@]}" env edsl-proof-export --registered \
            tests.GradingMultiply "EDSL.Tests.GradingMultiply.raw_$compiler" "$packet" "${options[@]}"
        expect_status 0 "$label-grade" "${lean[@]}" env edsl-grade multiplyModulo64 "$raw" "$packet"
        expect_status 0 "$label-elf-grade" "${lean[@]}" env edsl-grade --elf "$size" multiplyModulo64 "$elf" "$packet"
        expect_status 5 "$label-elf-changed" "${lean[@]}" env edsl-grade --elf "$size" multiplyModulo64 "$changed_elf" "$packet"
        expect_status 0 "$label-elf-changed-reason" grep -F 'kernel declTypeMismatch' "$output/logs/$label-elf-changed.stderr"
        expect_status 5 "$label-elf-short" "${lean[@]}" env edsl-grade --elf "$((size - 1))" multiplyModulo64 "$elf" "$packet"
        expect_status 0 "$label-elf-short-reason" grep -F 'kernel declTypeMismatch' "$output/logs/$label-elf-short.stderr"
        for fault in changed short; do
            candidate=$changed
            if [[ $fault == short ]]; then candidate=$short; fi
            expect_status 5 "$label-$fault" "${lean[@]}" env edsl-grade multiplyModulo64 "$candidate" "$packet"
            expect_status 0 "$label-$fault-reason" grep -F 'kernel declTypeMismatch' "$output/logs/$label-$fault.stderr"
        done
    done
done <<'EXTENTS'
gcc 11696 12 4206000
clang 4912 8 4199216
EXTENTS
sha256sum --quiet --check "$output/input-SHA256SUMS"
printf 'PASS: eight raw/ELF packet acceptances; sixteen changed-byte/extent rejections. No corpus score or native execution claim.\n' > "$output/result.txt"
