#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail
export LC_ALL=C
if [[ $# -ne 0 ]]; then
    echo 'usage: verify-logical64.sh' >&2
    exit 2
fi
cd "$(dirname "${BASH_SOURCE[0]}")/.."
archive=${EDSL_LOGICAL64_PROOF_OUTPUT:-artifacts/logical64}
mkdir -p "$archive"
archive=$(cd "$archive" && pwd -P)
output=$(mktemp -d "$archive/run.XXXXXXXX")
printf 'Logical64 proof and native evidence: %s\n' "$output"
record_command() { printf '%q ' "$@"; printf '\n'; }
write_hashes() {
    (cd "$output" && find . -type f ! -path ./SHA256SUMS -print0 | sort -z | xargs -0 sha256sum) \
        > "$output/SHA256SUMS"
}
finish() {
    local status=$?
    trap - EXIT
    if [[ $status -ne 0 ]]; then
        printf 'INCOMPLETE: full verification exited %s; inspect retained evidence\n' "$status" \
            > "$output/result.txt"
    fi
    printf '%s\n' "$status" > "$output/script-status.txt"
    if ! write_hashes || ! (cd "$output" && sha256sum --quiet --check SHA256SUMS); then
        status=1
        echo 'INCOMPLETE: full evidence manifest verification failed' > "$output/result.txt"
        printf '%s\n' "$status" > "$output/script-status.txt"
        write_hashes || true
    fi
    exit "$status"
}
trap finish EXIT
echo 'INCOMPLETE: full proof, grading and native checks have not finished' > "$output/result.txt"
mkdir -p "$output/source" "$output/logs" "$output/packets" "$output/negatives"
# Snapshot proof/registry/controller inputs independently of cached build output.
sources=(lean-toolchain lake-manifest.json ./*.lean
    scripts/verify-logical64.sh scripts/verify-logical64-native.sh
    scripts/check-audit.sh scripts/Audit.lean .github/workflows/logical64-clients.yml
    fixtures/logical64.c fixtures/logical64-check.c fixtures/logical64-check.S)
find EDSL Tools tests -type f -name '*.lean' -print0 | sort -z > "$output/source-files.nul"
while IFS= read -r -d '' file; do sources+=("$file"); done < "$output/source-files.nul"
sha256sum "${sources[@]}" > "$output/source-SHA256SUMS"
for file in "${sources[@]}"; do install -D -m 0644 "$file" "$output/source/$file"; done
(cd "$output/source" && sha256sum --quiet --check ../source-SHA256SUMS) \
    > "$output/source-copy-check.txt" 2>&1
expect_status() {
    local expected=$1 label=$2
    shift 2
    local actual=0
    record_command "$@" > "$output/logs/$label-arguments.txt"
    "$@" > "$output/logs/$label.txt" 2>&1 || actual=$?
    printf '%s\n' "$actual" > "$output/logs/$label-status.txt"
    if [[ $actual -ne $expected ]]; then
        tail -n 60 "$output/logs/$label.txt" >&2
        printf 'Expected %s for %s, got %s\n' "$expected" "$label" "$actual" >&2
        exit 1
    fi
}
expect_status 0 native env EDSL_LOGICAL64_OUTPUT="$output/native" bash scripts/verify-logical64-native.sh
find "$output/native" -mindepth 1 -maxdepth 1 -type d -name 'run.*' -print0 \
    > "$output/native-directories.nul"
mapfile -d '' -t native_runs < "$output/native-directories.nul"
if [[ ${#native_runs[@]} -ne 1 ]]; then
    echo 'Expected exactly one fresh native evidence directory' >&2
    exit 1
fi
native=${native_runs[0]}
lean=(env LEAN_NUM_THREADS=1 flock /tmp/edsl-lean-build.lock lake)
expect_status 0 build "${lean[@]}" build EDSL.All edsl-grade edsl-proof-export tests.fixtures.Logical64
expect_status 0 contract-tests "${lean[@]}" env lean -DwarningAsError=true tests/Logical64.lean
expect_status 0 registry-tests "${lean[@]}" env lean -DwarningAsError=true tests/GradingLogical64.lean
expect_status 0 audit env LEAN_NUM_THREADS=1 flock /tmp/edsl-lean-build.lock bash scripts/check-audit.sh
expect_status 0 fresh-project "${lean[@]}" env leanchecker --fresh EDSL.All
expect_status 0 fresh-client "${lean[@]}" env leanchecker --fresh tests.fixtures.Logical64
functions=(intersection64 union64 symmetric_difference64)
tasks=(intersection64 union64 symmetricDifference64)
claims=(intersection union symmetricDifference)
module=tests.fixtures.Logical64
for index in "${!functions[@]}"; do
    function=${functions[$index]}
    task=${tasks[$index]}
    theorem="EDSL.Logical64.Client.${claims[$index]}"
    expect_status 0 "$task-isolation" "${lean[@]}" env lean -DwarningAsError=true \
        --run tests/GradingIsolation.lean "$module" "$theorem"
    for mode in reference body; do
        options=()
        if [[ $mode == body ]]; then options=(--body); fi
        packet="$output/packets/$task-$mode.json"
        expect_status 0 "$task-export-$mode" "${lean[@]}" env edsl-proof-export \
            "$module" "$theorem" "$packet" "${options[@]}"
        for compiler in gcc clang; do
            directory="$native/$compiler/$function"
            raw="$directory/function.bin"
            elf="$directory/function.elf"
            span=$(< "$directory/span.txt")
            expect_status 0 "$task-$compiler-raw-$mode" "${lean[@]}" env edsl-grade "$task" "$raw" "$packet"
            expect_status 0 "$task-$compiler-elf-$mode" "${lean[@]}" env edsl-grade \
                --elf "$span" "$task" "$elf" "$packet"
        done
    done
    wrong_task=${tasks[$(((index + 1) % 3))]}
    for compiler in gcc clang; do
        directory="$native/$compiler/$function"
        raw="$directory/function.bin"
        span=$(< "$directory/span.txt")
        packet="$output/packets/$task-body.json"
        expect_status 5 "$task-$compiler-wrong-task" "${lean[@]}" env edsl-grade "$wrong_task" "$raw" "$packet"
        expect_status 5 "$task-$compiler-short-span" "${lean[@]}" env edsl-grade \
            --elf "$((span - 1))" "$task" "$directory/function.elf" "$packet"
        altered="$output/negatives/$task-$compiler-altered.bin"
        cp "$raw" "$altered"
        printf '\x90' | dd of="$altered" bs=1 seek=3 count=1 conv=notrunc status=none
        expect_status 5 "$task-$compiler-altered" "${lean[@]}" env edsl-grade "$task" "$altered" "$packet"
        extended="$output/negatives/$task-$compiler-extended.bin"
        cp "$raw" "$extended"
        printf '\x90' >> "$extended"
        expect_status 5 "$task-$compiler-extended" "${lean[@]}" env edsl-grade "$task" "$extended" "$packet"
    done
done
# Detect any concurrent source change, rather than binding a run to stale inputs.
sha256sum --quiet --check "$output/source-SHA256SUMS" > "$output/source-stability.txt" 2>&1
cat > "$output/scope.txt" <<'SCOPE'
Full logical64 verification under the recorded sequential callable profile:
independent per-bit intersection/union/symmetric-difference contracts, arbitrary
full64 arguments/registers/flags, all AF streams, actual RET, full RAM/permission
and SysV/nonarithmetic-flag frames, current original code/caller-slot loans and
all reachable-prefix read permissions. Admission contains no future-success,
decoding, CFG, compiler or cost requirement. The selected implementations have
exactly three retired model instructions and one original STACK8 read; a
separate generic theorem gives at least two when incoming RAX must change.
No global three-instruction optimum or physical timing bound is established.

The trusted registry imports generic contracts and independently constructed
domains, excluding compiler-client proofs. Six serialized reference/body packets
for three clients grade 24 raw/full-ELF cases covering both fresh GCC13/Clang18
outputs. The compilers emit identical seven-byte windows per operation, so the
same byte-bound packet correctly applies to both. Compiler identity is not an
admission condition. Twenty-four status-5 negatives alter task, selected span,
internal bytes or raw suffix. Those reject packet binding, not prove a defect.
Actual wrong-result/fault refutations are separate kernel-checked regressions.
Packet/axiom/resource limits retain their existing values.

Build traces reuse caches, with fresh kernel replay of EDSL and the client,
transitive axiom audit plus its negative probe, public driver/registry tests,
and trusted-snapshot client isolation. Source copies, commands, statuses and
hashes are retained, including honest incomplete failure evidence.

The nested native evidence separately records finite whole-call observations,
arithmetic-flag acceptance controls, owned mutants and pre-execution extraction
rejections. It does not establish universal CPU/kernel conformance or whole RAM
physical tracing. The model assumes stable ordinary sequential RAM, no MMIO or
asynchronous interference, four-level canonical addresses, disabled alignment
checking and ordinary RET without CET. Native loading/CPU behavior and logical
worker interpretation remain environmental boundaries. No source/IR preservation,
whole-OS proof, concurrency, speculation or cycle guarantee is claimed.
SCOPE
echo 'PASS: universal model/resource proofs, audits, fresh replay, isolation, raw/ELF proof grading and separate finite native evidence' \
    > "$output/result.txt"
echo 'Logical64 compiler clients, fixed-task proof grading and native contracts passed'
