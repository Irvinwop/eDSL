#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail
export LC_ALL=C LEAN_NUM_THREADS=1
if [[ $# -ne 0 ]]; then echo 'usage: verify-atomic-set64-grading.sh' >&2; exit 2; fi
cd "$(dirname "${BASH_SOURCE[0]}")/.."
archive=${EDSL_ATOMIC_SET64_GRADING_OUTPUT:-artifacts/atomic-set64-grading}
mkdir -p "$archive"
archive=$(cd "$archive" && pwd -P)
output=$(mktemp -d "$archive/run.XXXXXXXX")
printf 'Atomic set proof grading: %s\n' "$output"
phase=initialization
complete=0
original_paths=()
restore_clients() {
    local index saved
    for ((index=${#original_paths[@]}-1; index>=0; index--)); do
        saved="$output/hidden/$index"
        if [[ -f $saved ]]; then
            if [[ -e ${original_paths[index]} || -L ${original_paths[index]} ]]; then
                printf 'Refusing to overwrite restored client: %s\n' "${original_paths[index]}" >&2
                return 1
            fi
            mv -- "$saved" "${original_paths[index]}" || return 1
        elif [[ ! -f ${original_paths[index]} ]]; then
            printf 'Missing original and saved client: %s\n' "${original_paths[index]}" >&2
            return 1
        fi
    done
    original_paths=()
}
hide_file() {
    local original=$1 saved="$output/hidden/${#original_paths[@]}"
    [[ -f $original ]] || return 0
    # Register before the atomic rename so an interrupt at either boundary
    # can recover the file. Restoration also handles a registered pending move.
    original_paths+=("$original")
    mv -- "$original" "$saved"
}
write_hashes() {
    (cd "$output" && find . -type f ! -name SHA256SUMS -print0 | sort -z | xargs -0 sha256sum) > "$output/SHA256SUMS"
}
finish() {
    local status=$?
    trap - EXIT
    trap '' INT TERM HUP
    restore_clients || status=1
    if [[ $status -ne 0 || $complete -ne 1 ]]; then
        [[ $status -ne 0 ]] || status=1
        printf 'INCOMPLETE: exit=%s phase=%s; no complete verification claim\n' "$status" "$phase" > "$output/result.txt"
    fi
    printf '%s\n' "$status" > "$output/script-status.txt"
    if ! write_hashes || ! (cd "$output" && sha256sum --quiet --check SHA256SUMS); then
        status=1
        echo 'INCOMPLETE: manifest creation/verification failed' > "$output/result.txt"
        printf '%s\n' "$status" > "$output/script-status.txt"
        write_hashes || true
    fi
    printf 'Atomic set grading exit=%s phase=%s: %s\n' "$status" "$phase" "$output"
    exit "$status"
}
trap finish EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
trap 'exit 129' HUP
echo 'INCOMPLETE: checks have not finished' > "$output/result.txt"
record() { printf '%q ' "$@"; printf '\n'; }
run() { record "$@" >> "$output/commands.txt"; "$@"; }
expect() {
    local expected=$1 label=$2 status=0
    shift 2
    record "$@" > "$output/$label.arguments.txt"
    "$@" > "$output/$label.log" 2>&1 || status=$?
    printf '%s\n' "$status" > "$output/$label.status.txt"
    printf '%s\t%s\t%s\n' "$label" "$expected" "$status" >> "$output/statuses.tsv"
    if [[ $status -ne $expected ]]; then
        tail -n 25 "$output/$label.log" >&2
        printf 'Unexpected %s status: expected %s, got %s\n' "$label" "$expected" "$status" >&2
        exit 1
    fi
}

phase=snapshot
mapfile -d '' sources < <(find EDSL -type f -name '*.lean' -print0 | sort -z)
sources+=(lean-toolchain lakefile.lean lake-manifest.json EDSL.lean Tools/Grade/AtomicSet64.lean
    scripts/verify-atomic-set64-grading.sh .github/workflows/atomic-set64-grading.yml
    fixtures/atomic-set64-grading.c fixtures/atomic-set64-grading-check.c
    tests/AtomicSet64Grading.lean tests/AtomicSet64GradingPackets.lean
    tests/fixtures/AtomicSet64Grading.lean tests/GradingIsolation.lean)
run sha256sum "${sources[@]}" > "$output/source-SHA256SUMS"
for file in "${sources[@]}"; do install -D -m 0644 "$file" "$output/source/$file"; done
(cd "$output/source" && sha256sum --quiet --check "$output/source-SHA256SUMS")
run git rev-parse HEAD > "$output/repository-head.txt"
run date -u +%FT%TZ > "$output/start-utc.txt"
run bash -n scripts/verify-atomic-set64-grading.sh
run shellcheck -s bash scripts/verify-atomic-set64-grading.sh > "$output/shellcheck.txt" 2>&1

implementations=(And Or Xor AndTwice OrTwice XorThrice MixedUnion)
tasks=(intersection union symmetricDifference intersection union symmetricDifference union)
phase=compiler_artifacts
for compiler in gcc-13 clang-18; do
    run "$compiler" --version > "$output/$compiler-version.txt"
    expect 0 "$compiler-observer-build" "$compiler" -std=gnu2x -O2 -Wall -Wextra -Werror \
        "$output/source/fixtures/atomic-set64-grading-check.c" -o "$output/$compiler-observer"
    for index in "${!implementations[@]}"; do
        implementation=${implementations[index]}
        directory="$output/$compiler-$implementation"
        mkdir -p "$directory"
        expect 0 "$compiler-$implementation-compile" "$compiler" -std=gnu2x -O2 -Wall -Wextra -Werror \
            -ffreestanding -fno-pic -fno-pie -fno-stack-protector -fcf-protection=none \
            -fno-asynchronous-unwind-tables -fno-unwind-tables -DEDSL_IMPLEMENTATION="$index" \
            -c "$output/source/fixtures/atomic-set64-grading.c" -o "$directory/function.o"
        expect 0 "$compiler-$implementation-link" ld --entry atomic_set64_grading --section-start .text=0x401000 \
            -nostdlib -static -z noexecstack --build-id=none "$directory/function.o" -o "$directory/function.elf"
        run objcopy --dump-section ".text=$directory/function.bin" "$directory/function.elf"
        run readelf -aW "$directory/function.elf" > "$directory/readelf.txt"
        run objdump -d "$directory/function.elf" > "$directory/disassembly.txt"
        wc -c < "$directory/function.bin" > "$directory/span.txt"
    done
done

phase=build_and_contracts
lean=(env LEAN_NUM_THREADS=1 flock /tmp/edsl-lean-build.lock lake)
expect 0 build "${lean[@]}" build EDSL.Grading.AtomicSet64 EDSL.Audit \
    EDSL.X86.StackRead64 +tests.fixtures.AtomicSet64Grading edsl-grade-atomic-set64 edsl-proof-export
expect 0 contract-tests "${lean[@]}" env lean -DwarningAsError=true tests/AtomicSet64Grading.lean
expect 0 packet-tests "${lean[@]}" env lean -DwarningAsError=true tests/AtomicSet64GradingPackets.lean

phase=client_export
cat > "$output/Submission.lean" <<'LEAN'
import tests.fixtures.AtomicSet64Grading
namespace EDSL.Tests.Fixtures.AtomicSet64Grading.Submission
open EDSL.Grading.AtomicSet64
private theorem helperAnd : Claim .intersection (encode [.band]) := claimAnd
private theorem helperOr : Claim .union (encode [.bor]) := claimOr
private theorem helperXor : Claim .symmetricDifference (encode [.bxor]) := claimXor
private theorem helperAndTwice : Claim .intersection (encode [.band, .band]) := claimAndTwice
private theorem helperOrTwice : Claim .union (encode [.bor, .bor]) := claimOrTwice
private theorem helperXorThrice : Claim .symmetricDifference (encode [.bxor, .bxor, .bxor]) := claimXorThrice
private theorem helperMixedUnion : Claim .union (encode [.bxor, .bxor, .bor]) := claimMixedUnion
theorem And : Claim .intersection (encode [.band]) := helperAnd
theorem Or : Claim .union (encode [.bor]) := helperOr
theorem Xor : Claim .symmetricDifference (encode [.bxor]) := helperXor
theorem AndTwice : Claim .intersection (encode [.band, .band]) := helperAndTwice
theorem OrTwice : Claim .union (encode [.bor, .bor]) := helperOrTwice
theorem XorThrice : Claim .symmetricDifference (encode [.bxor, .bxor, .bxor]) := helperXorThrice
theorem MixedUnion : Claim .union (encode [.bxor, .bxor, .bor]) := helperMixedUnion
theorem wrong : True := True.intro
end EDSL.Tests.Fixtures.AtomicSet64Grading.Submission
LEAN
proof_path="$output:$(lake env printenv LEAN_PATH)"
expect 0 client-compile "${lean[@]}" env env LEAN_PATH="$proof_path" lean -R "$output" \
    -DwarningAsError=true -o "$output/Submission.olean" "$output/Submission.lean"
for implementation in "${implementations[@]}"; do
    theorem="EDSL.Tests.Fixtures.AtomicSet64Grading.Submission.$implementation"
    expect 0 "$implementation-isolation" "${lean[@]}" env env LEAN_PATH="$proof_path" \
        lean -DwarningAsError=true --run tests/GradingIsolation.lean Submission "$theorem"
    for mode in reference body; do
        options=()
        if [[ $mode == body ]]; then options=(--body); fi
        expect 0 "$implementation-export-$mode" "${lean[@]}" env env LEAN_PATH="$proof_path" \
            .lake/build/bin/edsl-proof-export Submission "$theorem" "$output/$implementation-$mode.json" "${options[@]}"
    done
done
expect 0 wrong-export "${lean[@]}" env env LEAN_PATH="$proof_path" .lake/build/bin/edsl-proof-export \
    Submission EDSL.Tests.Fixtures.AtomicSet64Grading.Submission.wrong "$output/wrong.json" --body

phase=packet_only_grading
mkdir -p "$output/hidden" "$output/poison"
hide_file "$output/Submission.lean"
hide_file "$output/Submission.olean"
hide_file tests/fixtures/AtomicSet64Grading.lean
for suffix in olean olean.private olean.server; do
    hide_file ".lake/build/lib/lean/tests/fixtures/AtomicSet64Grading.$suffix"
done
for module in EDSL/Grading/Known EDSL/Grading/Artifact EDSL/Grading/CallStack/Artifact \
    EDSL/Grading/CallMemory64/Artifact EDSL/Grading/CallMemoryLoop64/Artifact \
    EDSL/Grading/AtomicLogical64/Artifact EDSL/Grading/AtomicSet64/Artifact \
    tests/fixtures/AtomicSet64Grading Submission; do
    mkdir -p "$output/poison/${module%/*}"
    for suffix in olean olean.private olean.server so; do
        printf 'Untrusted LEAN_PATH sentinel; deliberately not a Lean object\n' > "$output/poison/$module.$suffix"
    done
done
grader=("${lean[@]}" env .lake/build/bin/edsl-grade-atomic-set64)
for compiler in gcc-13 clang-18; do
    for index in "${!implementations[@]}"; do
        implementation=${implementations[index]}
        task=${tasks[index]}
        directory="$output/$compiler-$implementation"
        span=$(< "$directory/span.txt")
        for mode in reference body; do
            packet="$output/$implementation-$mode.json"
            expect 0 "$compiler-$implementation-raw-$mode" "${grader[@]}" "$task" "$directory/function.bin" "$packet"
            expect 0 "$compiler-$implementation-elf-$mode" "${grader[@]}" "$task" --elf "$span" "$directory/function.elf" "$packet"
        done
        other=union
        [[ $task == union ]] && other=intersection
        expect 5 "$compiler-$implementation-crossed-task" "${grader[@]}" "$other" "$directory/function.bin" "$output/$implementation-body.json"
        expect 5 "$compiler-$implementation-short-span" "${grader[@]}" "$task" --elf "$((span - 1))" \
            "$directory/function.elf" "$output/$implementation-body.json"
        cp "$directory/function.elf" "$directory/metadata.elf"
        printf '\177' >> "$directory/metadata.elf"
        expect 0 "$compiler-$implementation-metadata" "${grader[@]}" "$task" --elf "$span" \
            "$directory/metadata.elf" "$output/$implementation-body.json"
        expect 0 "$compiler-$implementation-poison" "${lean[@]}" env env LEAN_PATH="$output/poison" \
            .lake/build/bin/edsl-grade-atomic-set64 "$task" "$directory/function.bin" "$output/$implementation-body.json"
        printf '["edsl-proof-v1",[],["const",["EDSL","Tests","Fixtures","AtomicSet64Grading","Submission","%s"],[]]]\n' \
            "$implementation" > "$output/$implementation-bare.json"
        expect 4 "$compiler-$implementation-bare-reference" "${grader[@]}" "$task" \
            "$directory/function.bin" "$output/$implementation-bare.json"
        expect 4 "$compiler-$implementation-poison-reference" "${lean[@]}" env env LEAN_PATH="$output/poison" \
            .lake/build/bin/edsl-grade-atomic-set64 "$task" "$directory/function.bin" "$output/$implementation-bare.json"
    done
done
expect 5 crossed-solution "${grader[@]}" union "$output/gcc-13-Or/function.bin" "$output/MixedUnion-body.json"
expect 5 wrong-contract "${grader[@]}" union "$output/gcc-13-Or/function.bin" "$output/wrong.json"
printf '{' > "$output/malformed.json"
expect 4 malformed-packet "${grader[@]}" union "$output/gcc-13-Or/function.bin" "$output/malformed.json"
printf '\360\110\011\067' > "$output/truncated.bin"
expect 5 truncated-binding "${grader[@]}" union "$output/truncated.bin" "$output/Or-body.json"
dd if=/dev/zero of="$output/oversize.bin" bs=4097 count=1 status=none
expect 6 bounded-raw "${grader[@]}" union "$output/oversize.bin" "$output/Or-body.json"
expect 2 unknown-task "${grader[@]}" Union "$output/gcc-13-Or/function.bin" "$output/Or-body.json"
run restore_clients

phase=native_observations
for compiler in gcc-13 clang-18; do
    for index in "${!implementations[@]}"; do
        implementation=${implementations[index]}
        task=${tasks[index]}
        directory="$output/$compiler-$implementation"
        for observer in gcc-13 clang-18; do
            expect 0 "$compiler-$implementation-native-$observer" "$output/$observer-observer" \
                "$task" "$directory/function.bin" "$directory/function.elf"
            other=union
            [[ $task == union ]] && other=intersection
            expect 1 "$compiler-$implementation-native-wrong-task-$observer" "$output/$observer-observer" \
                "$other" "$directory/function.bin" "$directory/function.elf"
        done
    done
done

phase=fresh_kernel
cat > "$output/Replay.lean" <<'LEAN'
import EDSL.Grading.AtomicSet64
import Submission
import EDSL.Audit
#audit_edsl
#print axioms EDSL.Tests.Fixtures.AtomicSet64Grading.claimMixedUnion
#print axioms EDSL.Grading.AtomicSet64.Claim.actual_lower_bound
LEAN
expect 0 replay-stored "${lean[@]}" env env LEAN_PATH="$proof_path" lean -R "$output" \
    -DwarningAsError=true -o "$output/Replay.olean" "$output/Replay.lean"
expect 0 replay-fresh "${lean[@]}" env env LEAN_PATH="$proof_path" leanchecker --fresh Replay

phase=source_stability
run sha256sum --quiet --check "$output/source-SHA256SUMS" > "$output/source-stability.txt"
cat > "$output/scope.txt" <<'SCOPE'
Independent full64 set tasks under original named actor/code/caller resources,
all AF streams, actual covered CPU/OS transitions and returned current world.
Admission has no opcode, count, compiler-shape or future-success restriction.
Seven implementations include mixed XOR/XOR/OR union with three actual events.
GCC/Clang raw/full-ELF artifacts use fresh reference/body data-only packets;
client/helper source and objects leave their import paths during grading.
Poisoned search paths and unknown references cannot supply trusted declarations.
Each wrapper binds its entire literal file/window. Nonloaded metadata may vary.
Separate finite native observations bind ELF entry, raw bytes and loaded slot,
then check independent set membership and neighboring RAM. They do not measure
events or establish model/physical correspondence, flags/ABI or concurrency.
These are uninterrupted callable model results, not compound-call linearizability,
whole-process coverage, compiler/source-order, physical LOCK, TSO or OS refinement.
SCOPE
echo 'PASS: three atomic set tasks, seven compiler solutions, packet-only raw/full-ELF grading, native observations, audits and fresh replay' > "$output/result.txt"
complete=1
phase=complete
