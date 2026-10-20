#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."
output=${EDSL_FUTEX_PREDICATE_ROOT:-artifacts/futex-predicate}
if [[ -e $output ]]; then
    echo "Refusing to overwrite evidence directory: $output" >&2
    exit 2
fi
mkdir -p "$output"

# Native observations retain their own status and provenance. Formal checking
# below binds the identical final windows; neither phase substitutes for the other.
EDSL_FUTEX_PREDICATE_OUTPUT="$output/native" bash scripts/verify-futex-predicate-native.sh
grep -qx 'checked_final_native_harnesses=2' "$output/native/result.txt"
grep -qx 'checked_standalone_ELF_sets=2' "$output/native/result.txt"

rejected=0
expect_unverified() {
    local log=$1
    shift
    local edsl_rejection_rc=0
    "$@" > "$log" 2>&1 || edsl_rejection_rc=$?
    if (( edsl_rejection_rc != 3 )) || ! grep -q '^UNVERIFIED:' "$log"; then
        cat "$log"
        echo 'FAIL: owned unsupported artifact was not rejected for the expected reason' >&2
        exit 1
    fi
    rejected=$((rejected + 1))
}

for compiler in clang gcc; do
    native="$output/native/$compiler"
    certificates="$output/$compiler"
    mkdir "$certificates"
    for window in wait.object wait.linked wait.native-linked; do
        lake exe edsl-certify-futex-predicate wait-recheck "$native/$window.bin" \
            "$certificates/$window.lean" > "$certificates/$window.log" 2>&1
    done
    lake exe edsl-certify-futex-predicate --elf wait-recheck "$native/wait.elf" \
        "$certificates/full-elf.lean" > "$certificates/full-elf.log" 2>&1
    expect_unverified "$certificates/no-recheck-raw.log" \
        lake exe edsl-certify-futex-predicate wait-recheck "$native/no-recheck.native-linked.bin" \
            "$certificates/rejected-raw.lean"
    expect_unverified "$certificates/no-recheck-elf.log" \
        lake exe edsl-certify-futex-predicate --elf wait-recheck "$native/no-recheck.elf" \
            "$certificates/rejected-elf.lean"
done

{
    printf 'native=OBSERVED\nformal=CHECKED\npositive_certificates=8\nowned_artifact_rejections=%d\n' "$rejected"
    printf 'Exact object/final windows and standalone ELF entry bind to the conditional Lean signal0/1 WAIT0 model.\n'
    printf 'Current resource admission, ABI and environment remain explicit premises.\n'
    printf 'No fairness, hardware timing, minimum-operation, multiple-waiter or kernel-refinement conclusion.\n'
} > "$output/result.txt"
if ! (cd "$output" && find . -type f ! -name ARTIFACTS.SHA256SUMS -exec sha256sum {} +) \
    > "$output/ARTIFACTS.SHA256SUMS"; then
    rm -f "$output/result.txt" "$output/ARTIFACTS.SHA256SUMS"
    echo 'FAIL: evidence manifest could not be completed' >&2
    exit 1
fi
cat "$output/result.txt"
