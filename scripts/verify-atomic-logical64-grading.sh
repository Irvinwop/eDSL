#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail
export LC_ALL=C LEAN_NUM_THREADS=1
if [[ $# -ne 0 ]]; then echo 'usage: verify-atomic-logical64-grading.sh' >&2; exit 2; fi
cd "$(dirname "${BASH_SOURCE[0]}")/.."
archive=${EDSL_ATOMIC64_GRADING_OUTPUT:-artifacts/atomic-logical64-grading}
mkdir -p "$archive"
archive=$(cd "$archive" && pwd -P)
output=$(mktemp -d "$archive/run.XXXXXXXX")
printf 'Atomic union proof grading: %s\n' "$output"
phase=initialization
complete=0
hidden=0
restore_client() {
    if [[ $hidden -eq 1 ]]; then
        mv "$output/hidden/Submission.lean" "$output/Submission.lean"
        mv "$output/hidden/Submission.olean" "$output/Submission.olean"
        hidden=0
    fi
}
write_hashes() {
    (cd "$output" && find . -type f ! -name SHA256SUMS -print0 | sort -z | xargs -0 sha256sum) > "$output/SHA256SUMS"
}
finish() {
    local status=$?
    trap - EXIT
    restore_client || status=1
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
    printf 'Atomic union grading exit=%s phase=%s: %s\n' "$status" "$phase" "$output"
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
sources+=(lean-toolchain lakefile.lean lake-manifest.json EDSL.lean AtomicLogical64GradeMain.lean
    scripts/verify-atomic-logical64-grading.sh .github/workflows/atomic-logical64-grading.yml
    fixtures/atomic-logical64.c fixtures/atomic-logical64-twice.c
    tests/AtomicLogical64Domain.lean tests/AtomicLogical64Grading.lean tests/GradingIsolation.lean)
run sha256sum "${sources[@]}" > "$output/source-SHA256SUMS"
for file in "${sources[@]}"; do install -D -m 0644 "$file" "$output/source/$file"; done
(cd "$output/source" && sha256sum --quiet --check "$output/source-SHA256SUMS")
run git rev-parse HEAD > "$output/repository-head.txt"
run date -u +%FT%TZ > "$output/start-utc.txt"
run bash -n scripts/verify-atomic-logical64-grading.sh
run shellcheck -s bash scripts/verify-atomic-logical64-grading.sh > "$output/shellcheck.txt" 2>&1

phase=compiler_artifacts
for compiler in gcc-13 clang-18; do
    run "$compiler" --version > "$output/$compiler-version.txt"
    for implementation in once twice; do
        directory="$output/$compiler-$implementation"
        mkdir -p "$directory"
        source=fixtures/atomic-logical64.c
        symbol=atomic_or64_discard
        if [[ $implementation == twice ]]; then
            source=fixtures/atomic-logical64-twice.c
            symbol=atomic_or64_discard_twice
        fi
        expect 0 "$compiler-$implementation-compile" "$compiler" -std=gnu2x -O2 -Wall -Wextra -Werror \
            -ffreestanding -fno-pic -fno-pie -fno-stack-protector -fcf-protection=none \
            -fno-asynchronous-unwind-tables -fno-unwind-tables -c "$output/source/$source" -o "$directory/function.o"
        expect 0 "$compiler-$implementation-link" ld --entry "$symbol" --section-start .text=0x401000 \
            -nostdlib -static -z noexecstack --build-id=none "$directory/function.o" -o "$directory/function.elf"
        run objcopy --dump-section ".text=$directory/function.bin" "$directory/function.elf"
        run readelf -aW "$directory/function.elf" > "$directory/readelf.txt"
        run objdump -d "$directory/function.elf" > "$directory/disassembly.txt"
        wc -c < "$directory/function.bin" > "$directory/span.txt"
    done
done

phase=build_and_contracts
lean=(env LEAN_NUM_THREADS=1 flock /tmp/edsl-lean-build.lock lake)
expect 0 build "${lean[@]}" build EDSL.Grading.AtomicLogical64 EDSL.Grading.AtomicLogical64.Clients \
    EDSL.Grading.AtomicLogical64.Artifact edsl-grade-atomic-logical64 edsl-proof-export
expect 0 domain-tests "${lean[@]}" env lean -DwarningAsError=true tests/AtomicLogical64Domain.lean
expect 0 contract-tests "${lean[@]}" env lean -DwarningAsError=true tests/AtomicLogical64Grading.lean

phase=client_export
cat > "$output/Submission.lean" <<'LEAN'
import EDSL.Grading.AtomicLogical64.Clients
namespace EDSL.Grading.AtomicLogical64.OwnedSubmission
private theorem auxiliary5 : Claim Clients.bytes5 := Clients.claim5
private theorem auxiliary9 : Claim Clients.bytes9 := Clients.claim9
theorem once : Claim Clients.bytes5 := auxiliary5
theorem twice : Claim Clients.bytes9 := auxiliary9
theorem wrong : True := True.intro
end EDSL.Grading.AtomicLogical64.OwnedSubmission
LEAN
proof_path="$output:$(lake env printenv LEAN_PATH)"
expect 0 client-compile "${lean[@]}" env env LEAN_PATH="$proof_path" lean -R "$output" \
    -DwarningAsError=true -o "$output/Submission.olean" "$output/Submission.lean"
cat > "$output/Isolation.lean" <<'LEAN'
import EDSL.Grading.Export
open Lean EDSLGrader
def main : IO Unit := do
  let (trusted, client) ← Export.loadEnvironments `Submission
  for name in [`EDSL.Grading.AtomicLogical64.Clients.claim5,
      `EDSL.Grading.AtomicLogical64.Clients.claim9,
      `EDSL.Grading.AtomicLogical64.OwnedSubmission.once,
      `EDSL.Grading.AtomicLogical64.OwnedSubmission.twice] do
    if (trusted.toKernelEnv.find? name).isSome then
      throw (IO.userError s!"client entered trusted snapshot: {name}")
    if (client.toKernelEnv.find? name).isNone then
      throw (IO.userError s!"export client lacks theorem: {name}")
  IO.println "Client solution and auxiliary theorems are absent from the fixed trusted snapshot"
LEAN
expect 0 snapshot-isolation "${lean[@]}" env env LEAN_PATH="$proof_path" \
    lean -DwarningAsError=true --run "$output/Isolation.lean"
for implementation in once twice; do
    theorem="EDSL.Grading.AtomicLogical64.OwnedSubmission.$implementation"
    for mode in reference body; do
        options=()
        if [[ $mode == body ]]; then options=(--body); fi
        expect 0 "$implementation-export-$mode" "${lean[@]}" env env LEAN_PATH="$proof_path" \
            .lake/build/bin/edsl-proof-export Submission "$theorem" "$output/$implementation-$mode.json" "${options[@]}"
    done
done
expect 0 wrong-export "${lean[@]}" env env LEAN_PATH="$proof_path" .lake/build/bin/edsl-proof-export \
    Submission EDSL.Grading.AtomicLogical64.OwnedSubmission.wrong "$output/wrong.json" --body

phase=packet_only_grading
mkdir -p "$output/hidden"
run mv "$output/Submission.lean" "$output/hidden/Submission.lean"
run mv "$output/Submission.olean" "$output/hidden/Submission.olean"
hidden=1
grader=("${lean[@]}" env .lake/build/bin/edsl-grade-atomic-logical64)
for compiler in gcc-13 clang-18; do
    for implementation in once twice; do
        directory="$output/$compiler-$implementation"
        span=$(< "$directory/span.txt")
        for mode in reference body; do
            packet="$output/$implementation-$mode.json"
            expect 0 "$compiler-$implementation-raw-$mode" "${grader[@]}" "$directory/function.bin" "$packet"
            expect 0 "$compiler-$implementation-elf-$mode" "${grader[@]}" --elf "$span" "$directory/function.elf" "$packet"
        done
        other=once
        [[ $implementation != once ]] || other=twice
        expect 5 "$compiler-$implementation-other-proof" "${grader[@]}" "$directory/function.bin" "$output/$other-body.json"
        expect 5 "$compiler-$implementation-short-span" "${grader[@]}" --elf "$((span - 1))" \
            "$directory/function.elf" "$output/$implementation-body.json"
        cp "$directory/function.elf" "$directory/metadata.elf"
        printf '\177' >> "$directory/metadata.elf"
        expect 0 "$compiler-$implementation-metadata" "${grader[@]}" --elf "$span" \
            "$directory/metadata.elf" "$output/$implementation-body.json"
    done
done
expect 5 wrong-contract "${grader[@]}" "$output/gcc-13-once/function.bin" "$output/wrong.json"
printf '{' > "$output/malformed.json"
expect 4 malformed-packet "${grader[@]}" "$output/gcc-13-once/function.bin" "$output/malformed.json"
printf '\360\110\011\067' > "$output/truncated.bin"
expect 5 truncated-binding "${grader[@]}" "$output/truncated.bin" "$output/once-body.json"
dd if=/dev/zero of="$output/oversize.bin" bs=4097 count=1 status=none
expect 6 bounded-raw "${grader[@]}" "$output/oversize.bin" "$output/once-body.json"
run restore_client

phase=fresh_kernel
cat > "$output/Replay.lean" <<'LEAN'
import EDSL.Grading.AtomicLogical64
import Submission
import EDSL.Audit
#audit_edsl
#print axioms EDSL.Grading.AtomicLogical64.Clients.claim5
#print axioms EDSL.Grading.AtomicLogical64.Clients.claim9
#print axioms EDSL.Grading.AtomicLogical64.Claim.actual_lower_bound
LEAN
expect 0 replay-stored "${lean[@]}" env env LEAN_PATH="$proof_path" lean -R "$output" \
    -DwarningAsError=true -o "$output/Replay.olean" "$output/Replay.lean"
expect 0 replay-fresh "${lean[@]}" env env LEAN_PATH="$proof_path" leanchecker --fresh Replay

phase=source_stability
run sha256sum --quiet --check "$output/source-SHA256SUMS" > "$output/source-stability.txt"
cat > "$output/scope.txt" <<'SCOPE'
Fixed independent discarded full64 union under current named actor/code/caller
resources, all AF streams, actual covered CPU/OS transitions and returned current
world. No instruction/event-count, opcode-list, compiler shape or future-success
admission gate. Five-byte and nine-byte implementations retain one/two real RMWs
and two/three retired instructions, separately from the shared task contract.
Fresh GCC/Clang raw/full-ELF artifacts are graded using both reference/body data
packets after the auxiliary client's source and olean leave its import location.
The fixed installed environment excludes Clients and the submission module.
Every artifact wrapper binds its own entire literal file and selected window;
unexecuted ELF metadata may differ while a byte-code proof remains applicable.
This window profile does not claim whole-process executable coverage or startup.
No native execution, C/source-order, concurrent linearizability, physical LOCK,
TSO, pthread/kernel or complete OS refinement is established by this job.
Physical/control/object-lifetime assumptions remain those of the locked profile.
SCOPE
echo 'PASS: fixed atomic union task, two distinct compiler solutions, packet-only raw/full-ELF grading, audits and fresh replay' > "$output/result.txt"
complete=1
phase=complete
