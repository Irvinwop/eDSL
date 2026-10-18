#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail
export LC_ALL=C
export LEAN_NUM_THREADS=1
if [[ $# -ne 0 ]]; then echo 'usage: verify-atomic-logical64.sh' >&2; exit 2; fi
cd "$(dirname "${BASH_SOURCE[0]}")/.."
archive=${EDSL_ATOMIC64_OUTPUT:-artifacts/atomic-logical64}
mkdir -p "$archive"
archive=$(cd "$archive" && pwd -P)
output=$(mktemp -d "$archive/run.XXXXXXXX")
printf 'AtomicLogical64 verification: %s\n' "$output"
phase=initialization
complete=0
write_hashes() {
    (cd "$output" && find . -type f ! -name SHA256SUMS -print0 | sort -z | xargs -0 sha256sum) \
        > "$output/SHA256SUMS"
}
finish() {
    local status=$?
    trap - EXIT
    if [[ $status -ne 0 || $complete -ne 1 ]]; then
        [[ $status -ne 0 ]] || status=1
        printf 'INCOMPLETE: exit=%s phase=%s; no complete verification claim\n' "$status" "$phase" \
            > "$output/result.txt"
    fi
    printf '%s\n' "$status" > "$output/script-status.txt"
    if ! write_hashes || ! (cd "$output" && sha256sum --quiet --check SHA256SUMS); then
        status=1
        echo 'INCOMPLETE: manifest creation/verification failed' > "$output/result.txt"
        printf '%s\n' "$status" > "$output/script-status.txt"
        write_hashes || true
    fi
    printf 'AtomicLogical64 exit=%s phase=%s: %s\n' "$status" "$phase" "$output"
    exit "$status"
}
trap finish EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
trap 'exit 129' HUP
echo 'INCOMPLETE: checks have not finished' > "$output/result.txt"
record_command() { printf '%q ' "$@"; printf '\n'; }
run() { record_command "$@" >> "$output/commands.txt"; "$@"; }
expect() {
    local expected=$1 label=$2 status=0
    shift 2
    record_command "$@" > "$output/$label.arguments.txt"
    "$@" > "$output/$label.log" 2>&1 || status=$?
    printf '%s\n' "$status" > "$output/$label.status.txt"
    printf '%s\t%s\t%s\n' "$label" "$expected" "$status" >> "$output/statuses.tsv"
    if [[ $status -ne $expected ]]; then
        tail -n 20 "$output/$label.log" >&2
        printf 'Unexpected status for %s: expected %s, got %s\n' "$label" "$expected" "$status" >&2
        exit 1
    fi
}

phase=snapshot
mapfile -d '' source_files < <(find EDSL -type f -name '*.lean' -print0 | sort -z)
source_files+=(EDSL.lean lean-toolchain lakefile.lean lake-manifest.json AtomicLogical64Main.lean
    scripts/verify-atomic-logical64.sh scripts/verify-atomic-logical64-native.sh
    scripts/check-audit.sh scripts/Audit.lean .github/workflows/atomic-logical64.yml
    fixtures/atomic-logical64.c fixtures/atomic-logical64-check.c fixtures/atomic-logical64-check.S
    tests/AtomicThreads64.lean tests/AtomicLogical64Artifact.lean)
run sha256sum "${source_files[@]}" > "$output/source-SHA256SUMS"
for file in "${source_files[@]}"; do install -D -m 0644 "$file" "$output/source/$file"; done
(cd "$output/source" && sha256sum --quiet --check "$output/source-SHA256SUMS")
run git rev-parse HEAD > "$output/repository-head.txt"
run date -u +%FT%TZ > "$output/start-utc.txt"
run uname -srmo > "$output/platform.txt"
run bash -n scripts/verify-atomic-logical64.sh
run shellcheck -s bash scripts/verify-atomic-logical64.sh > "$output/shellcheck.txt" 2>&1

phase=native
run env EDSL_ATOMIC64_NATIVE_OUTPUT="$output/native" bash scripts/verify-atomic-logical64-native.sh \
    > "$output/native-invocation.log" 2>&1
mapfile -t native_records < <(find "$output/native" -mindepth 1 -maxdepth 1 -type d -name 'run.*')
[[ ${#native_records[@]} -eq 1 ]]
native=${native_records[0]}
[[ $(< "$native/script-status.txt") == 0 ]]
(cd "$native" && sha256sum --quiet --check SHA256SUMS)
printf '%s\n' "$native" > "$output/native-record.txt"

phase=build_and_contracts
run flock /tmp/edsl-lean-build.lock lake build EDSL.OS.AtomicThreads64.Trace \
    EDSL.AtomicLogical64.Artifact edsl-certify-atomic-logical64 > "$output/build.log" 2>&1
expect 0 managed-tests flock /tmp/edsl-lean-build.lock lake env lean -DwarningAsError=true tests/AtomicThreads64.lean
expect 0 artifact-tests flock /tmp/edsl-lean-build.lock lake env lean -DwarningAsError=true tests/AtomicLogical64Artifact.lean

phase=literal_certificates
certifier=(lake env .lake/build/bin/edsl-certify-atomic-logical64)
for compiler in gcc clang; do
    expect 0 "$compiler-raw" "${certifier[@]}" "$native/$compiler/function.bin" "$output/$compiler-raw.lean"
    expect 0 "$compiler-elf" "${certifier[@]}" --elf "$native/$compiler/function.elf" "$output/$compiler-elf.lean"
done
for input in "$native"/raw-rejections/*.bin; do
    label=${input##*/}
    label=${label%.bin}
    expected=3
    [[ $label != empty ]] || expected=4
    expect "$expected" "reject-raw-$label" "${certifier[@]}" "$input" "$output/reject-raw-$label.lean"
done
for label in prefix suffix extra-text; do
    expect 3 "reject-elf-$label" "${certifier[@]}" --elf \
        "$native/elf-rejections/$label/function.elf" "$output/reject-elf-$label.lean"
done
# Static symbol/section records are not loader authority. The complete PT_LOAD
# code remains identical in these two owned metadata variants. Native extraction
# has stricter provenance gates; that is separate from this callable theorem.
for label in partial-span retained-relocation; do
    expect 0 "metadata-$label" "${certifier[@]}" --elf \
        "$native/elf-rejections/$label/function.elf" "$output/metadata-$label.lean"
done

phase=audit_and_kernel_replay
cat > "$output/Audit.lean" <<'LEAN'
import EDSL.AtomicLogical64.Artifact
import EDSL.OS.AtomicThreads64.Trace
import EDSL.Audit
#audit_edsl
#print axioms EDSL.AtomicLogical64.semantics
#print axioms EDSL.AtomicLogical64.Artifact.elf_sound
#print axioms EDSL.OS.AtomicThreads64.schedule_enabled_membership
LEAN
expect 0 audit flock /tmp/edsl-lean-build.lock lake env lean -DwarningAsError=true "$output/Audit.lean"
# Distinct replay namespaces permit one fresh checker to validate every literal
# certificate and both production graphs while sharing their imported terms.
printf 'import EDSL.OS.AtomicThreads64.Trace\n' > "$output/Replay.lean"
index=0
for certificate in gcc-raw gcc-elf clang-raw clang-elf metadata-partial-span metadata-retained-relocation; do
    replay="Certificate$index"
    run sed "s/EDSL.GeneratedAtomicLogical64/EDSL.GeneratedAtomicLogical64.Replay$index/g" \
        "$output/$certificate.lean" > "$output/$replay.lean"
    expect 0 "$certificate-stored" flock /tmp/edsl-lean-build.lock lake env lean -R "$output" \
        -DwarningAsError=true -o "$output/$replay.olean" "$output/$replay.lean"
    printf 'import %s\n' "$replay" >> "$output/Replay.lean"
    index=$((index + 1))
done
printf 'import EDSL.Audit\n#audit_edsl\n' >> "$output/Replay.lean"
proof_path="$output:$(lake env printenv LEAN_PATH)"
expect 0 replay-stored flock /tmp/edsl-lean-build.lock lake env env LEAN_PATH="$proof_path" \
    lean -R "$output" -DwarningAsError=true -o "$output/Replay.olean" "$output/Replay.lean"
# Independently recover every emitted literal and compare ALL bytes with its
# original input, including uninterpreted ELF metadata. This is an IO binding
# check, not a native computation used as a theorem premise.
cat > "$output/Roundtrip.lean" <<'LEAN'
import Replay
open EDSL X86
private def binary (bytes : List Byte) : ByteArray :=
  ByteArray.mk (bytes.map fun byte => UInt8.ofNat byte.toNat).toArray
private def roundtrip : IO Unit := do
  let some directory ← IO.getEnv "EDSL_ATOMIC64_ROUNDTRIP" | throw (IO.userError "missing output directory")
  let directory : System.FilePath := directory
  IO.FS.createDirAll directory
  IO.FS.writeBinFile (directory / "gcc-raw") (binary GeneratedAtomicLogical64.Replay0.observedBytes)
  IO.FS.writeBinFile (directory / "gcc-elf") (binary GeneratedAtomicLogical64.Replay1.observedELF)
  IO.FS.writeBinFile (directory / "clang-raw") (binary GeneratedAtomicLogical64.Replay2.observedBytes)
  IO.FS.writeBinFile (directory / "clang-elf") (binary GeneratedAtomicLogical64.Replay3.observedELF)
  IO.FS.writeBinFile (directory / "partial-span") (binary GeneratedAtomicLogical64.Replay4.observedELF)
  IO.FS.writeBinFile (directory / "retained-relocation") (binary GeneratedAtomicLogical64.Replay5.observedELF)
#eval roundtrip
LEAN
expect 0 literal-roundtrip flock /tmp/edsl-lean-build.lock lake env env LEAN_PATH="$proof_path" \
    EDSL_ATOMIC64_ROUNDTRIP="$output/roundtrip" lean -DwarningAsError=true "$output/Roundtrip.lean"
for compiler in gcc clang; do
    run cmp "$native/$compiler/function.bin" "$output/roundtrip/$compiler-raw"
    run cmp "$native/$compiler/function.elf" "$output/roundtrip/$compiler-elf"
done
for label in partial-span retained-relocation; do
    run cmp "$native/elf-rejections/$label/function.elf" "$output/roundtrip/$label"
done
expect 0 replay-fresh flock /tmp/edsl-lean-build.lock lake env env LEAN_PATH="$proof_path" \
    leanchecker --fresh Replay

phase=source_stability
run sha256sum --quiet --check "$output/source-SHA256SUMS" > "$output/source-stability.txt"
cat > "$output/scope.txt" <<'SCOPE'
Universal abstract callable OR/RET correctness for literal raw/full ELF bytes,
current actor/cell and code/caller-slot loans, all AF choices, one full64 event,
exact two retired instructions, independent bit-membership union and RAM frames.
Managed spawn/dispatch/join histories and finite legal schedules retain current
peer RAM and pin handles/loans through join; this is not native pthread refinement.
Native observations are finite, recorded separately, and never theorem premises.
The unlocked single-thread control passes deliberately: these observations do
not prove LOCK/CPU/C-SC/TSO/OS correctness. Physical WB/translation/alias/layout,
normal user control/CET/stack assumptions and native atomic lifetime stay external.
No general source frontend, arbitrary binary grader, runtime relocation or kernel
verification is supplied. ELF symbols/sections do not override PT_LOAD byte claims.
The changed-byte >=2 lower bound is only within the OR/RET retired-instruction model.
SCOPE
echo 'PASS: literal raw/full-ELF kernel certificates, managed contracts, audits/replay and separate finite native observations' \
    > "$output/result.txt"
phase=complete
complete=1
