#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail
export LC_ALL=C LEAN_NUM_THREADS=1
if [[ $# -ne 0 ]]; then echo 'usage: verify-atomic-set64.sh' >&2; exit 2; fi
cd "$(dirname "${BASH_SOURCE[0]}")/.."
archive=${EDSL_SET64_OUTPUT:-artifacts/atomic-set64}
mkdir -p "$archive"
archive=$(cd "$archive" && pwd -P)
output=$(mktemp -d "$archive/run.XXXXXXXX")
printf 'AtomicSet64 verification: %s\n' "$output"
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
    printf 'AtomicSet64 exit=%s phase=%s: %s\n' "$status" "$phase" "$output"
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
source_files+=(EDSL.lean lean-toolchain lakefile.lean lake-manifest.json Tools/Certify/AtomicSet64.lean
    scripts/verify-atomic-set64.sh scripts/verify-atomic-set64-native.sh
    .github/workflows/atomic-set64.yml fixtures/atomic-set64.c fixtures/atomic-set64.cpp
    fixtures/atomic-set64-check.c fixtures/atomic-set64-check.S tests/LockedSet64.lean
    tests/Atomics64Logical.lean tests/AtomicSet64.lean tests/AtomicSet64Artifact.lean)
run sha256sum "${source_files[@]}" > "$output/source-SHA256SUMS"
for file in "${source_files[@]}"; do install -D -m 0644 "$file" "$output/source/$file"; done
(cd "$output/source" && sha256sum --quiet --check "$output/source-SHA256SUMS")
run git rev-parse HEAD > "$output/repository-head.txt"
run date -u +%FT%TZ > "$output/start-utc.txt"
run uname -srmo > "$output/platform.txt"
run bash -n scripts/verify-atomic-set64.sh
run shellcheck -s bash scripts/verify-atomic-set64.sh > "$output/shellcheck.txt" 2>&1

phase=native
run env EDSL_SET64_NATIVE_OUTPUT="$output/native" bash scripts/verify-atomic-set64-native.sh \
    > "$output/native-invocation.log" 2>&1
mapfile -t native_records < <(find "$output/native" -mindepth 1 -maxdepth 1 -type d -name 'run.*')
[[ ${#native_records[@]} -eq 1 ]]
native=${native_records[0]}
[[ $(< "$native/script-status.txt") == 0 ]]
(cd "$native" && sha256sum --quiet --check SHA256SUMS)
printf '%s\n' "$native" > "$output/native-record.txt"

phase=build_and_contracts
run flock /tmp/edsl-lean-build.lock lake build EDSL.AtomicSet64 \
    EDSL.AtomicSet64Domain EDSL.OS.Atomics64.LogicalTrace EDSL.X86.LockedSet64 \
    EDSL.AtomicLogical64.Artifact EDSL.X86.StackRead64 EDSL.Audit \
    edsl-certify-atomic-set64 > "$output/build.log" 2>&1
for test in LockedSet64 Atomics64Logical AtomicSet64 AtomicSet64Artifact; do
    expect 0 "$test-tests" flock /tmp/edsl-lean-build.lock lake env lean -DwarningAsError=true "tests/$test.lean"
done

phase=literal_certificates
certifier=(lake env .lake/build/bin/edsl-certify-atomic-set64)
operations=(and or xor)
certificates=()
inputs=()
for compiler in gcc_c clang_c clang_cpp; do
    for operation in "${operations[@]}"; do
        label="$compiler-$operation"
        directory="$native/$compiler/$operation"
        expect 0 "$label-raw" "${certifier[@]}" "$operation" "$directory/function.bin" "$output/$label-raw.lean"
        expect 0 "$label-elf" "${certifier[@]}" "$operation" --elf "$directory/function.elf" "$output/$label-elf.lean"
        certificates+=("$label-raw" "$label-elf")
        inputs+=("$directory/function.bin" "$directory/function.elf")
        for wrong in "${operations[@]}"; do
            [[ $wrong != "$operation" ]] || continue
            expect 3 "$label-wrong-$wrong-raw" "${certifier[@]}" "$wrong" \
                "$directory/function.bin" "$output/rejected.lean"
            expect 3 "$label-wrong-$wrong-elf" "${certifier[@]}" "$wrong" --elf \
                "$directory/function.elf" "$output/rejected.lean"
        done
    done
done
for operation in "${operations[@]}"; do
    for input in "$native/raw-rejections/$operation"/*.bin; do
        label=${input##*/}
        label=${label%.bin}
        expected=3
        [[ $label != empty ]] || expected=4
        expect "$expected" "reject-$operation-raw-$label" "${certifier[@]}" "$operation" "$input" "$output/rejected.lean"
    done
    for label in prefix suffix extra-text wrong-entry wrong-operation wrong-machine; do
        expect 3 "reject-$operation-elf-$label" "${certifier[@]}" "$operation" --elf \
            "$native/elf-rejections/$operation/$label/function.elf" "$output/rejected.lean"
    done
    for label in empty truncated-header raw-as-elf; do
        expect 4 "malformed-$operation-elf-$label" "${certifier[@]}" "$operation" --elf \
            "$native/elf-rejections/$operation/$label/function.elf" "$output/rejected.lean"
    done
    # Section/symbol metadata cannot override complete PT_LOAD code authority.
    for label in partial-span retained-relocation stripped-symbols; do
        certificate="metadata-$operation-$label"
        input="$native/elf-rejections/$operation/$label/function.elf"
        expect 0 "$certificate" "${certifier[@]}" "$operation" --elf "$input" "$output/$certificate.lean"
        certificates+=("$certificate")
        inputs+=("$input")
    done
done
expect 2 bad-operation "${certifier[@]}" add "$native/gcc_c/and/function.bin" "$output/rejected.lean"
run head -c 65537 /dev/zero > "$output/over-limit.elf"
expect 3 over-limit-elf "${certifier[@]}" and --elf "$output/over-limit.elf" "$output/rejected.lean"
expect 5 missing-input "${certifier[@]}" and "$output/absent.bin" "$output/rejected.lean"
[[ ! -e "$output/rejected.lean" ]]

phase=renderer_rejections
# Exercise the public renderer after bypassing CLI admission. Actual generated
# Lean must reject a suffix and a crossed task; text copies of the renderer do
# not check that the emitted claims really fail kernel checking.
cat > "$output/RenderInvalid.lean" <<'LEAN'
import EDSL.AtomicSet64.Artifact
private def renderInvalid : IO Unit := do
  let some directory ← IO.getEnv "EDSL_SET64_INVALID" | throw (IO.userError "missing output path")
  IO.FS.writeFile (System.FilePath.mk directory / "render-suffix.lean")
    (EDSL.AtomicSet64.Artifact.rawSource .symmetricDifference [0xf0,0x48,0x31,0x37,0xc3,0x90])
  IO.FS.writeFile (System.FilePath.mk directory / "render-crossed.lean")
    (EDSL.AtomicSet64.Artifact.rawSource .intersection [0xf0,0x48,0x31,0x37,0xc3])
#eval renderInvalid
LEAN
expect 0 render-invalid flock /tmp/edsl-lean-build.lock lake env env EDSL_SET64_INVALID="$output" \
    lean -DwarningAsError=true "$output/RenderInvalid.lean"
for label in suffix crossed; do
    expect 1 "render-$label-rejected" flock /tmp/edsl-lean-build.lock lake env lean \
        -DwarningAsError=true "$output/render-$label.lean"
    run grep -Fq 'AtomicSet64.Artifact.checkRaw operation observedBytes = true' "$output/render-$label-rejected.log"
    run grep -Fq 'is false' "$output/render-$label-rejected.log"
done

phase=audit_and_kernel_replay
printf 'import EDSL.OS.Atomics64.LogicalTrace\nimport EDSL.AtomicSet64Domain\n' > "$output/Replay.lean"
printf 'import Replay\nopen EDSL X86\nprivate def binary (bytes : List Byte) : ByteArray :=\n  ByteArray.mk (bytes.map fun byte => UInt8.ofNat byte.toNat).toArray\nprivate def roundtrip : IO Unit := do\n  let some path ← IO.getEnv "EDSL_SET64_ROUNDTRIP" | throw (IO.userError "missing output path")\n  let directory : System.FilePath := path\n  IO.FS.createDirAll directory\n' > "$output/Roundtrip.lean"
for index in "${!certificates[@]}"; do
    certificate=${certificates[$index]}
    replay="Certificate$index"
    run sed "s/EDSL.GeneratedAtomicSet64/EDSL.GeneratedAtomicSet64.Replay$index/g" \
        "$output/$certificate.lean" > "$output/$replay.lean"
    expect 0 "$certificate-stored" flock /tmp/edsl-lean-build.lock lake env lean -R "$output" \
        -DwarningAsError=true -o "$output/$replay.olean" "$output/$replay.lean"
    printf 'import %s\n' "$replay" >> "$output/Replay.lean"
    declaration=observedELF
    [[ $certificate != *-raw ]] || declaration=observedBytes
    printf '  IO.FS.writeBinFile (directory / "%s") (binary GeneratedAtomicSet64.Replay%s.%s)\n' \
        "$index" "$index" "$declaration" >> "$output/Roundtrip.lean"
done
printf 'import EDSL.Audit\n#audit_edsl\n' >> "$output/Replay.lean"
printf '#eval roundtrip\n' >> "$output/Roundtrip.lean"
proof_path="$output:$(flock /tmp/edsl-lean-build.lock lake env printenv LEAN_PATH)"
expect 0 replay-stored flock /tmp/edsl-lean-build.lock lake env env LEAN_PATH="$proof_path" \
    lean -R "$output" -DwarningAsError=true -o "$output/Replay.olean" "$output/Replay.lean"
expect 0 literal-roundtrip flock /tmp/edsl-lean-build.lock lake env env LEAN_PATH="$proof_path" \
    EDSL_SET64_ROUNDTRIP="$output/roundtrip" lean -DwarningAsError=true "$output/Roundtrip.lean"
for index in "${!inputs[@]}"; do run cmp "${inputs[$index]}" "$output/roundtrip/$index"; done
expect 0 replay-fresh flock /tmp/edsl-lean-build.lock lake env env LEAN_PATH="$proof_path" \
    leanchecker --fresh Replay

phase=source_stability
run sha256sum --quiet --check "$output/source-SHA256SUMS" > "$output/source-stability.txt"
cat > "$output/scope.txt" <<'SCOPE'
Literal whole raw/full-ELF contracts for all three exact locked logical/RET
routines, all AF streams, actual current actor/cell/code/caller-slot authority,
independent natural-bit result, complete RAM/ABI/loan frames and exact two
retired instructions. Every emitted literal roundtrips to the complete input;
stored proofs replay with a fresh kernel environment. Finite native evidence
is separate and never a theorem premise. Unlocked single-thread controls pass
deliberately; no physical LOCK, language memory-order, compiler-source, TSO,
kernel/Arch or timing refinement is established. The new mixed-operation trace
is a finite persistent-cell modification order, not an instruction-level
spawn/join scheduler. The old OR-only scheduler and grader retain their scope.
The changed-byte >=2 bound is restricted to the new logical/RET ISA model.
SCOPE
echo 'PASS: literal certificates, independent contracts, audited fresh replay, separate finite native observations' \
    > "$output/result.txt"
complete=1
phase=complete
