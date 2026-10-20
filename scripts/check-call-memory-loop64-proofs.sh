#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail
umask 022
export LC_ALL=C TZ=UTC LEAN_NUM_THREADS=1
if [[ $# != 3 ]]; then
    echo 'usage: scripts/check-call-memory-loop64-proofs.sh OUTPUT GCC_TEXT CLANG_TEXT' >&2
    exit 2
fi
cd "$(dirname "${BASH_SOURCE[0]}")/.."
output=$1
artifacts=("$(realpath -- "$2")" "$(realpath -- "$3")")
lengths=(45 52)
# A fresh directory prevents stale .olean or success receipts from being reused.
mkdir -- "$output"
output=$(realpath -- "$output")
exec 3>"$output/commands.log" 4>"$output/command-status.tsv"
sequence=0
input_count=0
phases=(lock inputs build elaboration audit fresh_kernel input_stability)
declare -A phase_status
for phase in "${phases[@]}"; do phase_status[$phase]=NOTRUN; done
run() {
    sequence=$((sequence + 1))
    local status=0 line arguments tag="$BASHPID.$sequence"
    printf -v arguments '%q ' "$@"
    printf -v line '[%s] cwd=%q argv=%s\n' "$tag" "$PWD" "$arguments"
    printf '%s' "$line" >&3
    "$@" || status=$?
    printf '%s\t%d\n' "$tag" "$status" >&4
    return "$status"
}
phase_begin() {
    phase_status[$1]=RUNNING
    printf 'formal_phase=%s status=RUNNING UTC=%s\n' "$1" "$(date -u +%FT%TZ)" >&2
}
phase_pass() { phase_status[$1]=PASS; }
manifest() {
    (
        cd "$output" || exit 1
        # shellcheck disable=SC2094
        find . -type f ! -path ./SHA256SUMS ! -path ./MANIFEST-SHA256.txt -print0 |
            sort -z | xargs -0 -r sha256sum -- > SHA256SUMS || exit 1
        sha256sum SHA256SUMS > MANIFEST-SHA256.txt
    )
}
write_terminal() {
    local status=$1 phase
    if [[ $status == 0 ]]; then
        printf 'formal=PASS whole_texts=%d universal_closed_claims=true mixed_cpu_os_execution=true union_ram_frame=true fresh_kernel=true\n' \
            "$input_count" > "$output/result.txt"
    else
        printf 'formal=FAIL whole_texts=%d fresh_kernel=%s\n' "$input_count" \
            "${phase_status[fresh_kernel]}" > "$output/result.txt"
    fi
    printf 'phase\tstatus\n' > "$output/phase-status.tsv"
    for phase in "${phases[@]}"; do
        printf '%s\t%s\n' "$phase" "${phase_status[$phase]}" >> "$output/phase-status.tsv"
    done
    printf 'exit=%d UTC=%s\n' "$status" "$(date -u +%FT%TZ)" > "$output/terminal-status.txt"
}
finish() {
    local status=$? phase
    trap - EXIT HUP INT TERM
    set +e
    for phase in "${phases[@]}"; do
        if [[ ${phase_status[$phase]} == RUNNING ]]; then phase_status[$phase]=FAIL; fi
        if [[ ${phase_status[$phase]} != PASS && $status == 0 ]]; then status=1; fi
    done
    write_terminal "$status" || status=1
    exec 3>&- 4>&-
    if ! manifest; then
        status=1
        write_terminal "$status"
        manifest
    fi
    exit "$status"
}
trap finish EXIT
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM

# This helper is called UNLOCKED by the runner/CI. It owns the only Lean lock.
phase_begin lock
exec 8>/tmp/edsl-lean-build.lock
run flock 8
phase_pass lock

phase_begin inputs
run sha256sum -- "${artifacts[@]}" > "$output/extraction-SHA256SUMS"
for index in 0 1; do
    [[ $(run stat -c %s "${artifacts[index]}") == "${lengths[index]}" ]]
    run cp -- "${artifacts[index]}" "$output/input-$index.bin"
    input_count=$((input_count + 1))
done
run cat lean-toolchain > "$output/lean-toolchain"
run lake --version > "$output/lake-version.txt" 2>&1
run lake env lean --version > "$output/lean-version.txt" 2>&1
pinned=$(< lean-toolchain)
[[ $pinned =~ ^leanprover/lean4:v([0-9]+\.[0-9]+\.[0-9]+)$ ]]
version=${BASH_REMATCH[1]}
run grep -F "version $version," "$output/lean-version.txt" > "$output/lean-version-check.txt"
run lake env which lean leanchecker > "$output/lean-tools.txt"
mapfile -t lean_tools < "$output/lean-tools.txt"
[[ ${#lean_tools[@]} == 2 ]]
run sha256sum -- "${lean_tools[@]}" > "$output/lean-tool-SHA256SUMS"
phase_pass inputs

phase_begin build
run lake build tests.fixtures.CallMemoryLoop64.Audit \
    tests.fixtures.CallMemoryLoop64.ClosedForm.Audit tests.fixtures.CallMemoryLoop64ClosedFormExports \
    > "$output/build.log" 2>&1
phase_pass build

phase_begin elaboration
source_file="$output/CallMemoryLoop64Observed.lean"
cat > "$source_file" <<'LEAN'
import tests.fixtures.CallMemoryLoop64.GCC
import tests.fixtures.CallMemoryLoop64.Clang
import tests.fixtures.CallMemoryLoop64.Audit
import tests.fixtures.CallMemoryLoop64.ClosedForm.Audit
import tests.fixtures.CallMemoryLoop64ClosedFormExports
import EDSL.Audit
set_option warningAsError true
namespace EDSL.CallMemoryLoop64.Observed
open X86 OS
LEAN
names=(GccSeparate ClangSeparate)
profiles=(gccSeparate clangSeparate)
clients=(GCC Clang)
for index in 0 1; do
    run od -An -v -tu1 -- "$output/input-$index.bin" > "$output/input-$index.decimal.txt"
    {
    printf 'def bytes%s : List Byte := [' "${names[index]}"
    # Only decimal byte literals from the actual newly compiled raw extraction
    # enter generated source. Native observation files never enter the proof.
    run awk -v expected="${lengths[index]}" '
      { for (i=1;i<=NF;i++) { if (seen++) printf ","; printf "%s",$i } }
      END { if (seen != expected) exit 1; printf "]\n" }' "$output/input-$index.decimal.txt"
    cat <<LEAN
theorem binding${names[index]} :
    Compiler.program .${profiles[index]} = (⟨bytes${names[index]}, 0⟩ : Program) := by rfl
/-- The independent closed claim, including useful present admission, for the
actual complete raw extraction and its checked ELF caller entry offset. -/
theorem closedClaim${names[index]} : Claim ⟨bytes${names[index]}, 0⟩ := by
  rw [← binding${names[index]}]
  exact ${clients[index]}.claim
/-- Actual returning execution, full fetch/read coverage, current owner
resources, checked mixed history, union RAM frame and the independent Post.
Counts are outputs of execution, never a premise of resource admission. -/
theorem execution${names[index]} {resource : Resources} {initial : State}
    (pre : ResourcePre ⟨bytes${names[index]}, 0⟩ resource initial)
    (choices : CallReturn.Choices) :
    ∃ evolved result,
      CallReturn.run choices result.instructions initial = .ok result ∧
      Returned resource initial choices evolved result :=
  closedClaim${names[index]}.run pre choices
/-- Checked allocation admits every full64 value/count and old target word,
including count zero, with arbitrary other registers, flags and AF choices. -/
theorem reachableExecution${names[index]} (input count old : Word)
    (registers : Register → Word) (flags : Word) (choices : CallReturn.Choices) :
    ∃ evolved result,
      CallReturn.run choices result.instructions
        (Domain.initial ⟨bytes${names[index]}, 0⟩ input count old registers flags) = .ok result ∧
      Returned (Domain.resource ⟨bytes${names[index]}, 0⟩ input count old)
        (Domain.initial ⟨bytes${names[index]}, 0⟩ input count old registers flags)
        choices evolved result :=
  execution${names[index]} (Domain.resource_pre _ (by decide) (by decide)
    input count old registers flags) choices
#print axioms EDSL.CallMemoryLoop64.Observed.closedClaim${names[index]}
#print axioms EDSL.CallMemoryLoop64.Observed.execution${names[index]}
#print axioms EDSL.CallMemoryLoop64.Observed.reachableExecution${names[index]}
LEAN
    } >> "$source_file"
done
printf 'end EDSL.CallMemoryLoop64.Observed\n#audit_edsl\n' >> "$source_file"
run lake env lean -R "$output" -DwarningAsError=true -o "$output/CallMemoryLoop64Observed.olean" \
    "$source_file" > "$output/observed-proof.log" 2>&1
phase_pass elaboration

phase_begin audit
run grep -E '^Audited [0-9]+ EDSL declarations; no unapproved axioms' "$output/observed-proof.log" \
    > "$output/audit-receipt.txt"
phase_pass audit

phase_begin fresh_kernel
run lake env printenv LEAN_PATH > "$output/import-path.txt"
proof_path="$output:$(< "$output/import-path.txt")"
run lake env env LEAN_PATH="$proof_path" leanchecker --fresh --verbose CallMemoryLoop64Observed \
    > "$output/fresh-kernel.log" 2>&1
phase_pass fresh_kernel

phase_begin input_stability
run sha256sum -c "$output/extraction-SHA256SUMS" > "$output/extraction-stability.txt"
for index in 0 1; do run cmp "${artifacts[index]}" "$output/input-$index.bin"; done
phase_pass input_stability
