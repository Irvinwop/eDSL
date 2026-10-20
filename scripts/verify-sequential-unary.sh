#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail
export LC_ALL=C
export PATH="$HOME/.elan/bin:$PATH"
export LEAN_NUM_THREADS=1
if [[ $(uname -sm) != 'Linux x86_64' || ( $# -ne 0 && $# -ne 2 ) ]]; then
    echo 'usage: verify-sequential-unary.sh [ACCEPTED_CAPTURE.tsv ACCEPTED_OPCODE_DIRECTORY] (Linux x86_64)' >&2
    exit 2
fi
cd "$(dirname "${BASH_SOURCE[0]}")/.."
root=$(pwd -P)
mkdir -p .cache/unary-registers/native
output=$(mktemp -d "$root/.cache/unary-registers/native/run.XXXXXXXX")
printf 'Unary finite conformance evidence: %s\n' "$output"
exec 3>&1 4>&2
exec > "$output/script.log" 2>&1
ulimit -c 0
mkdir -p "$output/receipts" "$output/source" "$output/lean-lib/tests/native" "$output/generated" "$output/opcodes"
phase=initialization
complete=0
run() {
    local label=$1 status=0
    shift
    local receipt="$output/receipts/$label"
    printf '%q ' "$@" > "$receipt.command"
    printf '\n' >> "$receipt.command"
    date -u +%FT%T.%NZ > "$receipt.started"
    "$@" > "$receipt.stdout" 2> "$receipt.stderr" || status=$?
    printf '%s\n' "$status" > "$receipt.exit"
    date -u +%FT%T.%NZ > "$receipt.finished"
    if [[ $status -ne 0 ]]; then
        cat "$receipt.stdout" "$receipt.stderr"
    fi
    return "$status"
}
lean_call() {
    # One shared lock per individual Lean call; never an outer lock on this script.
    run "$1" flock /tmp/edsl-lean-build.lock lean -j1 -DwarningAsError=true -DautoImplicit=false "${@:2}"
}
finish() {
    local status=$? manifest_status=0
    trap - EXIT
    set +e
    exec 1>&3 2>&4
    if [[ $status -ne 0 || $complete -ne 1 ]]; then
        [[ $status -ne 0 ]] || status=1
        printf 'INCOMPLETE: exit=%s phase=%s; no defect/support credit\n' "$status" "$phase" > "$output/result.txt"
    fi
    printf '%s\n' "$status" > "$output/script.exit"
    cat > "$output/RECEIPT.md" <<RECEIPT
Finite owned NEG32/BSWAP64 conformance, exit $status, phase $phase.
Commands, separate stdout/stderr, timestamps and actual exits: receipts/.
Owned and imported source snapshots: source/; input and provider pins: *.sha256.
Production model objects are copied into lean-lib/ after a scoped Lake build.
Generated finite observation theorems: generated/; compiled kernel objects:
lean-lib/. Individual calls use the repository pin, -j1, warnings as errors,
LEAN_NUM_THREADS=1 and /tmp/edsl-lean-build.lock. Standard kernel budgets.
Full production Sequential.decodeAt and Sequential.step run for both AF choices.
Independent fixed literal results/flags authenticate the complete native matrix.
Native GPR observations cover RAX/RCX/R8/R9; other GPRs and RAM/permission frames
are model challenges plus a universal production memory-frame theorem.
PUSHFQ masks RF/VM. No arbitrary hidden flags, physical CPU/OS refinement,
universal instruction refinement, source/backend/corpus/concurrency or defect
claim follows. Only owned synthetic wrappers execute. Root owns integrated,
fresh/corpus/CI gates and registration. Actual failures remain recorded.
RECEIPT
    if [[ $status -eq 0 ]]; then
        printf 'Complete scoped native compile/run, literal validation, generated kernel replay and audit.\n' > "$output/READY"
    fi
    (cd "$output" && find . -type f ! -name EVIDENCE.sha256 ! -name 'manifest-check.*' -print0 |
        sort -z | xargs -0 sha256sum) > "$output/EVIDENCE.sha256"
    (cd "$output" && sha256sum --quiet --check EVIDENCE.sha256) \
        > "$output/manifest-check.stdout" 2> "$output/manifest-check.stderr" || manifest_status=$?
    printf '%s\n' "$manifest_status" > "$output/manifest-check.exit"
    if [[ $manifest_status -ne 0 ]]; then status=1; rm -f "$output/READY"; fi
    if [[ $status -eq 0 ]]; then
        printf 'PASS: scoped unary native capture, independent literals, kernel production replay and audit: %s\n' "$output"
    else
        printf 'INCOMPLETE (exit %s, phase %s); retained receipts: %s\n' "$status" "$phase" "$output" >&2
    fi
    exit "$status"
}
trap finish EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
trap 'exit 129' HUP

phase=sources
owned=(tests/SequentialUnary.lean tests/native/UnaryReplay.lean Tools/Native/UnaryReplay.lean
    fixtures/native/unary-registers/capture.cpp fixtures/native/unary-registers/registers.S
    fixtures/native/unary-registers/expected-literals.tsv scripts/verify-sequential-unary.sh docs/sequential-unary.md)
run owned-pins sha256sum "${owned[@]}" lean-toolchain
cp "$output/receipts/owned-pins.stdout" "$output/OWNED-SOURCES.sha256"
for file in "${owned[@]}" lean-toolchain; do install -D -m 0644 "$file" "$output/source/$file"; done
run script-syntax bash -n "$output/source/scripts/verify-sequential-unary.sh"
run shellcheck shellcheck -s bash "$output/source/scripts/verify-sequential-unary.sh"
[[ $(< lean-toolchain) == leanprover/lean4:v4.35.0 ]] || { echo 'Unexpected Lean pin'; exit 2; }
run lean-version flock /tmp/edsl-lean-build.lock lean --version
run lean-prefix flock /tmp/edsl-lean-build.lock lean --print-prefix
lean_prefix=$(< "$output/receipts/lean-prefix.stdout")
run platform uname -srmo
run cpu lscpu
run libc getconf GNU_LIBC_VERSION
compiler=${CXX:-clang++}
run compiler-version "$compiler" --version
for tool in "$compiler" objdump objcopy readelf flock bash timeout sha256sum grep "$lean_prefix/bin/lean"; do
    path=$(command -v "$tool")
    printf '%s\t%s\n' "$tool" "$(realpath "$path")" >> "$output/tool-paths.tsv"
    sha256sum "$(realpath "$path")" >> "$output/TOOLS.sha256"
done
sha256sum "$lean_prefix/lib/lean/Init.olean" "$lean_prefix/lib/lean/Lean.olean" \
    "$lean_prefix/lib/lean/Std.olean" > "$output/INSTALLED-LIBRARIES.sha256"

phase=production_model
run model-build flock /tmp/edsl-lean-build.lock lake build EDSL.X86.Sequential.Machine EDSL.Audit
# Copy only the actual transitive production import closure. No broad or stale
# package overlay, and no mutable links to another worktree's objects.
provider="$root/.lake/build/lib/lean"
declare -A imported=()
queue=(EDSL.X86.Sequential.Machine EDSL.Audit)
for ((q=0; q<${#queue[@]}; q++)); do
    module=${queue[$q]}
    [[ -z ${imported[$module]:-} ]] || continue
    imported[$module]=1
    relative=${module//.//}
    source="$relative.lean"
    object="$provider/$relative.olean"
    [[ -f $source && -f $object ]] || { echo "Missing production import $module"; exit 2; }
    sha256sum "$source" >> "$output/IMPORTED-SOURCES.sha256"
    sha256sum "$object" >> "$output/PROVIDER-OBJECTS.sha256"
    install -D -m 0644 "$source" "$output/source/$source"
    install -D -m 0644 "$object" "$output/lean-lib/$relative.olean"
    while IFS= read -r dependency; do queue+=("$dependency"); done < <(
        awk '/^(public )?import / {for (i=2;i<=NF;i++) if ($i ~ /^EDSL[.]/) print $i}' "$source")
done
export LEAN_PATH="$output/lean-lib"
printf 'LEAN_PATH=%s\nLEAN_NUM_THREADS=%s\nprovider=%s\n' "$LEAN_PATH" "$LEAN_NUM_THREADS" "$provider" > "$output/lean-environment.txt"
phase=owned_lean
lean_call validator -R "$output/source" -o "$output/lean-lib/tests/native/UnaryReplay.olean" \
    "$output/source/tests/native/UnaryReplay.lean"
lean_call regressions -R "$output/source" -o "$output/lean-lib/tests/SequentialUnary.olean" \
    "$output/source/tests/SequentialUnary.lean"
lean_call inputs --run "$output/source/Tools/Native/UnaryReplay.lean" inputs \
    "$output/source/fixtures/native/unary-registers/expected-literals.tsv" "$output/inputs.tsv"

phase=native_compile
run compile-cpp "$compiler" -std=gnu++26 -O2 -Wall -Wextra -Wpedantic -Werror \
    -fno-lto -fcf-protection=none -mno-red-zone -c \
    "$output/source/fixtures/native/unary-registers/capture.cpp" -o "$output/capture.o"
run compile-asm "$compiler" -c "$output/source/fixtures/native/unary-registers/registers.S" -o "$output/registers.o"
run link "$compiler" -fno-lto '-Wl,--build-id=none,-z,noexecstack' \
    "$output/capture.o" "$output/registers.o" -o "$output/capture.elf"
run final-disassembly objdump -d "$output/capture.elf"
run elf readelf -h -l -S -s -r -n -W "$output/capture.elf"
run final-text objcopy --dump-section ".text=$output/capture.text.bin" "$output/capture.elf"
phase=native_capture
run native timeout --kill-after=2 20 "$output/capture.elf" "$output/inputs.tsv" "$output/opcodes"
capture="$output/receipts/native.stdout"
phase=lean_generation
lean_call generate-fresh --run "$output/source/Tools/Native/UnaryReplay.lean" generate \
    "$output/source/fixtures/native/unary-registers/expected-literals.tsv" "$capture" "$output/opcodes" "$output/generated" Fresh
if [[ $# -eq 2 ]]; then
    run accepted-input-pins sha256sum "$1" "$2"/*.bin
    cp "$output/receipts/accepted-input-pins.stdout" "$output/ACCEPTED-INPUTS.sha256"
    install -m 0644 "$1" "$output/accepted.tsv"
    mkdir "$output/accepted-opcodes"
    cp "$2"/*.bin "$output/accepted-opcodes/"
    lean_call generate-accepted --run "$output/source/Tools/Native/UnaryReplay.lean" generate \
        "$output/source/fixtures/native/unary-registers/expected-literals.tsv" "$output/accepted.tsv" \
        "$output/accepted-opcodes" "$output/generated" Accepted
fi

phase=malformed_controls
awk -F '\t' 'BEGIN {OFS=FS} NR==2 {$11="0000000100000000"} {print}' "$capture" > "$output/corrupt-output.tsv"
awk 'NR!=1409' "$capture" > "$output/missing-row.tsv"
cat "$capture" > "$output/duplicate-row.tsv"
sed -n '2p' "$capture" >> "$output/duplicate-row.tsv"
for control in corrupt-output missing-row duplicate-row; do
    status=0
    lean_call "reject-$control" --run "$output/source/Tools/Native/UnaryReplay.lean" generate \
        "$output/source/fixtures/native/unary-registers/expected-literals.tsv" "$output/$control.tsv" \
        "$output/opcodes" "$output/rejected-$control" Rejected || status=$?
    [[ $status -eq 1 && ! -d $output/rejected-$control ]] || { echo "Failed malformed control: $control"; exit 1; }
done
run reject-corrupt-output-reason grep -F -- \
    'independent input/result/flags/prestate/frame check failed' "$output/receipts/reject-corrupt-output.stderr"
run reject-missing-row-reason grep -F -- 'incomplete matrix' "$output/receipts/reject-missing-row.stderr"
run reject-duplicate-row-reason grep -F -- 'duplicate case/register/seed' "$output/receipts/reject-duplicate-row.stderr"

phase=kernel_replay
printf 'import tests.SequentialUnary\n' > "$output/generated/UnaryAudit.lean"
for list in "$output/generated/"*.modules; do
    while IFS= read -r module; do
        [[ -n $module ]] || continue
        lean_call "kernel-$module" -R "$output/generated" -o "$output/lean-lib/$module.olean" "$output/generated/$module.lean"
        printf 'import %s\n' "$module" >> "$output/generated/UnaryAudit.lean"
    done < "$list"
done
printf '\n#audit_edsl\n' >> "$output/generated/UnaryAudit.lean"
phase=audit
lean_call audit -R "$output/generated" -o "$output/lean-lib/UnaryAudit.olean" "$output/generated/UnaryAudit.lean"
phase=closing_bindings
run owned-stable sha256sum --check "$output/OWNED-SOURCES.sha256"
run imported-stable sha256sum --check "$output/IMPORTED-SOURCES.sha256"
run provider-stable sha256sum --check "$output/PROVIDER-OBJECTS.sha256"
if [[ $# -eq 2 ]]; then run accepted-stable sha256sum --check "$output/ACCEPTED-INPUTS.sha256"; fi
printf 'PASS: 1408 fresh CPU observations; both AF choices; all decoder/frame regressions; independent literal matrix; 9 semantic corruption and 3 malformed controls; generated kernel replay; transitive audit.\n' > "$output/result.txt"
if [[ $# -eq 2 ]]; then printf 'PASS: all 1408 accepted private observations additionally kernel replayed.\n' >> "$output/result.txt"; fi
complete=1
phase=complete
