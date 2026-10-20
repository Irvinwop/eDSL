#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
# Scoped shared-core acceptance. Native replay has a different owner/runner.
set -euo pipefail
export LC_ALL=C
export PATH="${ELAN_HOME:-$HOME/.elan}/bin:$PATH"
export LEAN_NUM_THREADS=1
cd "$(dirname "${BASH_SOURCE[0]}")/.."
root=$(pwd -P)
[[ $# -eq 0 ]] || { echo 'usage: verify-sequential-shift-one.sh' >&2; exit 2; }
[[ $(cat lean-toolchain) == leanprover/lean4:v4.35.0 ]] || exit 2
mkdir -p .cache/shift-average/isa
output=$(mktemp -d "$root/.cache/shift-average/isa/acceptance.XXXXXXXX")
printf 'Shared SHR1 core evidence: %s\n' "$output"
mkdir -p "$output/receipts" "$output/source" "$output/fresh/lib"
phase=initialization
complete=0

run() {
    local label=$1 status=0
    shift
    local receipt="$output/receipts/$label"
    printf 'cwd=%q\nPATH=%q\nLEAN_NUM_THREADS=%q\nLEAN_PATH=%q\n' \
        "$PWD" "$PATH" "$LEAN_NUM_THREADS" "${LEAN_PATH-}" > "$receipt.environment"
    printf '%q ' "$@" > "$receipt.command"
    printf '\n' >> "$receipt.command"
    date -u +%FT%T.%NZ > "$receipt.started"
    "$@" > "$receipt.stdout" 2> "$receipt.stderr" || status=$?
    printf '%s\n' "$status" > "$receipt.exit"
    date -u +%FT%T.%NZ > "$receipt.finished"
    if [[ $status -ne 0 ]]; then cat "$receipt.stdout" "$receipt.stderr" >&2; fi
    return "$status"
}

finish() {
    local status=$?
    trap - EXIT
    if [[ $complete -ne 1 && $status -eq 0 ]]; then status=1; fi
    printf '%s\n' "$status" > "$output/script.exit"
    printf 'phase=%s\nexit=%s\n' "$phase" "$status" > "$output/result.txt"
    if [[ $status -ne 0 ]]; then
        printf 'INCOMPLETE: %s (phase %s, exit %s); evidence retained\n' "$output" "$phase" "$status" >&2
    else
        printf 'PASS: %s\n' "$output"
    fi
    exit "$status"
}
trap finish EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

owned=(EDSL/X86/Sequential/Model.lean EDSL/X86/Sequential/Flags.lean
    EDSL/X86/Sequential/Decode.lean EDSL/X86/Sequential/Machine.lean
    EDSL/X86/Sequential/CFG.lean EDSL/X86/Sequential/CFGTransport.lean
    EDSL/X86/Sequential/Return.lean EDSL/X86/Sequential/Literals.lean
    EDSL/X86/Sequential/ShiftOne.lean EDSL/X86/CallReturn/DecodeTransport.lean
    EDSL/Sum32/Shape.lean EDSL/Sum32/Artifact.lean
    tests/SequentialShiftOne.lean tests/ShiftOneAudit.lean
    scripts/verify-sequential-shift-one.sh docs/shift-one.md)
libraries=(EDSL.X86.Sequential.ShiftOne EDSL.X86.Sequential.CFGDiscovery
    EDSL.X86.Sequential.Return EDSL.X86.Sequential.Literals
    EDSL.X86.CallReturn EDSL.X86.CallReturn.DecodeTransport EDSL.Sum32.Artifact
    EDSL.X86.VCGen.Tactics EDSL.X86.VCGen.Unary)
tests=(tests.SequentialShiftOne tests.ShiftOneAudit tests.SequentialISA
    tests.SequentialExecution tests.CFG tests.CallReturnRaw
    tests.SequentialCounter32 tests.SequentialDisplacement tests.Sum32Artifact)

phase=tools
run lean-version flock /tmp/edsl-lean-build.lock lean -j1 --version
run lake-version flock /tmp/edsl-lean-build.lock lake --version
run script-syntax bash -n scripts/verify-sequential-shift-one.sh
run script-shellcheck shellcheck -s bash scripts/verify-sequential-shift-one.sh
run base-revision git rev-parse HEAD
run lean-prefix flock /tmp/edsl-lean-build.lock lean --print-prefix
sysroot=$(< "$output/receipts/lean-prefix.stdout")
tool_files=("$sysroot/bin/lean" "$sysroot/bin/lake" "$sysroot/bin/leanir")
for candidate in "$sysroot"/lib/lean/*shared*.so; do tool_files+=("$candidate"); done
for tool in bash flock sha256sum rg awk sort install cmp shellcheck; do
    tool_files+=("$(realpath "$(command -v "$tool")")")
done
run tools-before sha256sum "${tool_files[@]}"
cp "$output/receipts/tools-before.stdout" "$output/TOOLS.sha256"

# Read only the exact import closure. Other workers' source directories are
# never scanned or hashed. System imports are pinned by the same traversal.
declare -A visited=()
project_sources=()
system_sources=()
system_objects=()
imports() {
    # Read the actual header, excluding nested comments and examples in docs.
    # Lean imports precede declarations; later strings cannot add dependencies.
    awk '
    {
        line = ""
        for (i = 1; i <= length($0); i++) {
            pair = substr($0, i, 2)
            if (depth > 0) {
                if (pair == "/-") { depth++; i++ }
                else if (pair == "-/") { depth--; i++ }
            } else if (pair == "/-") { depth++; i++ }
            else if (pair == "--") { break }
            else { line = line substr($0, i, 1) }
        }
        sub(/^[ \t]+/, "", line)
        sub(/[ \t\r]+$/, "", line)
        if (line == "" || line == "module" || line == "prelude") next
        if (line ~ /^(public |private |meta )*import /) { print line; next }
        exit
    }' "$1"
}
collect() {
    local module=$1 source import_line token object
    [[ ${visited[$module]+yes} ]] && return 0
    visited[$module]=1
    case "$module" in
        EDSL|EDSL.All) printf 'Full-library import is outside this scoped gate\n' >&2; return 2 ;;
        EDSL.*|tests.*) source="${module//.//}.lean" ;;
        Init|Init.*|Lean|Lean.*|Std|Std.*|Lake|Lake.*) source="$sysroot/src/lean/${module//.//}.lean" ;;
        *) printf 'Unresolved import: %s\n' "$module" >&2; return 2 ;;
    esac
    [[ -f $source ]] || { printf 'Missing source: %s\n' "$source" >&2; return 2; }
    while IFS= read -r import_line; do
        for token in $import_line; do
            case "$token" in
                public|private|meta|import|all) continue ;;
                --*) break ;;
                *) collect "$token" ;;
            esac
        done
    done < <(imports "$source")
    case "$source" in
        "$sysroot"/*)
            system_sources+=("$source")
            object="$sysroot/lib/lean/${module//.//}.olean"
            [[ -f $object ]] || return 2
            system_objects+=("$object")
            for candidate in "$object.private" "$object.server"; do
                if [[ -f $candidate ]]; then system_objects+=("$candidate"); fi
            done ;;
        *) project_sources+=("$source") ;;
    esac
}

phase=source_freeze
collect Init
for module in "${libraries[@]}" "${tests[@]}"; do collect "$module"; done
printf '%s\n' "${project_sources[@]}" > "$output/PROJECT-CLOSURE.order"
printf '%s\n' "${system_sources[@]}" > "$output/SYSTEM-CLOSURE.sources"
run owned-before sha256sum "${owned[@]}"
cp "$output/receipts/owned-before.stdout" "$output/OWNED-SOURCES.sha256"
run source-before sha256sum "${project_sources[@]}" lean-toolchain lakefile.lean lake-manifest.json
cp "$output/receipts/source-before.stdout" "$output/DEPENDENCY-SOURCES.sha256"
run system-before sha256sum "${system_sources[@]}" "${system_objects[@]}"
cp "$output/receipts/system-before.stdout" "$output/LEAN-DEPENDENCIES.sha256"
for source in "${project_sources[@]}" "${owned[@]}" lean-toolchain lakefile.lean lake-manifest.json; do
    install -D -m 0644 "$source" "$output/source/$source"
done

phase=scoped_lake_build
library_modules=()
library_objects=()
for source in "${project_sources[@]}"; do
    if [[ $source == EDSL/* ]]; then
        module=${source%.lean}
        library_modules+=("${module//\//.}")
        library_objects+=(".lake/build/lib/lean/${source%.lean}.olean")
    fi
done
run lake-build flock /tmp/edsl-lean-build.lock lake build "${library_modules[@]}"
# Pin the exact current library objects before any source test imports them.
run current-objects sha256sum "${library_objects[@]}"
cp "$output/receipts/current-objects.stdout" "$output/CURRENT-OBJECTS.sha256"

phase=scoped_tests_and_audit
for module in "${tests[@]}"; do
    run "current-$module" flock /tmp/edsl-lean-build.lock lake env lean -j1 \
        -DwarningAsError=true "${module//.//}.lean"
done

phase=audit_negative_control
awk '/^#audit_edsl/ {
    print "axiom ShiftOneAuditUntrusted : False"
    print "theorem EDSL.shiftOneAuditRejection : False := ShiftOneAuditUntrusted"
} { print }' tests/ShiftOneAudit.lean > "$output/AuditNegative.lean"
if run audit-negative flock /tmp/edsl-lean-build.lock lake env lean -j1 \
    -DwarningAsError=true "$output/AuditNegative.lean"; then
    echo 'Audit incorrectly admitted an unapproved transitive axiom' >&2
    exit 1
fi
[[ $(cat "$output/receipts/audit-negative.exit") == 1 ]] || exit 1
rg -q 'depends on unapproved axiom ShiftOneAuditUntrusted' "$output/receipts/audit-negative.stdout"

phase=actual_fresh_build
# No cached project objects enter this search path. Compile each source once,
# in import order, with its own lock and the unmodified default proof budgets.
for source in "${project_sources[@]}"; do
    object="$output/fresh/lib/${source%.lean}.olean"
    mkdir -p "$(dirname "$object")"
    run "fresh-${source//\//.}" env LEAN_PATH="$output/fresh/lib" \
        flock /tmp/edsl-lean-build.lock lean -j1 -DwarningAsError=true \
        -o "$object" "$source"
done
fresh_objects=()
for source in "${project_sources[@]}"; do
    fresh_objects+=("$output/fresh/lib/${source%.lean}.olean")
done
run fresh-objects sha256sum "${fresh_objects[@]}"
cp "$output/receipts/fresh-objects.stdout" "$output/FRESH-OBJECTS.sha256"

phase=closing_pins
run owned-after sha256sum --check "$output/OWNED-SOURCES.sha256"
run source-after sha256sum --check "$output/DEPENDENCY-SOURCES.sha256"
run system-after sha256sum --check "$output/LEAN-DEPENDENCIES.sha256"
run tools-after sha256sum --check "$output/TOOLS.sha256"
run current-objects-after sha256sum --check "$output/CURRENT-OBJECTS.sha256"
run fresh-objects-after sha256sum --check "$output/FRESH-OBJECTS.sha256"
run source-freeze sha256sum "$output/OWNED-SOURCES.sha256" "$output/DEPENDENCY-SOURCES.sha256" \
    "$output/LEAN-DEPENDENCIES.sha256" "$output/TOOLS.sha256" \
    "$output/CURRENT-OBJECTS.sha256" "$output/FRESH-OBJECTS.sha256"
cp "$output/receipts/source-freeze.stdout" "$output/FREEZE.sha256"
cat > "$output/CORE-READY" <<EOF
CORE-READY: shared SHR64 by exactly one, scoped acceptance exit 0.
API: Sequential.Instruction.shrOne64 (destination : Register), length 3;
Sequential.shrOneFlags64 (old value : Word) (af : Bool).
REX.W D1 /5 mod3; B selects bank; R/X ignored. AF independently chosen.
Scoped Lake build, nine source test/audit entry points, rejecting audit control,
and ACTUALfresh project import-closure build all accepted. The intended audit
negative control exited 1 for its named unapproved axiom; all positive exits 0.
Owned source, dependency source/object, system closure and tool pins: FREEZE.sha256.
Root must review API and hashes before consumer/native replay integration.
No full-library/corpus/native/grading/publication or physical-refinement claim.
EOF
printf '%s\n' "$output" > "$root/.cache/shift-average/isa/ACCEPTED-RUN"
cp "$output/OWNED-SOURCES.sha256" "$root/.cache/shift-average/isa/OWNED-SOURCES.sha256"
cp "$output/CORE-READY" "$root/.cache/shift-average/isa/CORE-READY"
phase=complete
complete=1
