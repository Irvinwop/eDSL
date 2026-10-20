#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail
export PATH="${ELAN_HOME:-$HOME/.elan}/bin:$PATH" LEAN_NUM_THREADS=1 LC_ALL=C
cd "$(dirname "${BASH_SOURCE[0]}")/.."
[[ $(uname -sm) == 'Linux x86_64' ]] || { echo 'Linux x86_64 required' >&2; exit 2; }
[[ $(< lean-toolchain) == leanprover/lean4:v4.35.0 ]] || { echo 'Pinned Lean 4.35.0 required' >&2; exit 2; }
evidence=${NAMED_ELF_IMPORT_EVIDENCE_ROOT:-$PWD/.cache/named-elf-import/regression}
mkdir -p "$evidence"
output=$(mktemp -d "$evidence/run.XXXXXXXX")
output=$(realpath "$output")
printf 'Named ELF import evidence: %s\n' "$output"
mkdir -p "$output/generated" "$output/lib"
complete=0
run() {
    local label=$1 status=0
    shift
    printf '%q ' "$@" > "$output/$label.command"
    date -u +%FT%T.%NZ > "$output/$label.started"
    "$@" > "$output/$label.stdout" 2> "$output/$label.stderr" || status=$?
    printf '%s\n' "$status" > "$output/$label.exit"
    date -u +%FT%T.%NZ > "$output/$label.finished"
    return "$status"
}
finish() {
    local status=$?
    trap - EXIT
    if [[ $complete != 1 && $status == 0 ]]; then status=1; fi
    printf '%s\n' "$status" > "$output/exit"
    if [[ $status == 0 ]]; then
        printf 'PASS: owned linked ELF; exact named import; independent functional/current-resource proof; missing/duplicate and stale proof rejection; fresh kernel; closing pins\n' > "$output/READY"
    fi
    local manifest_list
    manifest_list=$(mktemp "$output/../.manifest.XXXXXXXX")
    if ! (cd "$output" &&
        find . -type f ! -name SHA256SUMS ! -name "manifest-check.*" -print0 | sort -z > "$manifest_list" &&
        xargs -0 sha256sum < "$manifest_list" > SHA256SUMS &&
        sha256sum --quiet -c SHA256SUMS > manifest-check.stdout 2> manifest-check.stderr); then
        status=1
        rm -f "$output/READY"
        printf "1\n" > "$output/exit"
    fi
    rm -f "$manifest_list"
    exit "$status"
}
trap finish EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
run syntax bash -n scripts/check-named-elf-import.sh
run lint shellcheck -s bash scripts/check-named-elf-import.sh
sha256sum lean-toolchain lakefile.lean EDSL.lean Tools/CFG.lean EDSL/ELF/FunctionCandidate*.lean \
    EDSL/ELF/CallerResources.lean EDSL/ELF/CallerResources/Stack.lean \
    EDSL/PureCall/ELFCertificate.lean EDSL/Examples/Verification/Double.lean \
    scripts/check-named-elf-import.sh tests/ELFFunctionCandidate.lean tests/ELFStackCaller.lean \
    tests/templates/NamedELFFunctional.lean fixtures/named-elf-import/functions.c > "$output/SOURCES.sha256"
run build flock /tmp/edsl-lean-build.lock lake build edsl-cfg-import VerificationTests \
    EDSL.Examples.Verification.Double
# Keep the reusable regression module composable with other executable roots.
# Only this private runner module owns a global main declaration.
cat > "$output/ParserRegressions.lean" <<'LEAN'
import tests.ELFFunctionCandidate
def main : IO Unit := EDSL.Tests.ELFFunctionCandidate.run
LEAN
run parser-regressions flock /tmp/edsl-lean-build.lock lake env lean -j1 \
    -DwarningAsError=true --run "$output/ParserRegressions.lean"
compiler=${CC:-gcc}
run compiler-version "$compiler" --version
run compile "$compiler" -O2 -nostdlib -no-pie -Wl,-e,_start -Wl,--build-id=none \
    fixtures/named-elf-import/functions.c -o "$output/function.elf"
run lean-prefix flock /tmp/edsl-lean-build.lock lean --print-prefix
lean_prefix=$(< "$output/lean-prefix.stdout")
find .lake/build/lib/lean "$lean_prefix/lib/lean" -type f \
    \( -name '*.olean' -o -name '*.private' -o -name '*.server' -o -name '*.so' -o -name '*.so.*' \) \
    -print0 | sort -z > "$output/providers.list0"
xargs -0 -r sha256sum < "$output/providers.list0" > "$output/PROVIDERS.sha256"
sha256sum .lake/build/bin/edsl-cfg-import "$lean_prefix/bin/lean" "$lean_prefix/bin/leanchecker" \
    "$(command -v "$compiler")" "$(command -v objcopy)" "$output/function.elf" > "$output/INPUTS-TOOLS.sha256"
# The CLI owns its kernel child's lock. Never outer-lock these invocations.
run import lake env .lake/build/bin/edsl-cfg-import --elf-symbol twice \
    "$output/function.elf" "$output/generated/Named.lean"
run entry-import lake env .lake/build/bin/edsl-cfg-import --elf-symbol _start \
    "$output/function.elf" "$output/generated/Entry.lean"
run override-import lake env .lake/build/bin/edsl-cfg-import --elf-symbol twice --namespace Custom.Proof \
    "$output/function.elf" "$output/generated/Override.lean"
status=0
run invalid-namespace lake env .lake/build/bin/edsl-cfg-import --elf-symbol twice --namespace 'Unsafe;Namespace' \
    "$output/function.elf" "$output/Invalid.lean" || status=$?
[[ $status == 4 && ! -e $output/Invalid.lean ]]
run invalid-namespace-reason grep -F 'namespace suffix requires' "$output/invalid-namespace.stderr"
status=0
run missing lake env .lake/build/bin/edsl-cfg-import --elf-symbol absent \
    "$output/function.elf" "$output/missing.lean" || status=$?
[[ $status == 3 && ! -e $output/missing.lean ]]
run missing-reason grep -F 'selected symbol is absent from complete symbol tables' "$output/missing.stderr"
run duplicate-fixture objcopy --redefine-sym _start=twice "$output/function.elf" "$output/duplicate.elf"
status=0
run duplicate lake env .lake/build/bin/edsl-cfg-import --elf-symbol twice \
    "$output/duplicate.elf" "$output/duplicate.lean" || status=$?
[[ $status == 3 && ! -e $output/duplicate.lean ]]
run duplicate-reason grep -F 'selected symbol has multiple static or dynamic occurrences' "$output/duplicate.stderr"
for module in Named Entry Override; do
    run "$module-module" flock /tmp/edsl-lean-build.lock lake env lean -j1 -DwarningAsError=true \
        -R "$output/generated" -o "$output/lib/$module.olean" "$output/generated/$module.lean"
done
run functional-source cp tests/templates/NamedELFFunctional.lean "$output/generated/Functional.lean"
run functional flock /tmp/edsl-lean-build.lock lake env env \
    LEAN_PATH="$output/lib:$PWD/.lake/build/lib/lean" lean -j1 -DwarningAsError=true \
    -R "$output/generated" -o "$output/lib/Functional.olean" "$output/generated/Functional.lean"
for control in WrongName WrongByte WrongExtent; do
    candidate=$output/generated/$control.lean
    cp "$output/generated/Named.lean" "$candidate"
    case $control in
        WrongName) sed -i '/^def observedNameChunk0 /s/\[116,/[117,/' "$candidate" ;;
        WrongByte) sed -i '/^def observedBytesChunk0 /s/, 195\]/, 144]/' "$candidate" ;;
        WrongExtent) sed -i '/^def observedBytesChunk0 /s/, 195\]/]/' "$candidate" ;;
    esac
    if cmp -s "$output/generated/Named.lean" "$candidate"; then echo 'Mutation did not change source' >&2; exit 1; fi
    status=0
    run "$control" flock /tmp/edsl-lean-build.lock lake env lean -j1 -DwarningAsError=true "$candidate" || status=$?
    [[ $status == 1 ]]
    cat "$output/$control.stdout" "$output/$control.stderr" > "$output/$control.diagnostic"
    run "$control-reason" grep -F '(kernel) application type mismatch' "$output/$control.diagnostic"
done
cat > "$output/generated/Joined.lean" <<'LEAN'
import Named
import Entry
import Override
import Functional
import EDSL.Audit
namespace EDSL.Tests.NamedELFImports
example : ELF.FunctionCandidate.Binding GeneratedCFG.Named.observedInput
    GeneratedCFG.Named.observedELF [116, 119, 105, 99, 101] := GeneratedCFG.Named.binding
example : ELF.FunctionCandidate.Binding GeneratedCFG.Entry.observedInput
    GeneratedCFG.Entry.observedELF [95, 115, 116, 97, 114, 116] := GeneratedCFG.Entry.binding
example : ELF.FunctionCandidate.Binding GeneratedCFG.Custom.Proof.observedInput
    GeneratedCFG.Custom.Proof.observedELF [116, 119, 105, 99, 101] := GeneratedCFG.Custom.Proof.binding
end EDSL.Tests.NamedELFImports
#audit_edsl
LEAN
run joined flock /tmp/edsl-lean-build.lock lake env env \
    LEAN_PATH="$output/lib:$PWD/.lake/build/lib/lean" lean -j1 -DwarningAsError=true \
    -R "$output/generated" -o "$output/lib/Joined.olean" "$output/generated/Joined.lean"
run fresh flock /tmp/edsl-lean-build.lock lake env env \
    LEAN_PATH="$output/lib:$PWD/.lake/build/lib/lean" leanchecker --fresh --verbose Joined
run source-stability sha256sum --quiet -c "$output/SOURCES.sha256"
run provider-stability sha256sum --quiet -c "$output/PROVIDERS.sha256"
run input-tool-stability sha256sum --quiet -c "$output/INPUTS-TOOLS.sha256"
complete=1
