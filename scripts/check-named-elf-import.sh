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
        printf 'PASS: owned linked ELFs; default/explicit named profiles; independent functional/current-resource proof; invalid options and stale suffix proof rejection; fresh kernel; closing pins\n' > "$output/READY"
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
sha256sum lean-toolchain lake-manifest.json lakefile.lean EDSL.lean Tools/CFG.lean EDSL/ELF/Function*.lean \
    EDSL/X86/Sequential/CFG*.lean \
    EDSL/ELF/CallerResources.lean EDSL/ELF/CallerResources/Stack.lean \
    EDSL/PureCall/ELFCertificate.lean EDSL/Examples/Verification/Double.lean \
    scripts/check-named-elf-import.sh tests/ELFFunctionCandidate.lean tests/ELFStackCaller.lean \
    tests/templates/NamedELFFunctional.lean tests/templates/ProfiledNamedELF.lean \
    fixtures/named-elf-import/functions.c fixtures/named-elf-import/profiled.S \
    docs/named-elf-import.md corpus/v1/SHA256SUMS > "$output/SOURCES.sha256"
run frozen-inputs sha256sum --quiet -c corpus/v1/SHA256SUMS
cp corpus/v1/SHA256SUMS "$output/FROZEN.sha256"
run build flock /tmp/edsl-lean-build.lock lake build edsl-cfg-import VerificationTests \
    EDSL.Examples.Verification.Double
# Keep the reusable regression module composable with other executable roots.
# Only this private runner module owns a global main declaration.
cat > "$output/ParserRegressions.lean" <<'LEAN'
import tests.ELFFunctionCandidate
def main : IO Unit := EDSL.Tests.ELFFunctionCandidate.run
LEAN
sha256sum "$output/ParserRegressions.lean" > "$output/DERIVED-SOURCES.sha256"
run parser-regressions flock /tmp/edsl-lean-build.lock lake env lean -j1 \
    -DwarningAsError=true --run "$output/ParserRegressions.lean"
compiler=${CC:-gcc}
run compiler-version "$compiler" --version
run compile "$compiler" -O2 -nostdlib -no-pie -Wl,-e,_start -Wl,--build-id=none \
    fixtures/named-elf-import/functions.c -o "$output/function.elf"
run profiled-compile "$compiler" -nostdlib -no-pie -Wl,-e,profiled -Wl,--build-id=none \
    fixtures/named-elf-import/profiled.S -o "$output/profiled.elf"
run profiled-metadata readelf -h -l -S -s "$output/profiled.elf"
run profiled-disassembly objdump -d "$output/profiled.elf"
run lean-prefix flock /tmp/edsl-lean-build.lock lean --print-prefix
lean_prefix=$(< "$output/lean-prefix.stdout")
find .lake/build/lib/lean "$lean_prefix/lib/lean" -type f \
    \( -name '*.olean' -o -name '*.private' -o -name '*.server' -o -name '*.so' -o -name '*.so.*' \) \
    -print0 | sort -z > "$output/providers.list0"
xargs -0 -r sha256sum < "$output/providers.list0" > "$output/PROVIDERS.sha256"
sha256sum .lake/build/bin/edsl-cfg-import "$lean_prefix/bin/lean" "$lean_prefix/bin/leanchecker" \
    "$(command -v "$compiler")" "$(command -v objcopy)" "$(command -v readelf)" \
    "$(command -v objdump)" "$output/function.elf" "$output/profiled.elf" > "$output/INPUTS-TOOLS.sha256"
# The CLI owns its kernel child's lock. Never outer-lock these invocations.
run import lake env .lake/build/bin/edsl-cfg-import --elf-symbol twice \
    "$output/function.elf" "$output/generated/Named.lean"
run entry-import lake env .lake/build/bin/edsl-cfg-import --elf-symbol _start \
    "$output/function.elf" "$output/generated/Entry.lean"
run override-import lake env .lake/build/bin/edsl-cfg-import --elf-symbol twice --namespace Custom.Proof \
    "$output/function.elf" "$output/generated/Override.lean"
# Profile options are named-only and precede the two paths in any order.
run explicit-default-import lake env .lake/build/bin/edsl-cfg-import --max-bytes 64 \
    --elf-symbol twice --max-nodes 32 "$output/function.elf" "$output/generated/ExplicitDefault.lean"
status=0
run profiled-default lake env .lake/build/bin/edsl-cfg-import --elf-symbol profiled \
    "$output/profiled.elf" "$output/ProfiledDefault.lean" || status=$?
[[ $status == 3 && ! -e $output/ProfiledDefault.lean ]]
run profiled-default-reason grep -F 'failed production admission' "$output/profiled-default.stderr"
status=0
run profiled-byte-only lake env .lake/build/bin/edsl-cfg-import --elf-symbol profiled --max-bytes 68 \
    "$output/profiled.elf" "$output/ProfiledByteOnly.lean" || status=$?
[[ $status == 3 && ! -e $output/ProfiledByteOnly.lean ]]
run profiled-node-reason grep -F 'exceeds 32 static instructions' "$output/profiled-byte-only.stderr"
status=0
run profiled-node-only lake env .lake/build/bin/edsl-cfg-import --max-nodes 40 --elf-symbol profiled \
    "$output/profiled.elf" "$output/ProfiledNodeOnly.lean" || status=$?
[[ $status == 3 && ! -e $output/ProfiledNodeOnly.lean ]]
run profiled-node-only-reason grep -F 'failed production admission' "$output/profiled-node-only.stderr"
run profiled-import lake env .lake/build/bin/edsl-cfg-import --max-nodes 40 --namespace Profiled \
    --elf-symbol profiled --max-bytes 68 "$output/profiled.elf" "$output/generated/Profiled.lean"
usage_rejected() {
    local label=$1 status=0
    shift
    run "$label" lake env .lake/build/bin/edsl-cfg-import "$@" || status=$?
    [[ $status == 2 && ! -e $output/Usage.lean ]]
    run "$label-reason" grep -F 'usage: edsl-cfg-import' "$output/$label.stderr"
}
usage_rejected zero-bytes --elf-symbol profiled --max-bytes 0 "$output/profiled.elf" "$output/Usage.lean"
usage_rejected zero-nodes --elf-symbol profiled --max-nodes 0 "$output/profiled.elf" "$output/Usage.lean"
usage_rejected invalid-integer --elf-symbol profiled --max-bytes twelve "$output/profiled.elf" "$output/Usage.lean"
usage_rejected negative-integer --elf-symbol profiled --max-nodes -1 "$output/profiled.elf" "$output/Usage.lean"
usage_rejected wrapping-profile --elf-symbol profiled --max-bytes 18446744073709551602 \
    "$output/profiled.elf" "$output/Usage.lean"
usage_rejected duplicate-bytes --elf-symbol profiled --max-bytes 68 --max-bytes 68 \
    "$output/profiled.elf" "$output/Usage.lean"
usage_rejected duplicate-nodes --elf-symbol profiled --max-nodes 40 --max-nodes 40 \
    "$output/profiled.elf" "$output/Usage.lean"
usage_rejected duplicate-symbol --elf-symbol profiled --elf-symbol profiled "$output/profiled.elf" "$output/Usage.lean"
usage_rejected duplicate-namespace --elf-symbol profiled --namespace One --namespace Two \
    "$output/profiled.elf" "$output/Usage.lean"
usage_rejected missing-value --elf-symbol profiled --max-bytes
usage_rejected missing-symbol-name --elf-symbol --max-bytes 68 "$output/profiled.elf" "$output/Usage.lean"
usage_rejected missing-namespace --elf-symbol profiled --namespace
usage_rejected unknown-option --elf-symbol profiled --unknown 68 "$output/profiled.elf" "$output/Usage.lean"
usage_rejected raw-profile --max-bytes 68 "$output/profiled.elf" "$output/Usage.lean"
usage_rejected entry-profile --elf 6 --max-bytes 68 "$output/profiled.elf" "$output/Usage.lean"
usage_rejected late-option --elf-symbol profiled "$output/profiled.elf" --max-bytes 68 "$output/Usage.lean"
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
for module in Named Entry Override ExplicitDefault Profiled; do
    sha256sum "$output/generated/$module.lean" >> "$output/DERIVED-SOURCES.sha256"
    run "$module-module" flock /tmp/edsl-lean-build.lock lake env lean -j1 -DwarningAsError=true \
        -R "$output/generated" -o "$output/lib/$module.olean" "$output/generated/$module.lean"
done
run functional-source cp tests/templates/NamedELFFunctional.lean "$output/generated/Functional.lean"
sha256sum "$output/generated/Functional.lean" >> "$output/DERIVED-SOURCES.sha256"
run functional flock /tmp/edsl-lean-build.lock lake env env \
    LEAN_PATH="$output/lib:$PWD/.lake/build/lib/lean" lean -j1 -DwarningAsError=true \
    -R "$output/generated" -o "$output/lib/Functional.olean" "$output/generated/Functional.lean"
run profiled-functional-source cp tests/templates/ProfiledNamedELF.lean "$output/generated/ProfiledFunctional.lean"
sha256sum "$output/generated/ProfiledFunctional.lean" >> "$output/DERIVED-SOURCES.sha256"
run profiled-functional flock /tmp/edsl-lean-build.lock lake env env \
    LEAN_PATH="$output/lib:$PWD/.lake/build/lib/lean" lean -j1 -DwarningAsError=true \
    -R "$output/generated" -o "$output/lib/ProfiledFunctional.olean" "$output/generated/ProfiledFunctional.lean"
for control in WrongName WrongByte WrongExtent; do
    candidate=$output/generated/$control.lean
    cp "$output/generated/Named.lean" "$candidate"
    case $control in
        WrongName) sed -i '/^def observedNameChunk0 /s/\[116,/[117,/' "$candidate" ;;
        WrongByte) sed -i '/^def observedBytesChunk0 /s/, 195\]/, 144]/' "$candidate" ;;
        WrongExtent) sed -i '/^def observedBytesChunk0 /s/, 195\]/]/' "$candidate" ;;
    esac
    if cmp -s "$output/generated/Named.lean" "$candidate"; then echo 'Mutation did not change source' >&2; exit 1; fi
    sha256sum "$candidate" >> "$output/DERIVED-SOURCES.sha256"
    status=0
    run "$control" flock /tmp/edsl-lean-build.lock lake env lean -j1 -DwarningAsError=true "$candidate" || status=$?
    [[ $status == 1 ]]
    cat "$output/$control.stdout" "$output/$control.stderr" > "$output/$control.diagnostic"
    run "$control-reason" grep -F '(kernel) application type mismatch' "$output/$control.diagnostic"
done
cat > "$output/ProfiledControls.lean" <<'LEAN'
import Profiled
import EDSL.ELF.FunctionCandidateSource
open EDSL GeneratedCFG.Profiled
def main (arguments : List String) : IO Unit := do
  let [directory] := arguments | throw (IO.userError "control output directory required")
  let changed := { observedInput with bytes := observedInput.bytes.set 66 0xc3 }
  let changedFile := observedELF.set (observedInput.function.window.offset + 66) 0xc3
  for (label, file, input) in [("ProfiledByteSuffix", observedELF, changed),
      ("ProfiledFileSuffix", changedFile, observedInput)] do
    let .ok text := ELF.FunctionCandidate.sourceWithProfile observedProfile label file
        observedName input observedGraph | throw (IO.userError "control emission failed")
    IO.FS.writeFile ((System.FilePath.mk directory) / (label ++ ".lean")) text
LEAN
sha256sum "$output/ProfiledControls.lean" >> "$output/DERIVED-SOURCES.sha256"
run profiled-controls flock /tmp/edsl-lean-build.lock lake env env \
    LEAN_PATH="$output/lib:$PWD/.lake/build/lib/lean" lean -j1 -DwarningAsError=true \
    --run "$output/ProfiledControls.lean" "$output/generated"
for control in ProfiledByteSuffix ProfiledFileSuffix; do
    sha256sum "$output/generated/$control.lean" >> "$output/DERIVED-SOURCES.sha256"
    status=0
    run "$control" flock /tmp/edsl-lean-build.lock lake env lean -j1 -DwarningAsError=true \
        "$output/generated/$control.lean" || status=$?
    [[ $status == 1 ]]
    cat "$output/$control.stdout" "$output/$control.stderr" > "$output/$control.diagnostic"
    run "$control-reason" grep -F '(kernel) application type mismatch' "$output/$control.diagnostic"
done
cat > "$output/generated/Joined.lean" <<'LEAN'
import Named
import Entry
import Override
import Functional
import ExplicitDefault
import ProfiledFunctional
import EDSL.Audit
namespace EDSL.Tests.NamedELFImports
example : ELF.FunctionCandidate.Binding GeneratedCFG.Named.observedInput
    GeneratedCFG.Named.observedELF [116, 119, 105, 99, 101] := GeneratedCFG.Named.binding
example : ELF.FunctionCandidate.Binding GeneratedCFG.Entry.observedInput
    GeneratedCFG.Entry.observedELF [95, 115, 116, 97, 114, 116] := GeneratedCFG.Entry.binding
example : ELF.FunctionCandidate.Binding GeneratedCFG.Custom.Proof.observedInput
    GeneratedCFG.Custom.Proof.observedELF [116, 119, 105, 99, 101] := GeneratedCFG.Custom.Proof.binding
example : ELF.FunctionCandidate.Binding GeneratedCFG.ExplicitDefault.observedInput
    GeneratedCFG.ExplicitDefault.observedELF [116, 119, 105, 99, 101] := GeneratedCFG.ExplicitDefault.binding
example : ELF.FunctionCandidate.Binding GeneratedCFG.Profiled.observedInput
    GeneratedCFG.Profiled.observedELF [112, 114, 111, 102, 105, 108, 101, 100] 68 :=
  GeneratedCFG.Profiled.binding
end EDSL.Tests.NamedELFImports
#audit_edsl
LEAN
sha256sum "$output/generated/Joined.lean" >> "$output/DERIVED-SOURCES.sha256"
run joined flock /tmp/edsl-lean-build.lock lake env env \
    LEAN_PATH="$output/lib:$PWD/.lake/build/lib/lean" lean -j1 -DwarningAsError=true \
    -R "$output/generated" -o "$output/lib/Joined.olean" "$output/generated/Joined.lean"
find "$output/lib" -type f -name '*.olean' -print0 | sort -z | \
    xargs -0 -r sha256sum > "$output/OBJECTS.sha256"
run fresh flock /tmp/edsl-lean-build.lock lake env env \
    LEAN_PATH="$output/lib:$PWD/.lake/build/lib/lean" leanchecker --fresh --verbose Joined
run source-stability sha256sum --quiet -c "$output/SOURCES.sha256"
run provider-stability sha256sum --quiet -c "$output/PROVIDERS.sha256"
run input-tool-stability sha256sum --quiet -c "$output/INPUTS-TOOLS.sha256"
run frozen-stability sha256sum --quiet -c "$output/FROZEN.sha256"
run object-stability sha256sum --quiet -c "$output/OBJECTS.sha256"
run derived-source-stability sha256sum --quiet -c "$output/DERIVED-SOURCES.sha256"
complete=1
