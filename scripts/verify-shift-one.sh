#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
# Default: native observations plus ordinary-kernel production replay.
# --native-only has no Lean/shared dependency; --replay never executes old ELF.
set -euo pipefail
export LC_ALL=C TZ=UTC PATH=/usr/bin:/bin
unset CPATH C_INCLUDE_PATH CPLUS_INCLUDE_PATH OBJC_INCLUDE_PATH LIBRARY_PATH
unset COMPILER_PATH GCC_EXEC_PREFIX LD_PRELOAD LD_LIBRARY_PATH
unset LEAN_PATH LEAN_SRC_PATH LEAN_SYSROOT ELAN_TOOLCHAIN
umask 077
cd "$(dirname "${BASH_SOURCE[0]}")/.."
root=$(pwd -P)
mode=${1:-full}
accepted=${2:-}
if [[ $# -gt 2 || $(uname -sm) != 'Linux x86_64' ||
      ( $mode != full && $mode != --native-only && $mode != --replay ) ||
      ( $mode == --replay && -z $accepted ) || ( $mode != --replay && $# -gt 1 ) ]]; then
    echo 'usage: verify-shift-one.sh [--native-only | --replay SEALED_RUN] (Linux x86_64)' >&2
    exit 2
fi
mkdir -p .cache/shift-average/native-replay
output=$(mktemp -d "$root/.cache/shift-average/native-replay/run.XXXXXXXX")
printf 'SHR64-by-one evidence: %s\n' "$output"
exec 3>&1 4>&2
exec > "$output/script.log" 2>&1
ulimit -c 0
mkdir -p "$output/receipts" "$output/source" "$output/opcodes" "$output/controls"
phase=initialization
complete=0
rejections=0
af_acceptances=0
run() {
    local label=$1 status=0
    shift
    local receipt="$output/receipts/$label"
    printf 'cwd=%q\nPATH=%q\nLC_ALL=%q\nTZ=%q\nLEAN_NUM_THREADS=%q\nLEAN_PATH=%q\numask=0077\n' \
        "$PWD" "$PATH" "$LC_ALL" "$TZ" "${LEAN_NUM_THREADS-}" "${LEAN_PATH-}" > "$receipt.environment"
    printf 'compiler search/load overrides unset: CPATH C_INCLUDE_PATH CPLUS_INCLUDE_PATH OBJC_INCLUDE_PATH LIBRARY_PATH COMPILER_PATH GCC_EXEC_PREFIX LD_PRELOAD LD_LIBRARY_PATH\n' >> "$receipt.environment"
    printf '%q ' "$@" > "$receipt.command"
    printf '\n' >> "$receipt.command"
    date -u +%FT%T.%NZ > "$receipt.started"
    "$@" > "$receipt.stdout" 2> "$receipt.stderr" || status=$?
    printf '%s\n' "$status" > "$receipt.exit"
    date -u +%FT%T.%NZ > "$receipt.finished"
    if [[ $status -ne 0 ]]; then cat "$receipt.stdout" "$receipt.stderr"; fi
    return "$status"
}
lean_call() {
    local label=$1
    shift
    run "$label" flock /tmp/edsl-lean-build.lock lean -j1 -DwarningAsError=true -DautoImplicit=false "$@"
}
seal() {
    (cd "$output" && find . -type f ! -name EVIDENCE.sha256 ! -name EVIDENCE.seal \
        ! -name 'seal-check.*' -print0 | sort -z | xargs -0 sha256sum) > "$output/EVIDENCE.sha256" || return
    local status=0
    (cd "$output" && sha256sum --quiet --check EVIDENCE.sha256) \
        > "$output/seal-check.stdout" 2> "$output/seal-check.stderr" || status=$?
    printf '%s\n' "$status" > "$output/seal-check.exit"
    (cd "$output" && sha256sum EVIDENCE.sha256) > "$output/EVIDENCE.seal" || return
    return "$status"
}
finish() {
    local status=$? seal_status=0
    trap - EXIT
    set +e
    exec 1>&3 2>&4
    if [[ $status -ne 0 || $complete -ne 1 ]]; then
        [[ $status -ne 0 ]] || status=1
        printf 'INCOMPLETE: exit=%s phase=%s; no completed replay/support/defect claim.\n' \
            "$status" "$phase" > "$output/result.txt"
        rm -f "$output/READY"
    elif [[ $mode == --native-only ]]; then
        printf 'PASS: 10240 native observations; 40 exact windows; 20 negative controls; two AF-policy acceptance controls; no Lean replay.\n' > "$output/result.txt"
    else
        printf 'PASS: 10240 original observations; 320 ordinary-kernel modules; production SHR decode/step, independent AF choices and observed-AF witness; dependency audit.\n' > "$output/result.txt"
    fi
    printf '%s\n' "$status" > "$output/script.exit"
    cat > "$output/RECEIPT.md" <<RECEIPT
Owned finite SHR64-by-one capture and independent persisted arithmetic check.
Mode: $mode; phase: $phase; actual script exit: $status.
Negative controls completed: $rejections/20; AF-policy acceptances: $af_acceptances/2.
Exact commands/environments/times/stdout/stderr/exits: receipts/.
Scope: 40 literal three-byte REX48..4f D1 /5 mod3 windows, normal B bank,
32 rotated full64 vectors and 8 ADD-established flag seeds = 10240 rows.
Actual before/after GPRs: RAX RCX RDX RBX RSP RBP R8 R9 R12 R13 R15.
RSP is observed live; R14 is pointer/R10 scratch. No unobserved GPR/RAM/
permission map or OS resource is reported as a physical measurement.
Unsigned wide division/2; CF old bit0, OF old MSB, SF/ZF/PF result;
all saved nonarithmetic flags preserved. AF is masked, raw physical AF saved.
Synthetic AF-clear/AF-set controls are distinct from raw observations.
No POPFQ; ordinary stack and stable ordinary RAM; AC/DF/TF already off;
CET shadow stack/IBT off, no debug/asynchronous boundary intervention.
PUSHFQ masks RF/VM: hidden physical values/preservation are not observed.
ARCH_SHSTK_STATUS is recorded; unsupported status leaves CET assumptions.
Only newly built owned ELF executes. No arbitrary/frozen external ELF runs.
Owned sources/tools and, for replay, actual production closure sources/objects
are pinned. Provider objects are built in place, never overlaid or copied.
Clang 18.1.3/GNU++26, warnings as errors, no LTO/red zone/CET instrumentation.
Native-only supplies no Lean admission. Full/replay requires all 10240 ordinary
kernel theorems and the transitive axiom audit. No physical CPU/OS refinement,
certificate, registration, corpus increase or defect claim. Root owns integration.
Historical runner/README differences are explicitly inventoried; the complete
old manifest, seal, snapshots and receipts are checked and retained unchanged.
No fresh whole-repository build is implied. See receipts for actual builds.
SHA256 manifests/seals check integrity, not authentication. Failures retained.
RECEIPT
    seal || seal_status=$?
    if [[ $seal_status -ne 0 ]]; then
        status=1
        rm -f "$output/NATIVE-READY" "$output/READY"
        printf 'INCOMPLETE: evidence sealing failed (exit %s); no ready marker.\n' "$seal_status" > "$output/result.txt"
        printf '1\n' > "$output/script.exit"
        printf '\nFinal actual script exit: 1 (sealing exit %s overrides the pre-seal status above).\n' \
            "$seal_status" >> "$output/RECEIPT.md"
        seal
    fi
    if [[ $status -eq 0 ]]; then
        printf 'PASS (%s): %s\n' "$mode" "$output"
    else
        printf 'INCOMPLETE (exit %s, phase %s): %s\n' "$status" "$phase" "$output" >&2
    fi
    exit "$status"
}
trap finish EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
trap 'exit 129' HUP

historical_inputs() {
    phase=historical_seal
    accepted=$(realpath -e "$accepted")
    [[ -d $accepted && $accepted != "$output" && -f $accepted/NATIVE-READY &&
       $(< "$accepted/script.exit") == 0 && $(< "$accepted/seal-check.exit") == 0 ]] || {
        echo 'Historical native run is incomplete'; exit 1;
    }
    # The whole old seal is checked. Never remove the script/README entries.
    run historical-manifest bash -c "cd \"\$1\" && sha256sum --quiet --check EVIDENCE.sha256 && sha256sum --check EVIDENCE.seal" _ "$accepted"
    run historical-snapshots bash -c "cd \"\$1/source\" && sha256sum --check ../OWNED-SOURCES.sha256" _ "$accepted"
    run historical-root sha256sum "$accepted/EVIDENCE.sha256" "$accepted/EVIDENCE.seal"
    run historical-bindings cp "$accepted/OWNED-SOURCES.sha256" "$accepted/SNAPSHOT-SOURCES.sha256" \
        "$accepted/OBSERVATIONS.sha256" "$accepted/FINAL-CODE.sha256" "$output/historical/"
    printf 'path\tclassification\tsealed_sha256\tcurrent_sha256\n' > "$output/historical/source-identity.tsv"
    local digest file current count=0
    local -A seen_sources=()
    while read -r digest file; do
        [[ $digest =~ ^[0-9a-f]{64}$ ]] || { echo 'Malformed historical source digest'; exit 1; }
        [[ -z ${seen_sources[$file]:-} ]] || { echo 'Duplicate historical source'; exit 1; }
        seen_sources[$file]=1
        case $file in
            fixtures/native/shift-one/capture.cpp|fixtures/native/shift-one/registers.S|\
            fixtures/native/shift-one/probes.def|fixtures/native/shift-one/inputs.def|\
            fixtures/native/shift-one/controls.awk)
                run "historical-source-$count" cmp "$file" "$accepted/source/$file"
                current=$(sha256sum "$file"); current=${current%% *}
                printf '%s\texact functional fixture\t%s\t%s\n' "$file" "$digest" "$current" >> "$output/historical/source-identity.tsv"
                ;;
            scripts/verify-shift-one.sh|fixtures/native/shift-one/README.md)
                current=$(sha256sum "$file"); current=${current%% *}
                printf '%s\texplicit runner/documentation evolution\t%s\t%s\n' "$file" "$digest" "$current" >> "$output/historical/source-identity.tsv"
                local status=0
                run "historical-admin-diff-$count" diff -u "$accepted/source/$file" "$file" || status=$?
                [[ $status -le 1 ]] || { echo 'Could not inventory administrative difference'; exit 1; }
                ;;
            *) echo "Unexpected historical source: $file"; exit 1 ;;
        esac
        count=$((count+1))
    done < "$accepted/OWNED-SOURCES.sha256"
    [[ $count -eq 7 ]] || { echo 'Incomplete historical source inventory'; exit 1; }
    cat > "$output/historical/ADMINISTRATIVE-DIFFERENCES.md" <<'NOTE'
All seven old source entries remain bound by the checked original seal and
source snapshots. The five functional capture/assembly/probe/input/control
sources must match current sources byte for byte. Only runner orchestration
and README may differ: native-only was the old default; the current runner
adds production replay and its receipts, and README explains that contract.
Both old/current hashes and literal diffs are retained. No old runner result
is evidence that the changed runner passed. The old ELF is never executed.
NOTE
    for file in capture.tsv probes.tsv inputs.tsv seeds.tsv; do
        run "historical-data-$file" cp "$accepted/$file" "$output/$file"
        run "historical-data-identity-$file" cmp "$accepted/$file" "$output/$file"
    done
    run historical-opcodes cp -r "$accepted/opcodes/." "$output/opcodes/"
    run historical-negative-receipt cp "$accepted/negative-controls.tsv" "$output/historical/negative-controls.tsv"
    run historical-controls awk -F '\t' "NR==1 {if (\$0!=\"control\texpected_exit\tactual_exit\texpected_reason\") exit 1; next} {if (\$2!=1 || \$3!=1) exit 1; n++} END {if(n!=20) exit 1}" "$accepted/negative-controls.tsv"
    rejections=20
    for file in af-clear af-set; do
        [[ $(< "$accepted/receipts/accept-$file.exit") == 0 ]] || { echo 'Historical AF acceptance failed'; exit 1; }
    done
    af_acceptances=2
}

# Read current imports recursively; provider objects remain in their actual
# Lake build location. No overlay, stale-object snapshot or private ready note.
production_closure() {
    local module relative imported_module
    local -a queue=(EDSL.X86.Sequential.ShiftOne EDSL.Audit tests.native.UnaryReplay)
    local -A imported=()
    for ((q=0; q<${#queue[@]}; q++)); do
        module=${queue[$q]}
        [[ -z ${imported[$module]:-} ]] || continue
        imported[$module]=1
        relative=${module//.//}
        [[ -f $relative.lean ]] || { echo "Missing production source: $module" >&2; return 1; }
        printf '%s\n' "$module"
        while read -r imported_module; do
            [[ -n $imported_module ]] || continue
            relative=${imported_module//.//}
            if [[ -f $relative.lean ]]; then queue+=("$imported_module")
            elif [[ $imported_module != Lean && $imported_module != Lean.* &&
                    $imported_module != Std && $imported_module != Std.* &&
                    $imported_module != Init && $imported_module != Init.* ]]; then
                echo "Unresolved production import: $imported_module" >&2; return 1
            fi
        done < <(sed -nE 's/^import +([A-Za-z0-9_.]+) *$/\1/p' "${module//.//}.lean")
    done
}

replay_pipeline() {
    phase=production_toolchain
    export ELAN_HOME="${ELAN_HOME:-$HOME/.elan}"
    export PATH="$ELAN_HOME/bin:/usr/bin:/bin" LEAN_NUM_THREADS=1
    [[ $(< lean-toolchain) == leanprover/lean4:v4.35.0 ]] || { echo 'Unexpected Lean pin'; exit 2; }
    for tool in flock lean lake; do
        sha256sum "$(realpath -e "$(command -v "$tool")")" >> "$output/TOOLS.sha256"
    done
    run lean-version flock /tmp/edsl-lean-build.lock lean --version
    [[ $(< "$output/receipts/lean-version.stdout") == 'Lean (version 4.35.0,'* ]] || {
        echo 'Unexpected executing Lean version'; exit 2;
    }
    run lean-prefix flock /tmp/edsl-lean-build.lock lean --print-prefix
    local lean_prefix
    lean_prefix=$(< "$output/receipts/lean-prefix.stdout")
    run installed-lean-before bash -c "set -euo pipefail; find \"\$1/bin\" \"\$1/lib/lean\" -type f \\( -name lean -o -name lake -o -name \"*.olean*\" -o -name \"*.so*\" \\) -print0 | sort -z | xargs -0 sha256sum" _ "$lean_prefix"
    run installed-lean-pins cp "$output/receipts/installed-lean-before.stdout" "$output/INSTALLED-LEAN.sha256"
    production_closure > "$output/production.modules"
    local -a sources=(lean-toolchain lakefile.lean lake-manifest.json tests/native/RegisterCapture.lean)
    local module relative object
    while IFS= read -r module; do sources+=("${module//.//}.lean"); done < "$output/production.modules"
    run production-sources-before sha256sum "${sources[@]}"
    run production-source-pins cp "$output/receipts/production-sources-before.stdout" "$output/PRODUCTION-SOURCES.sha256"
    phase=production_build
    run model-build flock /tmp/edsl-lean-build.lock lake build \
        EDSL.X86.Sequential.ShiftOne EDSL.Audit tests.native.UnaryReplay
    run production-sources-after-build sha256sum --check "$output/PRODUCTION-SOURCES.sha256"
    while IFS= read -r module; do
        relative=${module//.//}
        object="$root/.lake/build/lib/lean/$relative.olean"
        [[ -f $object ]] || { echo "Missing built production object: $module"; exit 1; }
        sha256sum "$object"* >> "$output/PRODUCTION-OBJECTS.sha256"
    done < "$output/production.modules"
    mkdir -p "$output/lean-lib/Tools/Native" "$output/generated" "$root/.lake/build/lib/lean/tests/native"
    export LEAN_PATH="$output/lean-lib:$root/.lake/build/lib/lean"
    phase=owned_adapter_build
    # Lean resolves a package prefix at one search root. Build tests.* in its
    # actual build directory; a partial tests/ overlay would hide UnaryReplay.
    lean_call capture-helper -R "$root" -o "$root/.lake/build/lib/lean/tests/native/RegisterCapture.olean" tests/native/RegisterCapture.lean
    lean_call adapter -R "$root" -o "$root/.lake/build/lib/lean/tests/native/ShiftOneReplay.olean" tests/native/ShiftOneReplay.lean
    run adapter-object-pins sha256sum "$root/.lake/build/lib/lean/tests/native/RegisterCapture.olean" \
        "$root/.lake/build/lib/lean/tests/native/ShiftOneReplay.olean"
    lean_call driver -R "$root" -o "$output/lean-lib/Tools/Native/ShiftOneReplay.olean" Tools/Native/ShiftOneReplay.lean
    phase=lean_generation
    lean_call generate --run Tools/Native/ShiftOneReplay.lean generate "$output" "$output/generated"
    phase=lean_parser_controls
    # Existing C++ negative evidence is retained; these target Lean's matrix
    # parser and AF policy. Direct semantic corruptions run inside generate.
    local status control
    for control in missing duplicate malformed; do
        case $control in
            missing) run lean-mutate-missing sed "\$d" "$output/capture.tsv" ;;
            duplicate) run lean-mutate-duplicate awk '{print; if (NR==2) print}' "$output/capture.tsv" ;;
            malformed) run lean-mutate-malformed awk "NR==2 {\$0=\"bad\"} {print}" "$output/capture.tsv" ;;
        esac
        status=0
        lean_call "lean-reject-$control" --run Tools/Native/ShiftOneReplay.lean check \
            "$output" "$output/receipts/lean-mutate-$control.stdout" || status=$?
        [[ $status -eq 1 ]] || { echo "Unexpected Lean rejection: $control ($status)"; exit 1; }
    done
    run lean-reason-missing grep -F 'incomplete matrix' "$output/receipts/lean-reject-missing.stderr"
    run lean-reason-duplicate grep -F 'duplicate observation' "$output/receipts/lean-reject-duplicate.stderr"
    run lean-reason-malformed grep -F 'malformed capture field count' "$output/receipts/lean-reject-malformed.stderr"
    for control in af-clear af-set; do
        run "lean-mutate-$control" awk -v "control=$control" -f fixtures/native/shift-one/controls.awk "$output/capture.tsv"
        lean_call "lean-accept-$control" --run Tools/Native/ShiftOneReplay.lean check \
            "$output" "$output/receipts/lean-mutate-$control.stdout"
    done
    phase=kernel_replay
    local count=0
    printf 'import tests.native.ShiftOneReplay\n' > "$output/generated/ShiftOneAudit.lean"
    while IFS= read -r module; do
        [[ $module == "ShiftOneChunk$count" ]] || { echo 'Unexpected generated module sequence'; exit 1; }
        lean_call "kernel-$module" -R "$output/generated" -o "$output/lean-lib/$module.olean" "$output/generated/$module.lean"
        printf 'import %s\n' "$module" >> "$output/generated/ShiftOneAudit.lean"
        count=$((count+1))
    done < "$output/generated/ShiftOne.modules"
    [[ $count -eq 320 ]] || { echo 'Incomplete kernel module coverage'; exit 1; }
    printf '\n#audit_edsl\n' >> "$output/generated/ShiftOneAudit.lean"
    phase=dependency_audit
    lean_call audit -R "$output/generated" -o "$output/lean-lib/ShiftOneAudit.olean" "$output/generated/ShiftOneAudit.lean"
    phase=replay_closing_bindings
    run production-sources-stable sha256sum --check "$output/PRODUCTION-SOURCES.sha256"
    run production-objects-stable sha256sum --check "$output/PRODUCTION-OBJECTS.sha256"
    run adapter-objects-stable sha256sum --check "$output/receipts/adapter-object-pins.stdout"
    run installed-lean-stable sha256sum --check "$output/INSTALLED-LEAN.sha256"
    production_closure > "$output/production-after.modules"
    run production-imports-stable cmp "$output/production.modules" "$output/production-after.modules"
    run current-owned-stable sha256sum --check "$output/OWNED-SOURCES.sha256"
    run current-snapshots-stable sha256sum --check "$output/SNAPSHOT-SOURCES.sha256"
    run current-tools-stable sha256sum --check "$output/TOOLS.sha256"
    run current-observations-stable sha256sum --check "$output/OBSERVATIONS.sha256"
    if [[ $mode == --replay ]]; then
        run historical-seal-stable bash -c "cd \"\$1\" && sha256sum --quiet --check EVIDENCE.sha256 && sha256sum --check EVIDENCE.seal" _ "$accepted"
        run historical-root-stable sha256sum --check "$output/receipts/historical-root.stdout"
    fi
    printf 'Complete finite production SHR replay: 10240 rows, both AF choices, observed AF witness, ordinary kernel and transitive audit.\n' > "$output/READY"
}

phase=tool_availability
compiler=/usr/bin/clang++-18
for tool in "$compiler" bash ld.bfd ldd objdump objcopy readelf timeout sha256sum shellcheck \
    awk sed grep find sort xargs realpath install cp cmp diff uname lscpu getconf date mktemp mkdir cat rm; do
    tool_path=$(command -v "$tool") || { echo "Missing required runner tool: $tool"; exit 2; }
    tool_path=$(realpath -e "$tool_path")
    printf '%s\t%s\n' "$tool" "$tool_path" >> "$output/tool-paths.tsv"
    sha256sum "$tool_path" >> "$output/TOOLS.sha256"
done
run platform uname -srmo
run cpu lscpu
run libc getconf GNU_LIBC_VERSION
run compiler-version "$compiler" --version
run compiler-pin "$compiler" -dumpversion
run compiler-target "$compiler" -print-target-triple
[[ $(< "$output/receipts/compiler-pin.stdout") == 18.1.3 ]] || { echo 'Unsupported compiler: expected Clang 18.1.3'; exit 2; }
[[ $(< "$output/receipts/compiler-target.stdout") == x86_64-pc-linux-gnu ]] || { echo 'Unsupported compiler target'; exit 2; }
run compiler-libraries ldd "$(realpath -e "$compiler")"
run compiler-library-paths awk "/=> \\/[^ ]/ {print \$3} /^[ \\t]*\\// {print \$1}" "$output/receipts/compiler-libraries.stdout"
while IFS= read -r library; do
    [[ -f $library ]] || { echo "Unresolved compiler library: $library"; exit 2; }
    sha256sum "$(realpath -e "$library")" >> "$output/TOOL-LIBRARIES.sha256"
done < "$output/receipts/compiler-library-paths.stdout"
run script-syntax bash -n scripts/verify-shift-one.sh
run shellcheck shellcheck -s bash scripts/verify-shift-one.sh

phase=source_pins
owned=(fixtures/native/shift-one/capture.cpp fixtures/native/shift-one/registers.S
    fixtures/native/shift-one/probes.def fixtures/native/shift-one/inputs.def
    fixtures/native/shift-one/controls.awk fixtures/native/shift-one/README.md
    scripts/verify-shift-one.sh)
if [[ $mode != --native-only ]]; then
    owned+=(tests/native/ShiftOneReplay.lean Tools/Native/ShiftOneReplay.lean)
fi
run owned-before sha256sum "${owned[@]}"
run save-owned-pins cp "$output/receipts/owned-before.stdout" "$output/OWNED-SOURCES.sha256"
snapshots=()
for file in "${owned[@]}"; do
    run "copy-source-${#snapshots[@]}" install -D -m 0644 "$file" "$output/source/$file"
    run "compare-source-${#snapshots[@]}" cmp "$file" "$output/source/$file"
    snapshots+=("$output/source/$file")
done
run snapshot-pins sha256sum "${snapshots[@]}"
run save-snapshot-pins cp "$output/receipts/snapshot-pins.stdout" "$output/SNAPSHOT-SOURCES.sha256"
source_dir="$output/source/fixtures/native/shift-one"
if [[ $mode == --replay ]]; then
    mkdir -p "$output/historical"
    historical_inputs
fi

phase=native_compile
cpp_flags=(-std=gnu++26 -O2 -Wall -Wextra -Wpedantic -Werror -fno-lto
    -fcf-protection=none -mno-red-zone -fPIE -MD -MF "$output/capture.d")
asm_flags=(-Wall -Wextra -Werror -fno-lto -fcf-protection=none -mno-red-zone -fPIE)
link_flags=(-fuse-ld=bfd -fno-lto -pie '-Wl,--build-id=none,-z,noexecstack,-t')
run cpp-driver "$compiler" -### "${cpp_flags[@]}" -c "$source_dir/capture.cpp" -o "$output/capture.o"
run compile-cpp "$compiler" "${cpp_flags[@]}" -c "$source_dir/capture.cpp" -o "$output/capture.o"
run asm-driver "$compiler" -### "${asm_flags[@]}" -c "$source_dir/registers.S" -o "$output/registers.o"
run compile-asm "$compiler" "${asm_flags[@]}" -c "$source_dir/registers.S" -o "$output/registers.o"
run link-driver "$compiler" -### "${link_flags[@]}" "$output/capture.o" "$output/registers.o" -o "$output/capture.elf"
run link "$compiler" "${link_flags[@]}" "$output/capture.o" "$output/registers.o" -o "$output/capture.elf"
run disassembly objdump -d "$output/capture.elf"
run elf readelf -h -l -S -s -r -n -d -W "$output/capture.elf"
run final-text objcopy --dump-section ".text=$output/capture.text.bin" "$output/capture.elf"
run final-code-before sha256sum "$output/capture.o" "$output/registers.o" "$output/capture.elf" "$output/capture.text.bin"
run save-code-pins cp "$output/receipts/final-code-before.stdout" "$output/FINAL-CODE.sha256"
run runtime-libraries ldd "$output/capture.elf"
run runtime-library-paths awk "/=> \\/[^ ]/ {print \$3} /^[ \\t]*\\// {print \$1}" "$output/receipts/runtime-libraries.stdout"
while IFS= read -r library; do
    [[ -f $library ]] || { echo "Unresolved runtime library: $library"; exit 2; }
    sha256sum "$(realpath -e "$library")" >> "$output/RUNTIME-LIBRARIES.sha256"
done < "$output/receipts/runtime-library-paths.stdout"

phase=native_capture
if [[ $mode != --replay ]]; then
    run native timeout --kill-after=2 30 "$output/capture.elf" capture "$output"
    run save-native cp "$output/receipts/native.stdout" "$output/capture.tsv"
fi
phase=independent_native_check
run independent-check timeout --kill-after=2 30 "$output/capture.elf" check "$output/capture.tsv" "$output/opcodes"
run observation-pins sha256sum "$output/capture.tsv" "$output/probes.tsv" "$output/inputs.tsv" "$output/seeds.tsv" "$output"/opcodes/*.bin
run save-observation-pins cp "$output/receipts/observation-pins.stdout" "$output/OBSERVATIONS.sha256"

phase=persisted_corruption_controls
if [[ $mode != --replay ]]; then
printf 'control\texpected_exit\tactual_exit\texpected_reason\n' > "$output/negative-controls.tsv"
expect_reject() {
    local label=$1 reason=$2 status=0
    shift 2
    run "reject-$label" "$@" || status=$?
    printf '%s\t1\t%s\t%s\n' "$label" "$status" "$reason" >> "$output/negative-controls.tsv"
    [[ $status -eq 1 ]] || { echo "Unexpected rejection status for $label: $status"; exit 1; }
    run "reason-$label" grep -F -- "$reason" "$output/receipts/reject-$label.stderr"
    rejections=$((rejections+1))
}
for control in result upper-result cf pf zf sf of if high-flag register rsp input seed-flags window seed-range malformed; do
    run "mutate-$control" awk -v "control=$control" -f "$source_dir/controls.awk" "$output/capture.tsv"
    case $control in
        result|upper-result) reason='independent unsigned division result mismatch' ;;
        cf|pf|zf|sf|of|if|high-flag) reason='independent defined/preserved flags mismatch (AF masked)' ;;
        register|rsp) reason='observed nondestination GPR changed' ;;
        input) reason='controlled input mismatch' ;;
        seed-flags) reason='flag seed mismatch' ;;
        window) reason='captured opcode mismatch' ;;
        seed-range) reason='invalid seed' ;;
        malformed) reason='malformed capture field count' ;;
    esac
    expect_reject "$control" "$reason" timeout --kill-after=2 30 "$output/capture.elf" check \
        "$output/receipts/mutate-$control.stdout" "$output/opcodes"
done
run mutate-missing sed "\$d" "$output/capture.tsv"
expect_reject missing 'incomplete matrix' timeout --kill-after=2 30 "$output/capture.elf" check \
    "$output/receipts/mutate-missing.stdout" "$output/opcodes"
run mutate-duplicate awk '{print; if (NR==2) print}' "$output/capture.tsv"
expect_reject duplicate 'duplicate observation' timeout --kill-after=2 30 "$output/capture.elf" check \
    "$output/receipts/mutate-duplicate.stdout" "$output/opcodes"
run copy-opcode-controls cp -r "$output/opcodes" "$output/controls/opcodes"
printf '\110\321\351' > "$output/controls/opcodes/shr_rax_48.bin"
expect_reject opcode-file 'opcode file mismatch' timeout --kill-after=2 30 "$output/capture.elf" check \
    "$output/capture.tsv" "$output/controls/opcodes"

phase=af_policy_controls
for control in af-clear af-set; do
    run "mutate-$control" awk -v "control=$control" -f "$source_dir/controls.awk" "$output/capture.tsv"
    run "accept-$control" timeout --kill-after=2 30 "$output/capture.elf" check \
        "$output/receipts/mutate-$control.stdout" "$output/opcodes"
    af_acceptances=$((af_acceptances+1))
done

phase=linked_window_control
run compile-negative-asm "$compiler" "${asm_flags[@]}" -DSHIFT_ONE_NEGATIVE_WINDOW=1 \
    -c "$source_dir/registers.S" -o "$output/controls/registers-negative.o"
run link-negative "$compiler" "${link_flags[@]}" "$output/capture.o" "$output/controls/registers-negative.o" \
    -o "$output/controls/window-negative.elf"
run disassembly-negative objdump -d "$output/controls/window-negative.elf"
run negative-code-pins sha256sum "$output/controls/registers-negative.o" "$output/controls/window-negative.elf" "$output/controls/opcodes/shr_rax_48.bin"
expect_reject live-window 'live linked bytes differ from independent literal window: shr_rax_48' \
    timeout --kill-after=2 30 "$output/controls/window-negative.elf" capture "$output/controls"
[[ ! -s $output/receipts/reject-live-window.stdout ]] || { echo 'Changed live window ran past preflight'; exit 1; }
[[ $rejections -eq 20 && $af_acceptances -eq 2 ]] || { echo 'Incomplete control matrix'; exit 1; }
fi

phase=closing_bindings
run owned-stable sha256sum --check "$output/OWNED-SOURCES.sha256"
run snapshots-stable sha256sum --check "$output/SNAPSHOT-SOURCES.sha256"
run tools-stable sha256sum --check "$output/TOOLS.sha256"
run tool-libraries-stable sha256sum --check "$output/TOOL-LIBRARIES.sha256"
run runtime-libraries-stable sha256sum --check "$output/RUNTIME-LIBRARIES.sha256"
run final-code-stable sha256sum --check "$output/FINAL-CODE.sha256"
run observations-stable sha256sum --check "$output/OBSERVATIONS.sha256"
if [[ $mode != --replay ]]; then
    run negative-code-stable sha256sum --check "$output/receipts/negative-code-pins.stdout"
fi
run owned-after sha256sum "${owned[@]}"
run owned-equal cmp "$output/receipts/owned-before.stdout" "$output/receipts/owned-after.stdout"
printf 'Native-only capture/check and corruption/AF-policy controls; no Lean/model/certificate claim.\n' > "$output/NATIVE-READY"
if [[ $mode != --native-only ]]; then replay_pipeline; phase=replay_complete
else phase=native_complete
fi
complete=1
