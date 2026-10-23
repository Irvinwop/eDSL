#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
# Native-only is independently useful while the production closure is built.
set -euo pipefail
export LC_ALL=C
export PATH="${ELAN_HOME:-$HOME/.elan}/bin:$PATH"
export LEAN_NUM_THREADS=1
cd "$(dirname "${BASH_SOURCE[0]}")/.."
root=$(pwd -P)
mode=${1:-full}
accepted=${2:-}
if [[ $(uname -sm) != 'Linux x86_64' || $# -gt 2 ||
    ( $mode != full && $mode != --native-only && $mode != --replay ) ||
    ( $mode == --replay && -z $accepted ) || ( $mode != --replay && $# -gt 1 ) ]]; then
    echo 'usage: verify-counter-displacement.sh [--native-only | --replay NATIVE_RUN_DIRECTORY] (Linux x86_64)' >&2
    exit 2
fi
mkdir -p .cache/popcount/native
output=$(mktemp -d "$root/.cache/popcount/native/run.XXXXXXXX")
printf 'Counter/displacement evidence: %s\n' "$output"
exec 3>&1 4>&2
exec > "$output/script.log" 2>&1
ulimit -c 0
mkdir -p "$output/receipts" "$output/source" "$output/opcodes"
phase=initialization
complete=0
matrix_summary='No complete native matrix comparison recorded.'
observation_count=0
# Check memory after taking the shared lock, before starting each Lean process.
# A resource failure leaves the run incomplete; it never weakens a proof gate.
edsl_lean_guard() {
    awk '/MemAvailable/ {exit !($2>=1572864)}' /proc/meminfo || return 75
    exec "$@"
}
export -f edsl_lean_guard
lean_gate=(flock /tmp/edsl-lean-build.lock bash -c 'edsl_lean_guard "$@"' edsl-lean)
run() {
    local label=$1 status=0
    shift
    local receipt="$output/receipts/$label"
    printf 'cwd=%q\nPATH=%q\nLEAN_NUM_THREADS=%q\nLEAN_PATH=%q\n' "$PWD" "$PATH" "$LEAN_NUM_THREADS" "${LEAN_PATH-}" > "$receipt.environment"
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
    run "$1" "${lean_gate[@]}" lean -j1 -DwarningAsError=true -DautoImplicit=false \
        -DmaxHeartbeats=300000 -DmaxRecDepth=128 "${@:2}"
}
finish() {
    local status=$? seal_status=0
    trap - EXIT
    set +e
    exec 1>&3 2>&4
    if [[ $status -ne 0 || $complete -ne 1 ]]; then
        [[ $status -ne 0 ]] || status=1
        printf 'INCOMPLETE: exit=%s phase=%s; no model/support/defect claim\n' "$status" "$phase" > "$output/result.txt"
    fi
    printf '%s\n' "$status" > "$output/script.exit"
    cat > "$output/RECEIPT.md" <<RECEIPT
Owned finite ADD32/SUB32/CMP32-imm8 / INC32 / LEA64 / LEA32 / TEST-low8 conformance.
Mode: $mode; phase: $phase; actual exit: $status.
Exact commands, environments, stdout, stderr, timestamps and exits: receipts/.
Checked matrix (reported only after complete persisted comparison):
$matrix_summary
SUB/LEA32 write zero-extended low32; CMP/TEST preserve every full64 GPR. Actual GPRs:
RAX RCX RDX RBX RSP RBP R8 R9 R12 R13 R15. RSP is source-only.
Other GPRs and RAM/permission maps in replay are synthetic full-state frames.
PUSHFQ clears saved RF/VM; no hidden physical RF/VM preservation established.
AC/DF/TF off, ordinary RAM, Linux x86-64 SysV, debug/asynchronous boundaries,
four-level canonical model and CET-off target limitations remain explicit.
No POPFQ. LEA does not read DATA, including noncanonical/modular results.
TEST compares every flag except undefined AF. Both real model step choices
must set AF to their respective false/true values with all other bits exact.
AF-only flips are synthetic admissibility controls, never extra observations.
Native-only success is independent finite mathematical comparison, not a Lean
replay or universal ISA/OS refinement. Full replay uses actual public decodeAt
and step for both AF choices with ordinary kernel terms at default budgets.
Full-project registration and fresh replay are separate validation gates.
RECEIPT
    (cd "$output" && find . -type f ! -name EVIDENCE.sha256 ! -name EVIDENCE.seal ! -name 'seal-check.*' -print0 |
        sort -z | xargs -0 sha256sum) > "$output/EVIDENCE.sha256"
    (cd "$output" && sha256sum --quiet --check EVIDENCE.sha256) \
        > "$output/seal-check.stdout" 2> "$output/seal-check.stderr" || seal_status=$?
    printf '%s\n' "$seal_status" > "$output/seal-check.exit"
    sha256sum "$output/EVIDENCE.sha256" > "$output/EVIDENCE.seal"
    if [[ $seal_status -ne 0 ]]; then status=1; fi
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

phase=tool_availability
compiler=${CXX:-clang++}
for tool in "$compiler" bash objdump objcopy readelf flock timeout sha256sum shellcheck awk sed grep find sort xargs realpath install cp cmp uname lscpu getconf date mktemp mkdir cat; do
    tool_path=$(command -v "$tool") || { echo "Missing standard runner tool: $tool"; exit 2; }
    printf '%s\t%s\n' "$tool" "$(realpath "$tool_path")" >> "$output/tool-paths.tsv"
    sha256sum "$(realpath "$tool_path")" >> "$output/TOOLS.sha256"
done
run platform uname -srmo
run cpu lscpu
run libc getconf GNU_LIBC_VERSION
run compiler-version "$compiler" --version
run script-syntax bash -n scripts/verify-counter-displacement.sh
run shellcheck shellcheck -s bash scripts/verify-counter-displacement.sh

phase=source_pins
owned=(fixtures/native/counter-displacement/capture.cpp fixtures/native/counter-displacement/registers.S
    fixtures/native/counter-displacement/probes.def fixtures/native/counter-displacement/inputs.def
    scripts/verify-counter-displacement.sh)
if [[ -f tests/native/CounterDisplacementReplay.lean ]]; then
    owned+=(tests/native/CounterDisplacementReplay.lean Tools/Native/CounterDisplacementReplay.lean)
fi
if [[ -f tests/native/RegisterCapture.lean ]]; then owned+=(tests/native/RegisterCapture.lean); fi
if [[ -f fixtures/native/counter-displacement/README.md ]]; then owned+=(fixtures/native/counter-displacement/README.md); fi
run owned-before sha256sum "${owned[@]}" lean-toolchain
cp "$output/receipts/owned-before.stdout" "$output/OWNED-SOURCES.sha256"
for file in "${owned[@]}" lean-toolchain; do install -D -m 0644 "$file" "$output/source/$file"; done
providers=(EDSL/X86/Sequential/Model.lean EDSL/X86/Sequential/Flags.lean EDSL/X86/Sequential/Decode.lean
    EDSL/X86/Sequential/DecodeTransport.lean EDSL/X86/Sequential/Machine.lean
    EDSL/X86/Sequential/Counter32.lean EDSL/X86/Sequential/Immediate32.lean
    EDSL/X86/Sequential/Address32.lean EDSL/X86/Sequential/TestImmediate8.lean
    EDSL/Audit.lean tests/native/UnaryReplay.lean)
run provider-sources-before sha256sum "${providers[@]}"
# These existing objects are observed only; never imported or copied in native-only mode.
for file in "${providers[@]}"; do
    object=".lake/build/lib/lean/${file%.lean}.olean"
    if [[ -f $object ]]; then sha256sum "$object" >> "$output/PROVIDERS-OBSERVED-BEFORE.sha256"; fi
done

if [[ $mode == --replay ]]; then
    phase=accepted_native
    accepted=$(realpath "$accepted")
    (cd "$accepted" && run accepted-seal sha256sum --quiet --check EVIDENCE.sha256)
    [[ -f $accepted/NATIVE-READY ]] || { echo 'Accepted run lacks NATIVE-READY'; exit 2; }
    run accepted-pins sha256sum "$accepted/receipts/native.stdout" "$accepted/capture.elf" "$accepted/probes.tsv" "$accepted/inputs.tsv" "$accepted/OWNED-SOURCES.sha256" "$accepted"/opcodes/*.bin
    for file in capture.cpp registers.S probes.def inputs.def; do
        run "accepted-source-$file" cmp "$accepted/source/fixtures/native/counter-displacement/$file" \
            "$output/source/fixtures/native/counter-displacement/$file"
    done
    cp "$accepted/receipts/native.stdout" "$output/capture.tsv"
    cp "$accepted/probes.tsv" "$accepted/inputs.tsv" "$output/"
    cp "$accepted"/opcodes/*.bin "$output/opcodes/"
    # Re-use the exact checked native executable, without executing its windows again.
    cp "$accepted/capture.elf" "$output/capture.elf"
else
    phase=native_compile
    run compile-cpp "$compiler" -std=gnu++26 -O2 -Wall -Wextra -Wpedantic -Werror \
        -fno-lto -fcf-protection=none -mno-red-zone -c \
        "$output/source/fixtures/native/counter-displacement/capture.cpp" -o "$output/capture.o"
    run compile-asm "$compiler" -c "$output/source/fixtures/native/counter-displacement/registers.S" -o "$output/registers.o"
    run link "$compiler" -fno-lto '-Wl,--build-id=none,-z,noexecstack' "$output/capture.o" "$output/registers.o" -o "$output/capture.elf"
    run disassembly objdump -d "$output/capture.elf"
    run elf readelf -h -l -S -s -r -n -W "$output/capture.elf"
    run final-text objcopy --dump-section ".text=$output/capture.text.bin" "$output/capture.elf"
    run final-code-before sha256sum "$output/capture.elf" "$output/capture.text.bin"
    cp "$output/receipts/final-code-before.stdout" "$output/FINAL-CODE.sha256"
    phase=native_capture
    run native timeout --kill-after=2 30 "$output/capture.elf" capture "$output"
    cp "$output/receipts/native.stdout" "$output/capture.tsv"
fi
phase=independent_native_check
run independent-check "$output/capture.elf" check "$output/capture.tsv" "$output/opcodes"
matrix_summary=$(< "$output/receipts/independent-check.stdout")
observation_count=$(awk 'END {print NR-1}' "$output/capture.tsv")
run opcode-pins sha256sum "$output"/opcodes/*.bin
cp "$output/receipts/opcode-pins.stdout" "$output/OPCODES.sha256"

phase=native_malformed_controls
awk -F '\t' 'BEGIN {OFS=FS} NR==2 {$18="0000000100000000"} {print}' "$output/capture.tsv" > "$output/corrupt-output.tsv"
awk -F '\t' 'BEGIN {OFS=FS} NR==2 {$6="0000000000000202"} {print}' "$output/capture.tsv" > "$output/corrupt-flags.tsv"
sed '$d' "$output/capture.tsv" > "$output/missing.tsv"
cp "$output/capture.tsv" "$output/duplicate.tsv"
sed -n '2p' "$output/capture.tsv" >> "$output/duplicate.tsv"
awk -F '\t' 'BEGIN {OFS=FS} NR==2 {NF=27} {print}' "$output/capture.tsv" > "$output/malformed.tsv"
# Mutate actual observed bits, including borrow versus ADD(-imm), nibble
# borrow and signed-minimum overflow. Each named capture must occur once.
corrupt_scalar() {
    local control=$1 case_id=$2 probe_name=$3 field=$4 digit=$5 mask=$6
    awk -F '\t' -v case_id="$case_id" -v probe_name="$probe_name" \
        -v field="$field" -v digit="$digit" -v mask="$mask" '
        BEGIN {OFS=FS; hex="0123456789abcdef"}
        NR>1 && $1==case_id && $2==probe_name && $3=="0" {
            word=$field
            n=index(hex,substr(word,digit,1))-1
            if (length(word)!=16 || n<0) exit 1
            n=int(n/mask)%2==0 ? n+mask : n-mask
            $field=substr(word,1,digit-1) substr(hex,n+1,1) substr(word,digit+1)
            changed++
        }
        {print}
        END {if (changed!=1) exit 1}' "$output/capture.tsv" > "$output/$control.tsv"
}
for family in sub cmp; do
    corrupt_scalar "$family-upper32" zero_dirty "${family}_eax_80" 18 8 1
    corrupt_scalar "$family-borrow" zero_dirty "${family}_eax_80" 6 16 1
    corrupt_scalar "$family-auxiliary" nibble_next "${family}_eax_7f" 6 15 1
    corrupt_scalar "$family-overflow" signed_min "${family}_eax_7f" 6 14 8
done
corrupt_scalar lea32-upper32 zero_dirty lea32_base_np 18 8 1
corrupt_scalar lea32-carry zero_dirty lea32_sib_47_all_alias 6 16 1
corrupt_scalar lea32-auxiliary zero_dirty lea32_sib_47_all_alias 6 15 1
corrupt_scalar lea32-overflow zero_dirty lea32_sib_47_all_alias 6 14 8
corrupt_scalar lea32-preserved zero_dirty lea32_sib_47_all_alias 6 1 1
corrupt_scalar test-low8 byte_high test_al_ff 18 16 1
corrupt_scalar test-upper32 byte_high test_al_ff 18 8 1
corrupt_scalar test-other-gpr byte_high test_al_ff 19 16 1
corrupt_scalar test-rsp zero_dirty test_spl_ff 22 16 1
corrupt_scalar test-carry byte_high test_al_ff 6 16 1
corrupt_scalar test-parity byte_high test_al_ff 6 16 4
corrupt_scalar test-zero byte_high test_al_ff 6 15 4
corrupt_scalar test-sign byte_high test_al_ff 6 15 8
corrupt_scalar test-overflow byte_high test_al_ff 6 14 8
corrupt_scalar test-preserved byte_high test_al_ff 6 1 1
# This is a positive SYNTHETIC admissibility control, not a physical observation.
corrupt_scalar test-af-admissible byte_high test_al_ff 6 15 1
awk -F '\t' 'BEGIN {OFS=FS} NR==2 {$4="83c081"} {print}' "$output/capture.tsv" > "$output/wrong-bytes.tsv"
awk -F '\t' 'BEGIN {OFS=FS} NR==2 {$4=$4 "90"} {print}' "$output/capture.tsv" > "$output/wrong-length.tsv"
native_controls=(corrupt-output corrupt-flags missing duplicate malformed
    sub-upper32 cmp-upper32 sub-borrow cmp-borrow sub-auxiliary cmp-auxiliary sub-overflow cmp-overflow
    lea32-upper32 lea32-carry lea32-auxiliary lea32-overflow lea32-preserved
    test-low8 test-upper32 test-other-gpr test-rsp
    test-carry test-parity test-zero test-sign test-overflow test-preserved wrong-bytes wrong-length)
for control in "${native_controls[@]}"; do
    status=0
    run "native-reject-$control" "$output/capture.elf" check "$output/$control.tsv" "$output/opcodes" || status=$?
    [[ $status -eq 1 ]] || { echo "Invalid native negative-control exit: $control"; exit 1; }
done
run native-admit-test-af "$output/capture.elf" check "$output/test-af-admissible.tsv" "$output/opcodes"
grep -F 'independent mathematical result mismatch' "$output/receipts/native-reject-corrupt-output.stderr"
grep -F 'independent mathematical flags mismatch' "$output/receipts/native-reject-corrupt-flags.stderr"
grep -F 'incomplete matrix' "$output/receipts/native-reject-missing.stderr"
grep -F 'duplicate observation' "$output/receipts/native-reject-duplicate.stderr"
grep -F 'malformed capture field count' "$output/receipts/native-reject-malformed.stderr"
grep -F 'independent mathematical result mismatch' "$output/receipts/native-reject-sub-upper32.stderr"
grep -F 'observed CMP operand changed' "$output/receipts/native-reject-cmp-upper32.stderr"
for family in sub cmp; do
    for bit in borrow auxiliary overflow; do
        grep -F 'independent mathematical flags mismatch' "$output/receipts/native-reject-$family-$bit.stderr"
    done
done
grep -F 'independent mathematical result mismatch' "$output/receipts/native-reject-lea32-upper32.stderr"
for control in lea32-carry lea32-auxiliary lea32-overflow lea32-preserved \
    test-carry test-parity test-zero test-sign test-overflow test-preserved; do
    grep -F 'independent mathematical flags mismatch' "$output/receipts/native-reject-$control.stderr"
done
for control in test-low8 test-upper32 test-rsp; do
    grep -F 'observed TEST operand changed' "$output/receipts/native-reject-$control.stderr"
done
grep -F 'observed nondestination GPR changed' "$output/receipts/native-reject-test-other-gpr.stderr"
for control in wrong-bytes wrong-length; do
    grep -F 'captured opcode mismatch' "$output/receipts/native-reject-$control.stderr"
done
# Persisted matrix/schema controls are deliberately separate from native rows.
# A smaller internally complete capture must not redefine the required keys.
manifest_controls=(missing-probe wrong-address-form missing-input)
for control in "${manifest_controls[@]}"; do
    control_dir="$output/manifest-$control"
    mkdir -p "$control_dir"
    cp -a "$output/opcodes" "$control_dir/opcodes"
    cp "$output/probes.tsv" "$output/inputs.tsv" "$output/capture.tsv" "$control_dir/"
    case $control in
        missing-probe)
            awk -F '\t' '$1!="lea32_base_np"' "$output/probes.tsv" > "$control_dir/probes.tsv"
            awk -F '\t' 'NR==1 || $2!="lea32_base_np"' "$output/capture.tsv" > "$control_dir/capture.tsv"
            ;;
        wrong-address-form)
            awk -F '\t' 'BEGIN {OFS=FS} $1=="lea32_disp_np_alias" {$9=3} {print}' \
                "$output/probes.tsv" > "$control_dir/probes.tsv"
            ;;
        missing-input)
            awk -F '\t' '$1!="zero_dirty"' "$output/inputs.tsv" > "$control_dir/inputs.tsv"
            awk -F '\t' 'NR==1 || $1!="zero_dirty"' "$output/capture.tsv" > "$control_dir/capture.tsv"
            ;;
    esac
    status=0
    run "native-reject-manifest-$control" "$output/capture.elf" check \
        "$control_dir/capture.tsv" "$control_dir/opcodes" || status=$?
    [[ $status -eq 1 ]] || { echo "Invalid native manifest-control exit: $control"; exit 1; }
    if [[ $control == missing-input ]]; then
        grep -F 'input manifest mismatch' "$output/receipts/native-reject-manifest-$control.stderr"
    else
        grep -F 'probe manifest mismatch' "$output/receipts/native-reject-manifest-$control.stderr"
    fi
done
rejection_control_count=$((${#native_controls[@]}+${#manifest_controls[@]}))

if [[ $mode != --native-only ]]; then
    phase=production_toolchain
    [[ $(< lean-toolchain) == leanprover/lean4:v4.35.0 ]] || { echo 'Unexpected Lean pin'; exit 2; }
    run lean-version "${lean_gate[@]}" lean --version
    run lean-prefix "${lean_gate[@]}" lean --print-prefix
    lean_prefix=$(< "$output/receipts/lean-prefix.stdout")
    sha256sum "$lean_prefix/bin/lean" "$lean_prefix/lib/lean/Init.olean" \
        "$lean_prefix/lib/lean/Lean.olean" "$lean_prefix/lib/lean/Std.olean" > "$output/INSTALLED-LEAN.sha256"
    phase=production_build
    # Build the current production closure before copying its pinned providers.
    run model-build "${lean_gate[@]}" lake build \
        EDSL.X86.Sequential.Machine EDSL.X86.Sequential.Immediate32 \
        EDSL.X86.Sequential.Address32 EDSL.X86.Sequential.TestImmediate8 EDSL.Audit tests.native.UnaryReplay
    mkdir -p "$output/lean-lib/tests/native" "$output/lean-lib/Tools/Native" "$output/generated"
    provider="$root/.lake/build/lib/lean"
    declare -A imported=()
    queue=(tests.native.UnaryReplay EDSL.X86.Sequential.Immediate32
        EDSL.X86.Sequential.Address32 EDSL.X86.Sequential.TestImmediate8 EDSL.Audit)
    for ((q=0; q<${#queue[@]}; q++)); do
        module=${queue[$q]}
        [[ -z ${imported[$module]:-} ]] || continue
        imported[$module]=1
        relative=${module//.//}
        source="$relative.lean"
        object="$provider/$relative.olean"
        [[ -f $source && -f $object ]] || { echo "Missing coherent production import $module"; exit 2; }
        sha256sum "$source" >> "$output/IMPORTED-SOURCES.sha256"
        sha256sum "$object" >> "$output/PROVIDER-OBJECTS.sha256"
        install -D -m 0644 "$source" "$output/source/$source"
        install -D -m 0644 "$object" "$output/lean-lib/$relative.olean"
        cmp "$source" "$output/source/$source"
        cmp "$object" "$output/lean-lib/$relative.olean"
        while IFS= read -r dependency; do queue+=("$dependency"); done < <(
            awk '/^(public )?import / {for (i=2;i<=NF;i++) if ($i ~ /^(EDSL|tests)[.]/) print $i}' "$source")
    done
    export LEAN_PATH="$output/lean-lib"
    phase=owned_lean
    lean_call shared-capture -R "$output/source" -o "$output/lean-lib/tests/native/RegisterCapture.olean" \
        "$output/source/tests/native/RegisterCapture.lean"
    lean_call validator -R "$output/source" -o "$output/lean-lib/tests/native/CounterDisplacementReplay.olean" \
        "$output/source/tests/native/CounterDisplacementReplay.lean"
    lean_call thin-driver -R "$output/source" -o "$output/lean-lib/Tools/Native/CounterDisplacementReplay.olean" \
        "$output/source/Tools/Native/CounterDisplacementReplay.lean"
    phase=lean_generation
    lean_call generate --run "$output/source/Tools/Native/CounterDisplacementReplay.lean" generate \
        "$output/probes.tsv" "$output/inputs.tsv" "$output/capture.tsv" "$output/opcodes" "$output/generated"
    phase=lean_malformed_controls
    for control in "${native_controls[@]}"; do
        status=0
        lean_call "lean-reject-$control" --run "$output/source/Tools/Native/CounterDisplacementReplay.lean" generate \
            "$output/probes.tsv" "$output/inputs.tsv" "$output/$control.tsv" "$output/opcodes" \
            "$output/rejected-$control" || status=$?
        [[ $status -eq 1 && ! -d $output/rejected-$control ]] || { echo "Invalid Lean rejection: $control"; exit 1; }
    done
    for control in corrupt-output corrupt-flags sub-upper32 cmp-upper32 sub-borrow cmp-borrow \
        sub-auxiliary cmp-auxiliary sub-overflow cmp-overflow \
        lea32-upper32 lea32-carry lea32-auxiliary lea32-overflow lea32-preserved \
        test-low8 test-upper32 test-other-gpr test-rsp test-carry test-parity test-zero \
        test-sign test-overflow test-preserved; do
        grep -F 'independent mathematical result/flags/frame mismatch' "$output/receipts/lean-reject-$control.stderr"
    done
    grep -F 'incomplete matrix' "$output/receipts/lean-reject-missing.stderr"
    grep -F 'duplicate observation' "$output/receipts/lean-reject-duplicate.stderr"
    grep -F 'malformed capture field count' "$output/receipts/lean-reject-malformed.stderr"
    for control in wrong-bytes wrong-length; do
        grep -F 'captured opcode mismatch' "$output/receipts/lean-reject-$control.stderr"
    done
    for control in "${manifest_controls[@]}"; do
        control_dir="$output/manifest-$control"
        status=0
        lean_call "lean-reject-manifest-$control" --run "$output/source/Tools/Native/CounterDisplacementReplay.lean" generate \
            "$control_dir/probes.tsv" "$control_dir/inputs.tsv" "$control_dir/capture.tsv" "$control_dir/opcodes" \
            "$output/rejected-manifest-$control" || status=$?
        [[ $status -eq 1 && ! -d $output/rejected-manifest-$control ]] || {
            echo "Invalid Lean manifest rejection: $control"; exit 1;
        }
    done
    grep -F 'incomplete required probe key inventory' "$output/receipts/lean-reject-manifest-missing-probe.stderr"
    grep -F 'unexpected probe name/metadata/byte key' "$output/receipts/lean-reject-manifest-wrong-address-form.stderr"
    grep -F 'incomplete or changed required input rotation' "$output/receipts/lean-reject-manifest-missing-input.stderr"
    lean_call lean-admit-test-af --run "$output/source/Tools/Native/CounterDisplacementReplay.lean" check \
        "$output/probes.tsv" "$output/inputs.tsv" "$output/test-af-admissible.tsv" "$output/opcodes"
    phase=kernel_replay
    printf 'import EDSL.X86.Sequential.Immediate32\nimport EDSL.X86.Sequential.Address32\nimport EDSL.X86.Sequential.TestImmediate8\nimport tests.native.CounterDisplacementReplay\n' \
        > "$output/generated/CounterDisplacementAudit.lean"
    while IFS= read -r module; do
        [[ -n $module ]] || continue
        lean_call "kernel-$module" -R "$output/generated" -o "$output/lean-lib/$module.olean" "$output/generated/$module.lean"
        printf 'import %s\n' "$module" >> "$output/generated/CounterDisplacementAudit.lean"
    done < "$output/generated/CounterDisplacement.modules"
    cat >> "$output/generated/CounterDisplacementAudit.lean" <<'AUDIT'

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128
#print axioms EDSL.X86.Sequential.execute_subImm32_context
#print axioms EDSL.X86.Sequential.execute_subImm32_signed
#print axioms EDSL.X86.Sequential.execute_subImm32_flags
#print axioms EDSL.X86.Sequential.execute_cmpImm32_context
#print axioms EDSL.X86.Sequential.execute_cmpImm32_flags
#print axioms EDSL.X86.Sequential.execute_lea32_context
#print axioms EDSL.X86.Sequential.execute_lea32_baseDisp8_signed
#print axioms EDSL.X86.Sequential.execute_lea32_sibDisp8_signed
#print axioms EDSL.X86.Sequential.lea32_narrows_lea64
#print axioms EDSL.X86.Sequential.lea32_effects
#print axioms EDSL.OS.CallResources.current_lea32_step
#print axioms EDSL.X86.Sequential.execute_testImm8_context
#print axioms EDSL.X86.Sequential.testImm8_result_toNat
#print axioms EDSL.X86.Sequential.execute_testImm8_admissible_iff
#print axioms EDSL.X86.Sequential.execute_testImm8_choices
#print axioms EDSL.X86.Sequential.testImm8_effects
#print axioms EDSL.X86.Sequential.executeWith_testImm8_agreement
#print axioms EDSL.OS.CallResources.current_testImm8_step
#audit_edsl
AUDIT
    phase=audit
    lean_call audit -R "$output/generated" -o "$output/lean-lib/CounterDisplacementAudit.olean" \
        "$output/generated/CounterDisplacementAudit.lean"
fi
phase=closing_bindings
run owned-stable sha256sum --check "$output/OWNED-SOURCES.sha256"
run tools-stable sha256sum --check "$output/TOOLS.sha256"
run opcodes-stable sha256sum --check "$output/OPCODES.sha256"
if [[ -f $output/FINAL-CODE.sha256 ]]; then run final-code-stable sha256sum --check "$output/FINAL-CODE.sha256"; fi
if [[ $mode != --native-only ]]; then
    run imported-stable sha256sum --check "$output/IMPORTED-SOURCES.sha256"
    run providers-stable sha256sum --check "$output/PROVIDER-OBJECTS.sha256"
    run installed-lean-stable sha256sum --check "$output/INSTALLED-LEAN.sha256"
    if [[ $mode == --replay ]]; then
        run accepted-stable sha256sum --check "$output/receipts/accepted-pins.stdout"
    fi
fi
run provider-sources-after sha256sum "${providers[@]}"
if [[ $mode != --native-only ]]; then
    run provider-sources-equal cmp "$output/receipts/provider-sources-before.stdout" "$output/receipts/provider-sources-after.stdout"
fi
for file in "${providers[@]}"; do
    object=".lake/build/lib/lean/${file%.lean}.olean"
    if [[ -f $object ]]; then sha256sum "$object" >> "$output/PROVIDERS-OBSERVED-AFTER.sha256"; fi
done
run owned-after sha256sum "${owned[@]}" lean-toolchain
run owned-equal cmp "$output/receipts/owned-before.stdout" "$output/receipts/owned-after.stdout"
if [[ $mode == --native-only ]]; then
    printf '%s\nPASS: independent finite native capture/check; %s rejection controls and synthetic AF admissibility. No Lean replay claimed.\n' \
        "$matrix_summary" "$rejection_control_count" > "$output/result.txt"
    printf 'Native capture and mathematical comparison only; not Lean replay.\n' > "$output/NATIVE-READY"
    phase=native_complete
else
    printf '%s\nPASS: production decodeAt/step, both AF choices with exact selected AF; required direct controls; %s rejection controls and synthetic AF admissibility; %s finite kernel row theorems at unchanged budgets; transitive axiom audit.\n' \
        "$matrix_summary" "$rejection_control_count" "$observation_count" > "$output/result.txt"
    printf 'Complete owned finite capture, current production model replay and dependency audit.\n' > "$output/READY"
    phase=complete
fi
complete=1
