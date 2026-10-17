#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail
export LC_ALL=C
native_only=false
case "$#:${1:-}" in
    0:) ;;
    1:--native-only) native_only=true ;;
    *) echo 'usage: verify-comparison64.sh [--native-only]' >&2; exit 2 ;;
esac
if [[ $(uname -sm) != 'Linux x86_64' ]]; then
    echo 'Comparison64 native integration requires Linux x86_64 and the System V ABI' >&2
    exit 2
fi
cd "$(dirname "${BASH_SOURCE[0]}")/.."
source_root=$PWD
# The caller can put evidence on a separate disk; CI retains this default.
archive=${EDSL_COMPARISON64_OUTPUT:-artifacts/comparison64}
mkdir -p "$archive"
archive=$(cd "$archive" && pwd -P)
output=$(mktemp -d "$archive/run.XXXXXXXX")
printf 'Comparison64 evidence: %s\n' "$output"
printf '%s\n' "$native_only" > "$output/native-only.txt"
echo 'NOT RUN: universal Lean proofs, theorem audits and proof-packet grading' > "$output/proof-status.txt"
ulimit -c 0

gcc=${EDSL_GCC:-gcc-13}
clang=${EDSL_CLANG:-clang-18}
functions=(maximum64 minimum64 signed_maximum64)
variants=(gcc clang)
identities=(
    4839f74889f0480f43c7c3 4839fe4889f8480f46c6c3 4839f74889f0480f4dc7c3
    4889f04839f7480f47c7c3 4889f04839f7480f42c7c3 4889f04839f7480f4fc7c3
)
tasks=(maximum64 minimum64 signedMaximum64)
operations=(unsignedMaximum unsignedMinimum signedMaximum)
names=()
binaries=()
record_command() {
    printf '%q ' "$@"
    printf '\n'
}
uname -srmo > "$output/platform.txt"
ld --version > "$output/linker.txt"
objcopy --version > "$output/objcopy.txt"
objdump --version > "$output/objdump.txt"
readelf --version > "$output/readelf.txt"
source_files=(fixtures/comparison64.c fixtures/comparison64-check.c
    fixtures/comparison64-check.S scripts/verify-comparison64.sh)
sha256sum "${source_files[@]}" > "$output/source-SHA256SUMS"
for file in "${source_files[@]}"; do
    install -D -m 0644 "$file" "$output/source/$file"
done
(cd "$output/source" && sha256sum -c "$output/source-SHA256SUMS") > "$output/source-copy-check.txt"
printf 'variant\tfunction\ttask\toperation\tbytes\n' > "$output/selections.tsv"
prepare() {
    local compiler=$1 variant=$2 variant_index=$3
    local directory="$output/$variant"
    mkdir -p "$directory"
    "$compiler" --version > "$directory/compiler.txt"
    command -v "$compiler" > "$directory/compiler-path.txt"
    local compile=(-std=gnu2x -Os -Wall -Wextra -Werror -fno-lto
        -fcf-protection=none -ffunction-sections -c fixtures/comparison64.c
        -o "$directory/functions.o")
    record_command "$compiler" "${compile[@]}" > "$directory/compile-arguments.txt"
    "$compiler" "${compile[@]}"
    local i function final expected actual
    for i in "${!functions[@]}"; do
        function=${functions[$i]}
        final="$directory/$function"
        mkdir -p "$final"
        local link=(-m elf_x86_64 --build-id=none --gc-sections -z noexecstack
            -e "$function" -Ttext=0x401000 -o "$final/function.elf" "$directory/functions.o")
        record_command ld "${link[@]}" > "$final/link-arguments.txt"
        ld "${link[@]}"
        record_command objcopy --dump-section ".text=$final/function.bin" "$final/function.elf" \
            > "$final/extraction-arguments.txt"
        objcopy --dump-section ".text=$final/function.bin" "$final/function.elf"
        readelf -h -l -S -s -r -W "$final/function.elf" > "$final/elf.txt"
        readelf -rW "$final/function.elf" > "$final/relocations.txt"
        if [[ $(< "$final/relocations.txt") != *'There are no relocations in this file.'* ]]; then
            echo "Relocated final comparison ELF is outside this profile: $variant/$function" >&2
            exit 3
        fi
        objdump -d -Mintel "$final/function.elf" > "$final/disassembly.txt"
        wc -c < "$final/function.bin" > "$final/span.txt"
        expected=${identities[$((variant_index * 3 + i))]}
        actual=$(od -An -tx1 -v "$final/function.bin" | tr -d ' \n')
        printf '%s\n' "$expected" > "$final/expected.txt"
        printf '%s\n' "$actual" > "$final/actual.txt"
        # A transparent exact-profile gate, separate from the native oracle.
        # Never silently accept a different compiler shape or a partial .text.
        if [[ "$actual" != "$expected" ]]; then
            echo "Unsupported final comparison bytes: $variant/$function: $actual" >&2
            exit 3
        fi
        printf '%s\t%s\t%s\t%s\t%s\n' "$variant" "$function" "${tasks[$i]}" \
            "${operations[$i]}" "$actual" >> "$output/selections.tsv"
        names+=("${variant}_${function}")
        binaries+=("$final/function.bin")
    done
}
prepare "$gcc" "${variants[0]}" 0
prepare "$clang" "${variants[1]}" 1

# Assemble .incbin paths relative to this fresh run directory. This embeds the
# actual complete extracted final sections in executable, relocation-free slots.
observer=(-std=gnu2x -O2 -Wall -Wextra -Werror -fno-lto -fcf-protection=none
    -fno-pie -no-pie '-Wl,--build-id=none,-z,noexecstack'
    "$source_root/fixtures/comparison64-check.c" "$source_root/fixtures/comparison64-check.S"
    -o "$output/native-check.elf")
{
    printf 'cd %q\n' "$output"
    record_command "$gcc" "${observer[@]}"
} > "$output/observer-arguments.txt"
(cd "$output" && "$gcc" "${observer[@]}")
readelf -h -l -S -s -r -W "$output/native-check.elf" > "$output/observer-elf.txt"
objdump -d -Mintel -j .text -j .edsl_comparison64 "$output/native-check.elf" \
    > "$output/observer-disassembly.txt"
record_command "$output/native-check.elf" "${binaries[@]}" > "$output/native-arguments.txt"
status=0
timeout 60 "$output/native-check.elf" "${binaries[@]}" \
    > "$output/native-results.txt" 2> "$output/native-errors.txt" || status=$?
printf '%s\n' "$status" > "$output/native-status.txt"
if [[ $status -ne 0 ]]; then
    cat "$output/native-errors.txt" >&2
    echo "Comparison64 native run did not pass: status $status (signals/timeouts are inconclusive)" >&2
    exit 1
fi
cat "$output/native-results.txt"

# All six files must match their executed slots before even the first probe.
# Check same-length internal alteration, truncation, extension and a substituted
# final compiler output. Synthetic semantic defects above are executed separately.
expect_extraction_rejection() {
    local index=$1 label=$2 changed=$3
    local directory="$output/extraction-rejections/${names[$index]}/$label"
    mkdir -p "$directory"
    local inputs=("${binaries[@]}")
    inputs[index]=$changed
    record_command "$output/native-check.elf" "${inputs[@]}" > "$directory/arguments.txt"
    local rejection_status=0
    timeout 60 "$output/native-check.elf" "${inputs[@]}" \
        > "$directory/stdout.txt" 2> "$directory/stderr.txt" || rejection_status=$?
    printf '%s\n' "$rejection_status" > "$directory/status.txt"
    if [[ $rejection_status -ne 2 || -s "$directory/stdout.txt" ||
        $(< "$directory/stderr.txt") != "Final ELF section extraction differs from executed bytes: ${names[$index]}" ]]; then
        echo "Expected pre-probe byte identity rejection 2: ${names[$index]}/$label, got $rejection_status" >&2
        exit 1
    fi
}
for index in "${!binaries[@]}"; do
    directory="$output/extraction-rejections/${names[$index]}"
    mkdir -p "$directory"
    cp "${binaries[$index]}" "$directory/altered.bin"
    printf '\000' | dd of="$directory/altered.bin" bs=1 seek=8 count=1 conv=notrunc status=none
    expect_extraction_rejection "$index" altered "$directory/altered.bin"
    head -c 10 "${binaries[$index]}" > "$directory/truncated.bin"
    expect_extraction_rejection "$index" truncated "$directory/truncated.bin"
    cp "${binaries[$index]}" "$directory/extended.bin"
    printf '\220' >> "$directory/extended.bin"
    expect_extraction_rejection "$index" extended "$directory/extended.bin"
    # Different operation from the same compiler, still exactly 11 final bytes.
    other_index=$((index / 3 * 3 + (index + 1) % 3))
    expect_extraction_rejection "$index" substituted "${binaries[$other_index]}"
done
echo 'PASS 24 altered/truncated/extended/substituted extraction rejections before native probing' \
    > "$output/extraction-results.txt"
cat "$output/extraction-results.txt"

cat > "$output/native-scope.txt" <<'SCOPE'
Owned Linux x86-64/System V whole-call evidence for GNU23 maximum64, minimum64
and signed_maximum64, separately compiled by the recorded GCC and Clang. Fixture
arguments are exactly -std=gnu2x -Os -Wall -Wextra -Werror -fno-lto
-fcf-protection=none -ffunction-sections. Each function is separately final-linked
with ld -m elf_x86_64 --build-id=none --gc-sections -z noexecstack -e FUNCTION
-Ttext=0x401000. The entire final .text must be the selected exact 11 bytes, and
the complete function ELF must have no relocations. This deliberately limited
identity profile rejects compiler drift; rejection establishes no defect.
Compiler versions, complete compile/link/extraction/observer/run commands, ELF
metadata, disassembly, source snapshots and SHA256 sums are recorded here.

The executable observer embeds the actual whole extractions using .incbin in
six executable slots. Every supplied file must exactly equal its executed slot
before any probe or positive output. Internal alteration (same length, offset
8), truncation, extension and substitution with another operation are rejected
for each of the six slots: 24 pre-probe rejections, status 2 and empty stdout.
No instruction decoder or opcode-derived condition occurs in the C oracle.
The independent postcondition requires full64 RAX to be an original argument
and bound both arguments in the requested unsigned or signed mathematical order.
Signed operands/results use their actual int64_t object representation, with no
subtraction/overflow computation in the oracle. Native execution includes RET;
the function ELF itself is a bare entry-window artifact, not a process to launch.

There are 188416 successful whole calls per compiler/function, 1130496 total.
Each runs all 32x32 boundary-value pairs and six pairs for each of 64 bit
boundaries under all 128 CF/PF/AF/ZF/SF/OF/ID profiles. A further 8192 deterministic
full64 operand pairs per function include equality every sixteenth pair. Inputs
cover zero, small values, 32-bit truncation boundaries, distinct high halves,
UINT64_MAX, INT64_MIN/MAX, both argument orders, equality and subtraction-overflow
boundary pairs. The observer requires the requested seven user flag bits to
actually be installed. DF is clear at every SysV call. It checks all six actual
callee-saved GPRs (RBX/RBP/R12..R15), the real caller RSP before/after CALL/RET,
and equality of all captured nonarithmetic RFLAGS. Arithmetic flags may change.
ID varies both ways; privileged flags are only their effective user-mode values.
RSP is a real aligned host stack pointer; no arbitrary modeled RSP is installed.
Capture uses only MOVs before saving flags and restores the host stack/flags
before returning to C. The observer/recovery globals are single-threaded.

Eighteen separate safe owned assembly mutants must be rejected for their
specified reason: wrong direction and signedness for all three operations,
wrong operand, signed-overflow condition, 32-bit narrowing, clobber of each of the six saved GPRs, a RET $8
stack imbalance, setting DF and changing ID. Witnesses are printed. These test
the oracle/capture; they are not security findings or compiler defects. Signals,
timeouts or unexpected failure categories fail the run and are inconclusive.

This is finite native evidence, not a universal Lean proof or proof-packet
acceptance, C/source preservation, physical CPU/kernel validation, data-memory
frame proof, operand memory-access trace, timing, speculation, concurrent
visibility, atomicity, whole-OS safety or global optimum. Normal stable user
memory, the recorded Linux CPU/kernel/System V environment, disabled CET and
no asynchronous interference with capture are assumed. The code profile is
position independent; the executable embedded copies have different addresses
from the original 0x401000 link address. A separate universal model theorem and
its environmental/ownership contracts must be checked by the root integration.
SCOPE

write_hashes() {
    (cd "$output" && find . -type f ! -name SHA256SUMS -print0 | sort -z | xargs -0 sha256sum) \
        > "$output/SHA256SUMS"
}
if [[ $native_only == true ]]; then
    echo 'PASS: finite native checks and extraction rejections; proof checks NOT RUN' > "$output/result.txt"
    write_hashes
    echo 'Comparison64 exact final compiler bytes and finite native contracts passed; proof checks not run'
    exit 0
fi
# Root owns these proof/registration sources. Native-only mode never needs
# them. Full mode uses the concrete wrapper names supplied by that integration.
required=(tests/fixtures/Comparison64.lean tests/fixtures/Comparison64/Machine.lean
    tests/fixtures/Comparison64/Raw.lean tests/Comparison64.lean tests/GradingComparison64.lean
    tests/GradingIsolation.lean EDSL/Comparison64/Contract.lean EDSL/Comparison64/Resources.lean
    EDSL/Comparison64/Domain.lean)
for file in "${required[@]}"; do
    if [[ ! -f $file ]]; then
        printf 'NOT RUN: root-owned full verification source is missing: %s\n' "$file" \
            > "$output/proof-status.txt"
        echo 'Native checks passed; full verification awaits root source sync (exit 2)' > "$output/result.txt"
        write_hashes
        cat "$output/proof-status.txt" >&2
        exit 2
    fi
done

# Retain an exact source snapshot for review. Build in the actual checkout so
# Lake can validate and reuse its cached outputs; fresh kernel replay below
# checks the stored proof terms independently of Lake's build traces.
proof_project="$source_root"
proof_snapshot="$output/proof-source"
mkdir -p "$proof_snapshot" "$output/proof-logs"
proof_sources=(lean-toolchain lake-manifest.json ./*.lean)
while IFS= read -r -d '' file; do
    proof_sources+=("$file")
done < <(rg --files --null -g '*.lean' EDSL tests)
sha256sum "${proof_sources[@]}" > "$output/proof-source-SHA256SUMS"
for file in "${proof_sources[@]}"; do
    install -D -m 0644 "$file" "$proof_snapshot/$file"
done
(cd "$proof_snapshot" && sha256sum -c "$output/proof-source-SHA256SUMS") \
    > "$output/proof-source-copy-check.txt"
echo 'INCOMPLETE: full proof checks started; only the final PASS marks success' > "$output/proof-status.txt"
lean=(env LEAN_NUM_THREADS=1 flock /tmp/edsl-lean-build.lock lake)
expect_full_status() {
    local expected_status=$1 label=$2
    shift 2
    {
        printf 'cd %q\n' "$proof_project"
        record_command "$@"
    } > "$output/$label-arguments.txt"
    local actual_status=0
    (cd "$proof_project" && "$@") > "$output/$label.txt" 2>&1 || actual_status=$?
    printf '%s\n' "$actual_status" > "$output/$label-status.txt"
    if [[ $actual_status -ne $expected_status ]]; then
        tail -n 60 "$output/$label.txt" >&2
        printf 'INCOMPLETE: %s expected status %s, got %s; full verification has not passed\n' \
            "$label" "$expected_status" "$actual_status" > "$output/proof-status.txt"
        write_hashes
        cat "$output/proof-status.txt" >&2
        exit 1
    fi
}
expect_full_status 0 proof-logs/build "${lean[@]}" build \
    edsl-grade edsl-proof-export tests.fixtures.Comparison64
expect_full_status 0 proof-logs/contract-audit "${lean[@]}" env lean \
    -DwarningAsError=true tests/Comparison64.lean
expect_full_status 0 proof-logs/registration-audit "${lean[@]}" env lean \
    -DwarningAsError=true tests/GradingComparison64.lean
expect_full_status 0 proof-logs/fresh-kernel "${lean[@]}" env leanchecker \
    --fresh tests.fixtures.Comparison64
claims=(gccMaximum gccMinimum gccSignedMaximum clangMaximum clangMinimum clangSignedMaximum)
module=tests.fixtures.Comparison64
exporter=("${lean[@]}" env "$proof_project/.lake/build/bin/edsl-proof-export")
grader=("${lean[@]}" env "$proof_project/.lake/build/bin/edsl-grade")
for index in "${!binaries[@]}"; do
    variant=${variants[$((index / 3))]}
    function=${functions[$((index % 3))]}
    task=${tasks[$((index % 3))]}
    theorem="EDSL.Comparison64.Client.${claims[$index]}"
    proof_label="$variant/$function/proof"
    mkdir -p "$output/$proof_label"
    expect_full_status 0 "$proof_label/isolation" "${lean[@]}" env lean -DwarningAsError=true \
        --run tests/GradingIsolation.lean "$module" "$theorem"
    span=$(< "$output/$variant/$function/span.txt")
    for mode in reference body; do
        options=()
        if [[ $mode == body ]]; then options=(--body); fi
        packet="$output/$proof_label/$mode.json"
        expect_full_status 0 "$proof_label/export-$mode" "${exporter[@]}" \
            "$module" "$theorem" "$packet" "${options[@]}"
        expect_full_status 0 "$proof_label/raw-$mode" "${grader[@]}" \
            "$task" "${binaries[$index]}" "$packet"
        expect_full_status 0 "$proof_label/elf-$mode" "${grader[@]}" \
            --elf "$span" "$task" "$output/$variant/$function/function.elf" "$packet"
    done
    wrong_task=${tasks[$(((index + 1) % 3))]}
    expect_full_status 5 "$proof_label/changed-task" "${grader[@]}" \
        "$wrong_task" "${binaries[$index]}" "$output/$proof_label/reference.json"
    expect_full_status 5 "$proof_label/changed-span" "${grader[@]}" \
        --elf "$((span - 1))" "$task" "$output/$variant/$function/function.elf" \
        "$output/$proof_label/body.json"
    expect_full_status 5 "$proof_label/changed-bytes" "${grader[@]}" \
        "$task" "$output/extraction-rejections/${names[$index]}/altered.bin" \
        "$output/$proof_label/body.json"
    # The other compiler has a valid implementation of the same task; a packet
    # for this compiler's different bytes must still reject the substituted one.
    other_index=$(((index + 3) % 6))
    expect_full_status 5 "$proof_label/changed-compiler-bytes" "${grader[@]}" \
        "$task" "${binaries[$other_index]}" "$output/$proof_label/reference.json"
done
cat > "$output/proof-scope.txt" <<'SCOPE'
Full verification records a SHA-checked snapshot of the Lean sources. It builds
the checkout through Lake, which invalidates changed inputs and can reuse cached
outputs; stored proof terms are replayed through a fresh kernel environment.
Lean is pinned by lean-toolchain, uses the caller's PATH, and is serialized with
LEAN_NUM_THREADS=1 and flock /tmp/edsl-lean-build.lock. Reports, proof packets and
source snapshots are archived; reproducible Lake build products stay in cache.
The client module tests.fixtures.Comparison64 supplies the concrete wrappers
EDSL.Comparison64.Client.gccMaximum/gccMinimum/gccSignedMaximum and
EDSL.Comparison64.Client.clangMaximum/clangMinimum/clangSignedMaximum.
Each claims its complete final 11 bytes under maximum64, minimum64 or
signedMaximum64. The independent registrations use mathematical order and
current ownership/call-resource contracts; instruction accounting is separate.

The flow requires contract and registration regression checks/axiom audits,
fresh stored-proof kernel replay, and trusted-snapshot isolation of all six
client wrappers. Reference and body packets for all six implementations must
grade both the raw whole .text and the selected complete restricted ELF span:
12 exports and 24 successful raw/ELF grading calls. Every implementation also
requires status-5 rejection of a changed task, shortened span, internally
altered bytes and the other compiler's different bytes for the same task:
24 packet rejections. These rejections demonstrate artifact/task binding,
not a defect or a semantic refutation of the changed artifact. Actual semantic
counterexamples are the separate root-supplied kernel-checked regressions.

A successful full script run establishes the recorded model claims and finite
native checks under their stated environmental assumptions. It does not prove
C/source preservation, universal physical CPU/kernel conformance, timing,
speculation, concurrent visibility, whole-OS safety or global optimum.
Native results and their practical limitations are described in native-scope.txt.
SCOPE
echo 'PASS: universal client/model audits, fresh kernel replay, isolation and raw/ELF proof-packet checks' \
    > "$output/proof-status.txt"
echo 'PASS: full model/proof integration and separate finite native evidence' > "$output/result.txt"
write_hashes
echo 'Comparison64 client proofs, raw/ELF grading and separate finite native contracts passed'
