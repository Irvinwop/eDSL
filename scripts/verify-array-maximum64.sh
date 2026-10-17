#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail
export LC_ALL=C
native_only=false
case "$#:${1:-}" in
    0:) ;;
    1:--native-only) native_only=true ;;
    *) echo 'usage: verify-array-maximum64.sh [--native-only]' >&2; exit 2 ;;
esac
if [[ $(uname -sm) != 'Linux x86_64' ]]; then
    echo 'ArrayMaximum64 native evidence requires Linux x86_64/System V' >&2
    exit 2
fi
cd "$(dirname "${BASH_SOURCE[0]}")/.."
source_root=$PWD
archive=${EDSL_ARRAY_MAXIMUM64_OUTPUT:-artifacts/array-maximum64}
mkdir -p "$archive"
archive=$(cd "$archive" && pwd -P)
output=$(mktemp -d "$archive/run.XXXXXXXX")
printf 'ArrayMaximum64 evidence: %s\n' "$output"
printf '%s\n' "$native_only" > "$output/native-only.txt"
echo 'NOTRUN: universal Lean proofs, theorem audits and proof-packet grading' \
    > "$output/proof-status.txt"
echo 'INCOMPLETE: native checks have not finished' > "$output/result.txt"
ulimit -c 0

record_command() { printf '%q ' "$@"; printf '\n'; }
# EXIT calls these functions indirectly; ShellCheck cannot follow that edge.
# shellcheck disable=SC2317
write_hashes() {
    (cd "$output" && find . -type f ! -name SHA256SUMS ! -name manifest-check.txt -print0 |
        sort -z | xargs -0 sha256sum) > "$output/SHA256SUMS" || return 1
    (cd "$output" && sha256sum -c SHA256SUMS) > "$output/manifest-check.txt"
}
# shellcheck disable=SC2317
finish() {
    local status=$?
    trap - EXIT
    printf '%s\n' "$status" > "$output/runner-status.txt"
    if ! write_hashes; then
        echo 'INCOMPLETE: evidence manifest could not be written/checked' > "$output/result.txt"
        exit 1
    fi
    exit "$status"
}
trap 'finish' EXIT

gcc=${EDSL_GCC:-gcc-13}
clang=${EDSL_CLANG:-clang-18}
variants=(gcc clang)
names=(gcc_maximum64_array clang_maximum64_array)
identities=(
    31d231c04839f27410488b0cd74839c8480f42c148ffc2ebebc3
    4885f6741831c931c0488b14cf4839c2480f47c248ffc14839ce75edc331c0c3
)
binaries=()
{
    printf 'cd %q\n' "$source_root"
    printf 'PATH=%q\nEDSL_GCC=%q\nEDSL_CLANG=%q\n' "$PATH" "$gcc" "$clang"
    printf 'EDSL_ARRAY_MAXIMUM64_OUTPUT=%q\n' "$archive"
    record_command bash "$source_root/scripts/verify-array-maximum64.sh" "$@"
} > "$output/runner-arguments.txt"
uname -srmo > "$output/platform.txt"
getconf PAGESIZE > "$output/page-size.txt"
getconf GNU_LIBC_VERSION > "$output/libc-version.txt"
if command -v lscpu > /dev/null; then lscpu > "$output/cpu.txt"; fi
for tool in ld objcopy objdump readelf timeout sha256sum bash; do
    command -v "$tool" > "$output/$tool-path.txt"
    "$tool" --version > "$output/$tool-version.txt"
done
source_files=(fixtures/array-maximum64.c fixtures/array-maximum64-check.c
    fixtures/array-maximum64-check.S scripts/verify-array-maximum64.sh)
sha256sum "${source_files[@]}" > "$output/source-SHA256SUMS"
for file in "${source_files[@]}"; do
    install -D -m 0644 "$file" "$output/source/$file"
done
(cd "$output/source" && sha256sum -c "$output/source-SHA256SUMS") > "$output/source-copy-check.txt"
printf 'variant\tfunction\tcomplete-text-bytes\n' > "$output/selections.tsv"
prepare() {
    local compiler=$1 variant=$2 expected=$3
    local directory="$output/$variant"
    mkdir -p "$directory"
    command -v "$compiler" > "$directory/compiler-path.txt"
    "$compiler" --version > "$directory/compiler-version.txt"
    local compile=(-std=gnu2x -Os -Wall -Wextra -Werror -fno-lto -fcf-protection=none
        -ffunction-sections -c "$output/source/fixtures/array-maximum64.c" -o "$directory/function.o")
    record_command "$compiler" "${compile[@]}" > "$directory/compile-arguments.txt"
    "$compiler" "${compile[@]}" > "$directory/compiler-output.txt" 2>&1
    readelf -h -l -S -s -r -W "$directory/function.o" > "$directory/object-elf.txt"
    objdump -dr -Mintel "$directory/function.o" > "$directory/object-disassembly.txt"
    local link=(-m elf_x86_64 --build-id=none --gc-sections -z noexecstack
        -e maximum64_array -Ttext=0x401000 -o "$directory/function.elf" "$directory/function.o")
    record_command ld "${link[@]}" > "$directory/link-arguments.txt"
    ld "${link[@]}" > "$directory/link-output.txt" 2>&1
    record_command objcopy --dump-section ".text=$directory/function.bin" "$directory/function.elf" \
        > "$directory/extraction-arguments.txt"
    objcopy --dump-section ".text=$directory/function.bin" "$directory/function.elf"
    readelf -h -l -S -s -r -n -W "$directory/function.elf" > "$directory/final-elf.txt"
    readelf -rW "$directory/function.elf" > "$directory/final-relocations.txt"
    if [[ $(< "$directory/final-relocations.txt") != *'There are no relocations in this file.'* ]]; then
        echo "Relocated final array-maximum ELF is outside this profile: $variant" >&2
        exit 3
    fi
    objdump -d -Mintel "$directory/function.elf" > "$directory/final-disassembly.txt"
    wc -c < "$directory/function.bin" > "$directory/text-length.txt"
    local actual
    actual=$(od -An -tx1 -v "$directory/function.bin" | tr -d ' \n')
    printf '%s\n' "$expected" > "$directory/expected-text-hex.txt"
    printf '%s\n' "$actual" > "$directory/text-hex.txt"
    # Complete final .text identity, never a prefix/window or equivalent source
    # assumption. Both profiles must pass before the observer is built or run.
    if [[ "$actual" != "$expected" ]]; then
        echo "Unsupported final array-maximum bytes: $variant: $actual" >&2
        exit 3
    fi
    echo 'PASS complete final .text identity; no final ELF relocations' > "$directory/identity-status.txt"
    printf '%s\tmaximum64_array\t%s\n' "$variant" "$actual" >> "$output/selections.tsv"
    binaries+=("$directory/function.bin")
}
prepare "$gcc" "${variants[0]}" "${identities[0]}"
prepare "$clang" "${variants[1]}" "${identities[1]}"

# Syntax checks are compiler checks, separate from the actual native contract
# checks below. No Lean project, build or proof replay is performed here.
for compiler in "$gcc" "$clang"; do
    variant=gcc
    if [[ $compiler == "$clang" ]]; then variant=clang; fi
    syntax=(-std=gnu2x -Wall -Wextra -Werror -fsyntax-only
        "$output/source/fixtures/array-maximum64.c" "$output/source/fixtures/array-maximum64-check.c")
    record_command "$compiler" "${syntax[@]}" > "$output/$variant/syntax-arguments.txt"
    "$compiler" "${syntax[@]}" > "$output/$variant/syntax-results.txt" 2>&1
done
observer=(-std=gnu2x -O2 -Wall -Wextra -Werror -fno-lto -fcf-protection=none
    -fno-pie -no-pie '-Wl,--build-id=none,-z,noexecstack'
    "$output/source/fixtures/array-maximum64-check.c" "$output/source/fixtures/array-maximum64-check.S"
    -o "$output/native-check.elf")
{
    printf 'cd %q\n' "$output"
    record_command "$gcc" "${observer[@]}"
} > "$output/observer-arguments.txt"
# .incbin resolves only these two already-gated, actual final extractions.
(cd "$output" && "$gcc" "${observer[@]}") > "$output/observer-build.txt" 2>&1
readelf -h -l -S -s -r -n -W "$output/native-check.elf" > "$output/observer-elf.txt"
objdump -d -Mintel -j .text -j .edsl_array_maximum64 "$output/native-check.elf" \
    > "$output/observer-disassembly.txt"

expect_extraction_rejection() {
    local index=$1 label=$2 changed=$3
    local directory="$output/extraction-rejections/${names[$index]}/$label"
    mkdir -p "$directory"
    local inputs=("${binaries[@]}")
    inputs[index]=$changed
    local run=(timeout --kill-after=2 60 "$output/native-check.elf" "${inputs[@]}")
    record_command "${run[@]}" > "$directory/arguments.txt"
    local status=0
    "${run[@]}" > "$directory/stdout.txt" 2> "$directory/stderr.txt" || status=$?
    printf '%s\n' "$status" > "$directory/status.txt"
    if [[ $status -ne 2 || -s "$directory/stdout.txt" ||
        $(< "$directory/stderr.txt") != "Final ELF section extraction differs from executed bytes: ${names[$index]}" ]]; then
        echo "Expected pre-probe extraction rejection 2: ${names[$index]}/$label, got $status" >&2
        exit 1
    fi
}
for index in "${!binaries[@]}"; do
    directory="$output/extraction-rejections/${names[$index]}"
    mkdir -p "$directory"
    cp "${binaries[$index]}" "$directory/altered.bin"
    printf '\000' | dd of="$directory/altered.bin" bs=1 seek=12 count=1 conv=notrunc status=none
    expect_extraction_rejection "$index" altered "$directory/altered.bin"
    size=$(wc -c < "${binaries[$index]}")
    head -c "$((size - 1))" "${binaries[$index]}" > "$directory/truncated.bin"
    expect_extraction_rejection "$index" truncated "$directory/truncated.bin"
    cp "${binaries[$index]}" "$directory/extended.bin"
    printf '\220' >> "$directory/extended.bin"
    expect_extraction_rejection "$index" extended "$directory/extended.bin"
    expect_extraction_rejection "$index" substituted "${binaries[$((1 - index))]}"
done
echo 'PASS 8 altered/truncated/extended/substituted extraction rejections: status 2, empty stdout, no probes' \
    > "$output/extraction-results.txt"
cat "$output/extraction-results.txt"
run=(timeout --kill-after=2 60 "$output/native-check.elf" "${binaries[@]}")
record_command "${run[@]}" > "$output/native-arguments.txt"
status=0
"${run[@]}" > "$output/native-results.txt" 2> "$output/native-errors.txt" || status=$?
printf '%s\n' "$status" > "$output/native-status.txt"
if [[ $status -ne 0 ]]; then
    cat "$output/native-errors.txt" >&2
    echo 'INCOMPLETE: native checks failed; signals/timeouts/environment failures are inconclusive' \
        > "$output/result.txt"
    printf 'ArrayMaximum64 native checks did not pass: status %s (signals/timeouts are inconclusive)\n' \
        "$status" >&2
    exit 1
fi
cat "$output/native-results.txt"
cat > "$output/native-scope.txt" <<'SCOPE'
Finite owned Linux x86-64/System V evidence for actual full64 maximum64_array
loops compiled by the recorded GCC and Clang. Sources, resolved tool paths,
versions, compile/link/extraction/observer/run arguments, ELF metadata,
disassemblies and source/artifact SHA256 manifests are retained. The fixture C
is verbatim from the cold array-max-probe-20261017/maximum64-array.c. Compilation
uses GNU23 spelling -std=gnu2x -Os -Wall -Wextra -Werror -fno-lto
-fcf-protection=none -ffunction-sections. Each object is final-linked with ld
-m elf_x86_64 --build-id=none --gc-sections -z noexecstack -e maximum64_array
-Ttext=0x401000. The complete final .text must match the selected 26-byte GCC or
32-byte Clang profile and the final ELF must contain no relocations. Profile
rejection means unsupported/drift, not a compiler defect.

Only actual whole extracted .text sections are embedded with .incbin. They are
position independent and execute at observer addresses distinct from 0x401000.
The bare function ELF is not launched as a process. Before any probe or stdout,
the observer requires BOTH complete extraction inputs to match their embedded
slots AND fixed compiler profiles. It never maps/executes supplied files.
Both slots must reject internal alteration (offset 12), truncation, extension
and substitution with the other compiler: eight status-2 rejections with exact
diagnostics and empty stdout. These identity tests do not execute changed code.

The independent unsigned result contract is membership in the original input
AND an upper bound for every original element, with zero for the empty array.
There is no second maximum computation or opcode-derived semantic oracle.
Snapshots cover every accessible byte of each owned input page, including
padding, and are compared after every call. Original values in the snapshots
also define result checks, so a data-writing mutant cannot change the oracle.
Empty calls allocate/dereference no input: raw RDI bits are null, an unused
PROT_NONE base or 0x0200000000000000 (noncanonical at both 48 and 57 bits).

Selected deterministic vectors run all 128 combinations of CF/PF/AF/ZF/SF/OF
and ID. Singleton and ordered pair matrices cover 32 unsigned edges, equality,
upper-32/high-sign bits, duplicates and UINT64_MAX. Six pairs for every bit
boundary and multiple lengths through 511 cover maxima first/middle/last.
Read-only aligned inputs end at a guard page; unaligned inputs end one byte
before it. One writable padded positive also checks the memory frame. Another
1024 deterministic random arrays per compiler vary lengths, duplicate values,
alignment and flag profiles. All profiles reuse the same allocation/snapshot.
Actual case/call totals, including negative probes, are in native-results.txt.

The actual CALL/RET observer checks RBX/RBP/R12..R15, RDI/RSI/R8..R11, real
aligned host RSP before/after CALL and all effective nonarithmetic RFLAGS.
Initial RAX and saved/extra GPRs vary; RCX/RDX are also seeded. Requested seven
flag bits must actually install; DF is clear at the SysV call. Privileged and
other flags use their captured effective values, not invented input values.
Only MOV captures precede PUSHFQ. RIP-relative single-thread recovery restores
the host stack, six saved GPRs and host flags/DF before returning to C, even for
the owned RET $8, DF and ID mutants. No arbitrary modeled RSP is installed.

Twenty-three owned safe mutants require actual counterexamples with exactly
their specified failure category: wrong direction, signedness, narrowing,
skip-last, zero, membership-only and nonzero empty result, changed input bytes,
each saved/argument/extra GPR, RET $8, DF and ID. Nonempty mutant inputs are
writable, owned and padded; no intentional overread, invalid access, signal or
timeout is accepted as a counterexample. Witnesses/reasons are recorded.
Signals, timeouts, unsupported hosts and environmental failures fail the run
inconclusively; they do not establish a security finding or compiler defect.

Assume ordinary coherent stable user memory, the recorded Linux kernel/CPU/
libc/System V execution environment, disabled CET enforcement, a real usable
host stack, and no concurrent/asynchronous interference with observer globals
or capture. These finite executions do not prove universal Lean/model claims,
source/IR preservation, whole-OS/physical CPU correctness, universal memory
frames/access traces, synchronization, timing, speculation or optimality.
Universal proofs, resource/domain/registry integration and proof-packet checks
are separate full-mode gates. The native phase needs no Lean build. Full mode
adds a Lean source snapshot and reuses the actual checkout's Lake cache.
SCOPE
if [[ $native_only == true ]]; then
    echo 'PASS: finite native checks and extraction rejections; universal Lean NOTRUN' > "$output/result.txt"
    echo 'ArrayMaximum64 exact final compiler sections and finite native checks passed; universal Lean NOTRUN'
    exit 0
fi
# Build in the actual checkout so Lake validates changed inputs and reuses its
# cache. The snapshot is evidence; fresh kernel replay checks stored terms.
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
        cat "$output/proof-status.txt" >&2
        exit 1
    fi
}
expect_full_status 0 proof-logs/build "${lean[@]}" build \
    edsl-grade edsl-proof-export tests.fixtures.ArrayMaximum64
expect_full_status 0 proof-logs/resource-audit "${lean[@]}" env lean \
    -DwarningAsError=true tests/ArrayResources64.lean
expect_full_status 0 proof-logs/contract-registration-audit "${lean[@]}" env lean \
    -DwarningAsError=true tests/ArrayMaximum64.lean
expect_full_status 0 proof-logs/fresh-kernel "${lean[@]}" env leanchecker \
    --fresh tests.fixtures.ArrayMaximum64
modules=(tests.fixtures.ArrayMaximum64.GCCExport tests.fixtures.ArrayMaximum64.ClangExport)
claims=(EDSL.ArrayMaximum64.Client.gcc EDSL.ArrayMaximum64.Client.clang)
exporter=("${lean[@]}" env "$proof_project/.lake/build/bin/edsl-proof-export")
grader=("${lean[@]}" env "$proof_project/.lake/build/bin/edsl-grade")
for index in "${!binaries[@]}"; do
    variant=${variants[$index]}
    module=${modules[$index]}
    theorem=${claims[$index]}
    proof_label="$variant/proof"
    mkdir -p "$output/$proof_label"
    expect_full_status 0 "$proof_label/isolation" "${lean[@]}" env lean -DwarningAsError=true \
        --run tests/GradingIsolation.lean "$module" "$theorem"
    span=$(< "$output/$variant/text-length.txt")
    for mode in reference body; do
        options=()
        if [[ $mode == body ]]; then options=(--body); fi
        packet="$output/$proof_label/$mode.json"
        expect_full_status 0 "$proof_label/export-$mode" "${exporter[@]}" \
            "$module" "$theorem" "$packet" "${options[@]}"
        expect_full_status 0 "$proof_label/raw-$mode" "${grader[@]}" \
            arrayMaximum64 "${binaries[$index]}" "$packet"
        expect_full_status 0 "$proof_label/elf-$mode" "${grader[@]}" \
            --elf "$span" arrayMaximum64 "$output/$variant/function.elf" "$packet"
    done
    expect_full_status 5 "$proof_label/changed-task" "${grader[@]}" \
        maximum64 "${binaries[$index]}" "$output/$proof_label/reference.json"
    expect_full_status 5 "$proof_label/changed-span" "${grader[@]}" \
        --elf "$((span - 1))" arrayMaximum64 "$output/$variant/function.elf" \
        "$output/$proof_label/body.json"
    expect_full_status 5 "$proof_label/changed-bytes" "${grader[@]}" \
        arrayMaximum64 "$output/extraction-rejections/${names[$index]}/altered.bin" \
        "$output/$proof_label/body.json"
    other_index=$((1 - index))
    expect_full_status 5 "$proof_label/changed-compiler-bytes" "${grader[@]}" \
        arrayMaximum64 "${binaries[$other_index]}" "$output/$proof_label/reference.json"
done
# Detect source changes during the run rather than attributing cached outputs
# or proof-packet results to a snapshot of different source files.
sha256sum -c "$output/proof-source-SHA256SUMS" > "$output/proof-source-final-check.txt"
cat > "$output/proof-scope.txt" <<'SCOPE'
Full mode records a SHA-checked snapshot of the Lean sources and verifies that
the originals remain unchanged during the run. Lake builds in the checkout,
validating its input traces while reusing cached outputs. The pinned toolchain
replays stored proofs in a fresh kernel environment. Builds use LEAN_NUM_THREADS=1
and flock /tmp/edsl-lean-build.lock; cache hits never skip the proof gates.

The independent arrayMaximum64 task requires full64 unsigned natural maximum
(zero when empty), actual RET and RSP+8, complete RAM/permission equality, the
declared register frame and nonarithmetic flags, under current code, input and
original caller-slot authority. Every AF choice stream must terminate and
every actual reachable prefix retains current authority and authorized reads.
Empty input needs no input loan or canonical base; compatible readonly aliases
remain allowed. Compiler loop shape, exact operand order and cost are separate
client theorems, not part of task admission or its semantic postcondition.

GCCExport/ClangExport supply closed claims Client.gcc/Client.clang for complete
26/32-byte final functions. Neither implementation is in the grader's trusted
imports. Full mode requires contract/resource regressions and axiom audits,
fresh kernel replay and independent trusted/client snapshot isolation. Both
reference and body packets must export and grade with unchanged default limits,
against raw whole .text and the complete restricted ELF span: four exports and
eight positive grades. Changed task, shortened span, internally altered bytes
and the other compiler's bytes must reject with status 5 for each client:
eight negative grades. Artifact/task rejection establishes binding, not a
semantic defect in a changed artifact. Owned semantic mutants are independent
native checks; failures/timeouts/unsupported inputs do not establish defects.

The proofs establish the stated Lean model claims under their environmental
assumptions. Native observations remain finite evidence described separately
in native-scope.txt. Neither proves source/IR preservation, physical CPU/kernel
conformance, concurrent interference safety, whole-OS safety, timing, speculation
or a minimum among all possible implementations.
SCOPE
echo 'PASS: universal client/model audits, fresh kernel replay, isolation and raw/ELF proof-packet checks' \
    > "$output/proof-status.txt"
echo 'PASS: full model/proof integration and separate finite native evidence' > "$output/result.txt"
echo 'ArrayMaximum64 client proofs, raw/ELF grading and separate finite native contracts passed'
