#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail
export LC_ALL=C
if [[ $# -ne 0 ]]; then
    echo 'usage: verify-logical64-native.sh' >&2
    exit 2
fi
if [[ $(uname -sm) != 'Linux x86_64' ]]; then
    echo 'Logical64 native evidence requires Linux x86_64 and the System V ABI' >&2
    exit 2
fi
cd "$(dirname "${BASH_SOURCE[0]}")/.."
# Run locally on the caller's machine; never dispatch native code over SSH.
archive=${EDSL_LOGICAL64_OUTPUT:-artifacts/logical64-native}
mkdir -p "$archive"
archive=$(cd "$archive" && pwd -P)
output=$(mktemp -d "$archive/run.XXXXXXXX")
printf 'Logical64 native evidence: %s\n' "$output"
ulimit -c 0

record_command() {
    printf '%q ' "$@"
    printf '\n'
}
write_hashes() {
    (cd "$output" && find . -type f ! -name SHA256SUMS -print0 | sort -z | xargs -0 sha256sum) \
        > "$output/SHA256SUMS"
}
# Every run gets a fresh directory. Preserve partial logs and hash them even
# after a build failure, unsupported compiler profile, signal or timeout.
finish() {
    local status=$?
    trap - EXIT
    if [[ $status -ne 0 ]]; then
        printf 'INCOMPLETE: script exit %s; inspect retained logs; no successful native claim\n' \
            "$status" > "$output/result.txt"
    fi
    printf '%s\n' "$status" > "$output/script-status.txt"
    if ! write_hashes || ! (cd "$output" && sha256sum --quiet --check SHA256SUMS); then
        status=1
        echo 'INCOMPLETE: evidence manifest creation/verification failed' > "$output/result.txt"
        printf '%s\n' "$status" > "$output/script-status.txt"
        write_hashes || true
        echo "Logical64 evidence manifest failed: $output" >&2
    fi
    if [[ $status -eq 0 ]]; then
        echo 'Logical64 finite native evidence passed; SHA256 manifest verified; Lean proofs NOT RUN'
    else
        printf 'Logical64 native evidence incomplete (exit %s): %s\n' "$status" "$output" >&2
    fi
    exit "$status"
}
trap finish EXIT
echo 'INCOMPLETE: native checks have not finished' > "$output/result.txt"
echo 'NOT RUN: Lean builds, universal theorems, source preservation and proof-packet grading' \
    > "$output/proof-status.txt"

gcc=${EDSL_GCC:-gcc-13}
clang=${EDSL_CLANG:-clang-18}
functions=(intersection64 union64 symmetric_difference64)
variants=(gcc clang)
identities=(4889f84821f0c3 4889f84809f0c3 4889f84831f0c3)
operations=(intersection union symmetric_difference)
names=()
binaries=()
final_elfs=()
source_files=(fixtures/logical64.c fixtures/logical64-check.c
    fixtures/logical64-check.S scripts/verify-logical64-native.sh)
sha256sum "${source_files[@]}" > "$output/source-SHA256SUMS"
for file in "${source_files[@]}"; do
    install -D -m 0644 "$file" "$output/source/$file"
done
(cd "$output/source" && sha256sum -c "$output/source-SHA256SUMS") > "$output/source-copy-check.txt"
record_command shellcheck -s bash scripts/verify-logical64-native.sh > "$output/shellcheck-arguments.txt"
shellcheck -s bash scripts/verify-logical64-native.sh > "$output/shellcheck.txt" 2>&1
uname -srmo > "$output/platform.txt"
hostname > "$output/hostname.txt"
lscpu > "$output/cpu.txt"
git rev-parse HEAD > "$output/repository-head.txt"
ld --version > "$output/linker.txt"
objcopy --version > "$output/objcopy.txt"
objdump --version > "$output/objdump.txt"
readelf --version > "$output/readelf.txt"
shellcheck --version > "$output/shellcheck-version.txt"
for tool in "$gcc" "$clang" ld objcopy objdump readelf shellcheck timeout; do
    tool_path=$(command -v "$tool")
    printf '%s\t%s\n' "$tool" "$tool_path" >> "$output/tool-paths.tsv"
    sha256sum "$(realpath "$tool_path")" >> "$output/tool-SHA256SUMS"
done
printf 'variant\tfunction\toperation\tspan\tbytes\n' > "$output/selections.tsv"

prepare() {
    local compiler=$1 variant=$2 required_major=$3
    local directory="$output/$variant"
    mkdir -p "$directory"
    "$compiler" --version > "$directory/compiler.txt"
    "$compiler" -dumpmachine > "$directory/compiler-target.txt"
    "$compiler" -dumpversion > "$directory/compiler-version.txt"
    local version
    version=$(< "$directory/compiler-version.txt")
    if [[ ${version%%.*} != "$required_major" ]]; then
        echo "Unsupported compiler major for $variant: expected $required_major, got $version" >&2
        exit 3
    fi
    local compile=(-std=gnu2x -Os -Wall -Wextra -Werror -fno-lto
        -fcf-protection=none -ffunction-sections -c "$output/source/fixtures/logical64.c"
        -o "$directory/functions.o")
    record_command "$compiler" "${compile[@]}" > "$directory/compile-arguments.txt"
    "$compiler" "${compile[@]}" > "$directory/compile-stdout.txt" 2> "$directory/compile-stderr.txt"
    local i function final expected actual span
    for i in "${!functions[@]}"; do
        function=${functions[$i]}
        final="$directory/$function"
        mkdir -p "$final"
        local link=(-m elf_x86_64 --build-id=none --gc-sections -z noexecstack
            -e "$function" -Ttext=0x401000 -o "$final/function.elf" "$directory/functions.o")
        record_command ld "${link[@]}" > "$final/link-arguments.txt"
        ld "${link[@]}" > "$final/link-stdout.txt" 2> "$final/link-stderr.txt"
        record_command objcopy --dump-section ".text=$final/function.bin" "$final/function.elf" \
            > "$final/extraction-arguments.txt"
        objcopy --dump-section ".text=$final/function.bin" "$final/function.elf" \
            > "$final/extraction-stdout.txt" 2> "$final/extraction-stderr.txt"
        readelf -h -l -S -s -r -n -W "$final/function.elf" > "$final/elf.txt"
        readelf -rW "$final/function.elf" > "$final/relocations.txt"
        if [[ $(< "$final/relocations.txt") != *'There are no relocations in this file.'* ]]; then
            echo "Relocated final logical64 ELF is outside this profile: $variant/$function" >&2
            exit 3
        fi
        objdump -d -Mintel "$final/function.elf" > "$final/disassembly.txt"
        span=$(wc -c < "$final/function.bin")
        printf '%s\n' "$span" > "$final/span.txt"
        expected=${identities[$i]}
        actual=$(od -An -tx1 -v "$final/function.bin" | tr -d ' \n')
        printf '%s\n' "$expected" > "$final/expected.txt"
        printf '%s\n' "$actual" > "$final/actual.txt"
        # Identity/admission is separate from the mathematical oracle. Reject
        # compiler drift and partial extraction; neither establishes a defect.
        if [[ "$actual" != "$expected" ]]; then
            echo "Unsupported whole final logical64 bytes: $variant/$function: $actual" >&2
            exit 3
        fi
        printf '%s\t%s\t%s\t%s\t%s\n' "$variant" "$function" "${operations[$i]}" \
            "$span" "$actual" >> "$output/selections.tsv"
        names+=("${variant}_${function}")
        binaries+=("$final/function.bin")
        final_elfs+=("$final/function.elf")
    done
}
prepare "$gcc" "${variants[0]}" 13
prepare "$clang" "${variants[1]}" 18

# .incbin embeds all six actual complete final extractions. No mmap, input
# program loader, instruction decoder or untrusted entry address is involved.
observer=(-std=gnu2x -O2 -Wall -Wextra -Werror -fno-lto -fcf-protection=none
    -fno-pie -no-pie '-Wl,--build-id=none,-z,noexecstack'
    "$output/source/fixtures/logical64-check.c" "$output/source/fixtures/logical64-check.S"
    -o "$output/native-check.elf")
{
    printf 'cd %q\n' "$output"
    record_command "$gcc" "${observer[@]}"
} > "$output/observer-arguments.txt"
(cd "$output" && "$gcc" "${observer[@]}") \
    > "$output/observer-stdout.txt" 2> "$output/observer-stderr.txt"
readelf -h -l -S -s -r -n -W "$output/native-check.elf" > "$output/observer-elf.txt"
objdump -d -Mintel -j .text -j .edsl_logical64 "$output/native-check.elf" \
    > "$output/observer-disassembly.txt"
record_command objcopy --dump-section ".edsl_logical64=$output/executed-section.bin" \
    "$output/native-check.elf" > "$output/observer-extraction-arguments.txt"
objcopy --dump-section ".edsl_logical64=$output/executed-section.bin" "$output/native-check.elf"
record_command timeout 60 "$output/native-check.elf" "${binaries[@]}" > "$output/native-arguments.txt"
status=0
timeout 60 "$output/native-check.elf" "${binaries[@]}" \
    > "$output/native-results.txt" 2> "$output/native-errors.txt" || status=$?
printf '%s\n' "$status" > "$output/native-status.txt"
if [[ $status -ne 0 ]]; then
    cat "$output/native-errors.txt" >&2
    echo "Logical64 native run did not pass: status $status (signals/timeouts are inconclusive)" >&2
    exit 1
fi
cat "$output/native-results.txt"

expect_extraction_rejection() {
    local index=$1 label=$2 changed=$3
    local directory="$output/extraction-rejections/${names[$index]}/$label"
    mkdir -p "$directory"
    local inputs=("${binaries[@]}")
    inputs[index]=$changed
    record_command timeout 60 "$output/native-check.elf" "${inputs[@]}" > "$directory/arguments.txt"
    local rejection_status=0
    timeout 60 "$output/native-check.elf" "${inputs[@]}" \
        > "$directory/stdout.txt" 2> "$directory/stderr.txt" || rejection_status=$?
    printf '%s\n' "$rejection_status" > "$directory/status.txt"
    if [[ $rejection_status -ne 2 || -s "$directory/stdout.txt" ||
        $(< "$directory/stderr.txt") != "Final ELF section extraction differs from executed bytes: ${names[$index]}" ]]; then
        echo "Expected pre-probe byte identity rejection 2: ${names[$index]}/$label, got $rejection_status" >&2
        exit 1
    fi
    rejection_count=$((rejection_count + 1))
}
rejection_count=0
for index in "${!binaries[@]}"; do
    directory="$output/extraction-rejections/${names[$index]}"
    mkdir -p "$directory"
    cp "${binaries[$index]}" "$directory/altered.bin"
    # Change the interior logical opcode, never execute the modified file.
    printf '\000' | dd of="$directory/altered.bin" bs=1 seek=4 count=1 conv=notrunc status=none
    expect_extraction_rejection "$index" altered "$directory/altered.bin"
    head -c 6 "${binaries[$index]}" > "$directory/truncated.bin"
    expect_extraction_rejection "$index" truncated "$directory/truncated.bin"
    cp "${binaries[$index]}" "$directory/extended.bin"
    printf '\220' >> "$directory/extended.bin"
    expect_extraction_rejection "$index" extended "$directory/extended.bin"
    other_index=$((index / 3 * 3 + (index + 1) % 3))
    expect_extraction_rejection "$index" substituted "${binaries[$other_index]}"
    : > "$directory/empty.bin"
    expect_extraction_rejection "$index" empty "$directory/empty.bin"
    expect_extraction_rejection "$index" full-elf "${final_elfs[$index]}"
done
printf 'PASS %s altered/truncated/extended/substituted/empty/full-ELF extraction rejections before native probing\n' \
    "$rejection_count" > "$output/extraction-results.txt"
cat "$output/extraction-results.txt"

cat > "$output/native-scope.txt" <<'SCOPE'
Finite owned Linux x86-64/System V whole-call evidence for uint64_t
intersection64, union64 and symmetric_difference64. Both GCC major 13 and Clang
major 18 freshly compile the archived source. Exact versions and tool hashes
are retained. The GNU23 driver profile is -std=gnu2x -Os -Wall -Wextra -Werror
-fno-lto -fcf-protection=none -ffunction-sections. GCC 13 does not support the
gnu23 spelling. Each function is separately final-linked with ld -m elf_x86_64
--build-id=none --gc-sections -z noexecstack -e FUNCTION -Ttext=0x401000.
Its entire .text must equal the selected seven-byte MOV RAX,RDI; logical
RAX,RSI; RET identity and the full final ELF must have no relocations. This
limited profile rejects compiler drift; rejection establishes no compiler defect.
Actual final ELF/raw bytes, versions, complete compile/link/extraction/observer/
run commands, ELF metadata, disassembly, source snapshots and hashes are stored.

The observer embeds the actual six entire final .text extractions via .incbin.
It compares all six supplied data files against their actually loaded execution
slots before any probe or positive stdout. An interior opcode mutation at offset
4, truncation, extension, substitution with another operation, empty file and
full ELF supplied as raw extraction are independently rejected for every slot:
36 pre-probe rejections, each status 2 and empty stdout. The runtime does not
execute file inputs, map executable memory or accept an input entry address.
Only project-owned compiler outputs and explicit safe owned assembly controls/
mutants are called. The bare function ELF is not launched as a process. The
embedded position-independent instructions execute at different addresses from
their original 0x401000 link address, with the same complete instruction bytes.

The mathematical oracle defines S(word) as bit positions i in [0,64) where
floor(word/2^i) mod 2 = 1. For every output bit it requests membership in both
input sets, either input set, or exactly one input set. It contains no byte
decoder, model/Lean invocation or whole-word logical expected-result expression.
Every bit of the actual full64 RAX is checked. Inputs include all 32x32 ordered
boundary pairs; all four membership combinations at each of 64 positions with
the other bits uniformly absent or present; and both orders of single-bit/
complement pairs and their equal pairs. Those cases run under all 128 input
CF/PF/AF/ZF/SF/OF/ID combinations. Three deterministic seeds each add 8192
full64 pairs, including equal and complementary operands every sixteen pairs.
Zero, full word, distinct high halves and 32-bit truncation boundaries occur.
Actual per-function/total call counts are reported in native-results.txt.

The observer verifies actual flag installation and 16-byte caller alignment,
all six actual SysV callee-saved GPRs RBX/RBP/R12..R15, the actual RSP before/
after CALL/RET and preservation of all captured nonarithmetic RFLAGS. DF is
clear at every ordinary SysV call; ID is tested both ways. Privileged flags are
only their effective user-mode values. Arithmetic flags including AF are all
unconstrained on return. Three owned acceptance controls set every arithmetic
flag, including AF, and must still satisfy the independent contract on all
32x32 boundary pairs under every flag profile. Their calls are counted separately.
Capture uses only MOVs until flags have been saved and restores host stack/
flags before returning to C. Recovery globals require single-threaded use.

Twenty-one safe owned assembly negatives must fail for exactly the requested
category: both wrong alternative operators per operation (six), 32-bit narrowing
per operation (three), wrong input register per operation (three), each of six
saved-GPR clobbers, RET $8 stack imbalance, setting DF and changing ID. The
independent oracle finds and prints concrete rejection witnesses. These are
synthetic project fixtures, not security findings or compiler defects. Signals,
timeouts and unexpected failure categories fail this run and are inconclusive.
Fresh per-run directories preserve failed evidence; an EXIT trap hashes partial
artifacts and records failure rather than converting it to a successful claim.

This is finite native evidence, not a universal Lean or physical CPU theorem,
source/IR preservation, proof-packet acceptance, whole-RAM/data-memory frame
proof, hardware access trace, timing/speculation result, concurrent visibility,
atomicity or whole-OS safety. It assumes normal stable user memory, the recorded
Linux CPU/kernel/System V environment, disabled CET and no asynchronous
interference with capture. RSP is a real host pointer, not arbitrary modeled
state. Universal machine/model claims need separately checked root-owned
theorems and environmental/resource contracts. No Lean build or import is run.
SCOPE

# Separate hashes make source, tool, command and machine-byte evidence easy to
# inspect, while the final manifest covers every retained file in this run.
find "$output" -type f -name '*arguments.txt' -print0 | sort -z \
    > "$output/command-files.nul"
while IFS= read -r -d '' file; do
    sha256sum "$file"
done < "$output/command-files.nul" > "$output/command-SHA256SUMS"
byte_files=("$output/gcc/functions.o" "$output/clang/functions.o" "${final_elfs[@]}"
    "${binaries[@]}" "$output/native-check.elf" "$output/executed-section.bin")
sha256sum "${byte_files[@]}" > "$output/byte-SHA256SUMS"
sha256sum "$output/platform.txt" "$output/hostname.txt" "$output/cpu.txt" \
    > "$output/platform-SHA256SUMS"
echo 'PASS: finite native checks and extraction rejections; universal/proof checks NOT RUN' \
    > "$output/result.txt"
