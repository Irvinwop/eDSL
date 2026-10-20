#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail
export LC_ALL=C
if [[ $# -ne 0 ]]; then
    echo 'usage: verify-short-jcc.sh' >&2
    exit 2
fi
if [[ $(uname -sm) != 'Linux x86_64' ]]; then
    echo 'Short-Jcc native checks require Linux x86_64 and the System V ABI' >&2
    exit 2
fi
cd "$(dirname "${BASH_SOURCE[0]}")/.."
source_root=$PWD
archive=${EDSL_SHORT_JCC_OUTPUT:-artifacts/short-jcc}
mkdir -p "$archive"
archive=$(cd "$archive" && pwd -P)
output=$(mktemp -d "$archive/run.XXXXXXXX")
printf 'Short-Jcc evidence: %s\n' "$output"
ulimit -c 0
compiler=${EDSL_CC:-cc}
record_command() { printf '%q ' "$@"; printf '\n'; }
uname -srmo > "$output/platform.txt"
"$compiler" --version > "$output/compiler.txt"
command -v "$compiler" > "$output/compiler-path.txt"
objcopy --version > "$output/objcopy.txt"
objdump --version > "$output/objdump.txt"
readelf --version > "$output/readelf.txt"
source_files=(fixtures/short-jcc-check.c fixtures/short-jcc-check.S scripts/verify-short-jcc.sh)
sha256sum "${source_files[@]}" > "$output/source-SHA256SUMS"
for file in "${source_files[@]}"; do
    install -D -m 0644 "$file" "$output/source/$file"
done
(cd "$output/source" && sha256sum -c "$output/source-SHA256SUMS") > "$output/source-copy-check.txt"
compile=(-std=gnu2x -O2 -Wall -Wextra -Werror -fno-lto -fcf-protection=none
    -fno-pie -no-pie '-Wl,--build-id=none,-z,noexecstack'
    "$source_root/fixtures/short-jcc-check.c" "$source_root/fixtures/short-jcc-check.S"
    -o "$output/native-check.elf")
record_command "$compiler" "${compile[@]}" > "$output/compile-arguments.txt"
"$compiler" "${compile[@]}"
readelf -h -l -S -s -r -W "$output/native-check.elf" > "$output/elf.txt"
objdump -d -Mintel -j .text -j .edsl_short_jcc "$output/native-check.elf" \
    > "$output/disassembly.txt"
record_command objcopy --dump-section ".edsl_short_jcc=$output/fixtures.bin" \
    "$output/native-check.elf" > "$output/extraction-arguments.txt"
objcopy --dump-section ".edsl_short_jcc=$output/fixtures.bin" "$output/native-check.elf"
record_command "$output/native-check.elf" "$output/fixtures.bin" > "$output/native-arguments.txt"
status=0
timeout 30 "$output/native-check.elf" "$output/fixtures.bin" \
    > "$output/native-results.txt" 2> "$output/native-errors.txt" || status=$?
printf '%s\n' "$status" > "$output/native-status.txt"
if [[ $status -ne 0 ]]; then
    cat "$output/native-errors.txt" >&2
    echo "Short-Jcc native run failed: status $status (signals/timeouts are inconclusive)" >&2
    exit 1
fi
cat "$output/native-results.txt"

# Changed files are never executed; identity must fail before any probe/output.
mkdir "$output/extraction-rejections"
cp "$output/fixtures.bin" "$output/extraction-rejections/altered.bin"
printf '\220' | dd of="$output/extraction-rejections/altered.bin" bs=1 count=1 conv=notrunc status=none
size=$(wc -c < "$output/fixtures.bin")
head -c "$((size - 1))" "$output/fixtures.bin" > "$output/extraction-rejections/truncated.bin"
cp "$output/fixtures.bin" "$output/extraction-rejections/extended.bin"
printf '\220' >> "$output/extraction-rejections/extended.bin"
for label in altered truncated extended; do
    directory="$output/extraction-rejections/$label"
    mkdir "$directory"
    rejected=0
    record_command "$output/native-check.elf" "$output/extraction-rejections/$label.bin" \
        > "$directory/arguments.txt"
    timeout 30 "$output/native-check.elf" "$output/extraction-rejections/$label.bin" \
        > "$directory/stdout.txt" 2> "$directory/stderr.txt" || rejected=$?
    printf '%s\n' "$rejected" > "$directory/status.txt"
    if [[ $rejected -ne 2 || -s "$directory/stdout.txt" ||
        $(< "$directory/stderr.txt") != 'Owned fixture section differs from executed bytes' ]]; then
        echo "Expected pre-probe extraction rejection 2: $label, got $rejected" >&2
        exit 1
    fi
done
echo 'PASS 3 altered/truncated/extended extraction rejections before native probing' \
    > "$output/extraction-results.txt"
cat "$output/extraction-results.txt"
cat > "$output/scope.txt" <<'SCOPE'
Finite native evidence for the 16 ordinary x86-64 short conditional branches,
opcodes 70..7f. Owned static assembly fixtures use named Jcc mnemonics; the final
linked opcode, signed displacement and actual target are checked before any
native probe. Every condition has a +127 and a -128 displacement fixture. All
64 combinations of CF/PF/AF/ZF/SF/OF run with ID clear and set: 4096 whole calls.
The independent C oracle gives the named Boolean flag predicates; it does not
decode the instruction or copy an assigned fixture result. Each path returns
its actual reached label address with LEA, then executes RET. The observer
requires the requested flag profile to have been installed and every captured
RFLAGS bit to remain unchanged across CALL, Jcc, LEA and RET. AF is varied even
though no Jcc consumes it. Effective non-arithmetic host flags remain captured;
DF is clear at the SysV call. Captured privileged flags use their user-mode
values. RIP-relative LEA records the real final linked path addresses.

Three safe owned synthetic mutants exercise distinct oracle failures across
all 128 profiles: inverse condition (128 wrong paths), a wrong safe signed
branch destination (64 wrong paths), and CMC before JO (128 flag-frame failures
with unchanged branch decision). An unexpected failure category is an error.
Signals and timeouts are inconclusive and fail the run. The extracted fixture
section must equal the actually linked executable bytes before any probe;
altered, truncated and extended extraction inputs each require status 2 with
empty stdout. Supplied files are compared only, never mapped or executed.
Compiler path/version, commands, ELF metadata, disassembly, source snapshots
and SHA256 hashes are recorded. The runner uses caller PATH and EDSL_CC.

This is finite Linux x86-64/System V native evidence, not a universal Lean
proof, proof-packet acceptance, arbitrary displacement coverage, canonicality
or fault testing, source preservation, physical CPU/kernel validation, timing,
speculation, concurrent visibility, whole-OS safety or an operation optimum.
Stable ordinary user memory, the recorded CPU/kernel environment, disabled CET
and no asynchronous interference with capture are assumed. The observer uses a
real aligned host stack and single-threaded global capture/recovery state.
SCOPE
echo 'PASS finite native Jcc checks; Lean proofs and theorem audits are separate' > "$output/result.txt"
(cd "$output" && find . -type f ! -name SHA256SUMS -print0 | sort -z | xargs -0 sha256sum) \
    > "$output/SHA256SUMS"
echo 'Short-Jcc finite native checks passed'
