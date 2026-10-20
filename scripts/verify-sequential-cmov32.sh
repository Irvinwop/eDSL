#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail
if [[ $(uname -sm) != 'Linux x86_64' ]]; then
    echo 'Sequential register CMOV32 native checks require Linux x86_64' >&2
    exit 2
fi
cd "$(dirname "${BASH_SOURCE[0]}")/.."
output=${EDSL_CMOV32_OUTPUT:-.cache/cmov32-work/native/run}
mkdir -p "$output"
compiler=${EDSL_CLANG:-clang-18}
"$compiler" --version > "$output/compiler.txt"
uname -srmo > "$output/platform.txt"
lscpu > "$output/cpu.txt"
objcopy --version > "$output/objcopy.txt"
arguments=(-std=gnu23 -O2 -Wall -Wextra -Werror -fcf-protection=none -fno-lto -no-pie
    '-Wl,--build-id=none,-z,noexecstack' fixtures/sequential-cmov32-check.c
    fixtures/sequential-cmov32-probe.S -o "$output/native-check.elf")
printf '%q ' "$compiler" "${arguments[@]}" > "$output/arguments.txt"
printf '\n' >> "$output/arguments.txt"
"$compiler" "${arguments[@]}"
objcopy --dump-section ".edsl_cmov32=$output/instructions.bin" "$output/native-check.elf"
objdump -d -j .edsl_cmov32 "$output/native-check.elf" > "$output/disassembly.txt"
readelf -h -l -S -s -r -W "$output/native-check.elf" > "$output/elf.txt"
timeout 30 "$output/native-check.elf" "$output/instructions.bin" \
    > "$output/observations.tsv" 2> "$output/native-results.txt"
cat "$output/native-results.txt"
# Every identity control must fail before probe execution or observation output.
cp "$output/instructions.bin" "$output/altered.bin"
printf '\x00' | dd of="$output/altered.bin" bs=1 count=1 conv=notrunc status=none
head -c -1 "$output/instructions.bin" > "$output/truncated.bin"
cp "$output/instructions.bin" "$output/appended.bin"
printf '\x00' >> "$output/appended.bin"
: > "$output/identity-controls.tsv"
for mutation in altered truncated appended; do
    status=0
    timeout 30 "$output/native-check.elf" "$output/$mutation.bin" \
        > "$output/$mutation.tsv" 2> "$output/$mutation-results.txt" || status=$?
    if [[ $status -ne 2 || -s "$output/$mutation.tsv" ||
        $(< "$output/$mutation-results.txt") != 'Final ELF section extraction differs from executed bytes' ]]; then
        echo "Expected pre-probe ELF byte identity rejection 2 with empty output for $mutation, got $status" >&2
        exit 1
    fi
    printf '%s\t%s\n' "$mutation" "$status" >> "$output/identity-controls.tsv"
done
cat > "$output/scope.txt" <<'SCOPE'
Finite owned Linux x86-64 hardware observations for register-only CMOV32.
This script performs native checks only. No Lean/model/kernel replay is claimed.
The final linked section holds 52 positive windows and eight safe semantic
mutants, each followed by a capture jump. Extracted bytes must match the whole
executed section before any probe. Altered, shortened and appended extraction
controls must reject before any observation output.
The independent C observer has no opcode/REX/ModRM decoder. Its named condition
contracts inspect actual effective RFLAGS and compare all 16 full GPRs and all
captured RFLAGS. The selected low32 source (true) or original destination
(false) is zero extended into the full destination. False conditions and every
self alias must also clear the high32 destination. Other GPRs and flags retain
their original values. Input source and destination are read before writing.
All 16 conditions are tested unprefixed; REX.R/B banks cover every GPR in both
roles; all 16 self aliases and ignored REX.X across four banks are included.
Positive windows use unprefixed or one 40..47 REX prefix, 0f40..4f and register
ModRM. Every window runs all 32 CF/PF/ZF/SF/OF combinations, both AF/DF profiles
and six boundary/mixed-low32 payloads, totaling 19968 snapshots.
All payloads have nonzero high halves to expose false-condition retention,
64/16-bit width, sign-extension, wrong-register or aliasing errors.
Eight owned semantic mutants must fail independent contracts: condition,
operand direction, 64-bit width, 16-bit width, flag damage, false no-write to
RSP, wrong source and false alias no-write. Mutant data is never positive data.
The harness does not implement a decoder or establish unsupported-form
rejection. Lean integration must reject memory, operand-size16, multiple or
legacy prefixes and malformed/truncated encodings, and keep W=1 in its CMOV64
path. Memory-source CMOV has unconditional source reads and needs its own
read/fault contract, including false conditions.
Capture is single threaded and nonreentrant. No stack or data dereference is
performed by instruction windows while arbitrary modeled RSP is installed;
RIP-relative stores capture all GPRs before restoring host RSP and recording flags.
The harness assumes ordinary user mode, executable owned code, disabled CET
and alignment checking, installed requested flags and no asynchronous capture
interference. -fcf-protection=none applies to this native harness, not corpus
compiler output. CPUID must advertise CMOV. This is selected-pair and finite
payload coverage on the recorded CPU, not universal CPU/ISA/OS conformance,
timing, speculation, atomicity, interleaving or whole-system safety.
SCOPE
sha256sum fixtures/sequential-cmov32-check.c fixtures/sequential-cmov32-probe.S \
    scripts/verify-sequential-cmov32.sh "$output/native-check.elf" \
    "$output/instructions.bin" "$output/observations.tsv" "$output/native-results.txt" \
    "$output/altered.bin" "$output/altered.tsv" "$output/altered-results.txt" \
    "$output/truncated.bin" "$output/truncated.tsv" "$output/truncated-results.txt" \
    "$output/appended.bin" "$output/appended.tsv" "$output/appended-results.txt" \
    "$output/identity-controls.tsv" "$output/compiler.txt" "$output/platform.txt" \
    "$output/cpu.txt" "$output/objcopy.txt" "$output/arguments.txt" \
    "$output/disassembly.txt" "$output/elf.txt" "$output/scope.txt" > "$output/SHA256SUMS"
echo 'Sequential register CMOV32 native contracts passed; Lean integration remains pending'
