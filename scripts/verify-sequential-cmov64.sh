#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail
if [[ $(uname -sm) != 'Linux x86_64' ]]; then
    echo 'Sequential register CMOV64 native integration requires Linux x86_64' >&2
    exit 2
fi
cd "$(dirname "${BASH_SOURCE[0]}")/.."
output=artifacts/sequential-cmov64
mkdir -p "$output"
compiler=${EDSL_CLANG:-clang-18}
"$compiler" --version > "$output/compiler.txt"
uname -srmo > "$output/platform.txt"
objcopy --version > "$output/objcopy.txt"
arguments=(-std=gnu23 -O2 -Wall -Wextra -Werror -fcf-protection=none -fno-lto -no-pie
    '-Wl,--build-id=none,-z,noexecstack' fixtures/sequential-cmov64-check.c
    fixtures/sequential-cmov64-probe.S -o "$output/native-check.elf")
printf '%q ' "$compiler" "${arguments[@]}" > "$output/arguments.txt"
printf '\n' >> "$output/arguments.txt"
"$compiler" "${arguments[@]}"
objcopy --dump-section ".edsl_cmov64=$output/instructions.bin" "$output/native-check.elf"
objdump -d -j .edsl_cmov64 "$output/native-check.elf" > "$output/disassembly.txt"
readelf -h -l -S -s -r -W "$output/native-check.elf" > "$output/elf.txt"
timeout 30 "$output/native-check.elf" "$output/instructions.bin" \
    > "$output/NativeSequentialCmov64.lean" 2> "$output/native-results.txt"
cat "$output/native-results.txt"
# Changed extraction must reject before probes execute and before Lean output.
cp "$output/instructions.bin" "$output/altered.bin"
printf '\x00' | dd of="$output/altered.bin" bs=1 count=1 conv=notrunc status=none
status=0
timeout 30 "$output/native-check.elf" "$output/altered.bin" \
    > "$output/altered.lean" 2> "$output/altered-results.txt" || status=$?
if [[ $status -ne 2 || -s "$output/altered.lean" ||
    $(< "$output/altered-results.txt") != 'Final ELF section extraction differs from executed bytes' ]]; then
    echo "Expected pre-probe ELF byte identity rejection 2 with empty Lean output, got $status" >&2
    exit 1
fi
flock /tmp/edsl-lean-build.lock lake build EDSL.X86.Sequential.Machine EDSL.Audit
flock /tmp/edsl-lean-build.lock lake env lean -DwarningAsError=true "$output/NativeSequentialCmov64.lean" \
    > "$output/kernel-check.txt" 2>&1
cat "$output/kernel-check.txt"
cat > "$output/scope.txt" <<'SCOPE'
Finite owned Linux x86-64 native/model conformance for register-only CMOV64.
The final linked ELF section holds 52 positive windows and six safe negative
windows, each followed by a capture jump. The observer requires exact identity
between the extracted final section and executed linked section before probes.
The independently requested C predicates inspect actual effective RFLAGS;
the observer has no instruction/REX/ModRM decoder. It checks all 16 GPRs and
complete captured flags. True conditions copy the full original source;
false conditions retain the complete destination. No flag changes are allowed.
All 16 conditions run with all 32 CF/PF/ZF/SF/OF combinations, both with AF/DF
clear and with AF/DF set on distinct register pairs. Captured condition bits
and AF/DF must equal requests or the run fails. Sixteen self aliases and four
ignored-X windows also run all 32 condition-flag combinations, totaling 1664
positive snapshots. All 16 GPRs occur as source/destination, including RSP;
REX.R/B banks, every REX.W prefix 48..4f and ignored X combinations are covered.
Distinct nonzero high halves and varied low bits expose narrowing/wrong-source
errors. This is selected register-pair/value coverage, not every possible pair
or payload. Effective user-mode flags are used, not arbitrary privileged flags.
The single-threaded capture makes no stack access while arbitrary modeled RSP
is installed; RIP-relative stores capture all registers before restoring host
RSP and recording flags. Neither positive nor negative windows access data.
Each positive snapshot is replayed through actual public Sequential.step
with both AF choices using kernel-checked rfl, followed by the transitive
axiom audit. Replay makes only exact instruction bytes accessible, with no
data mapping. RIP uses extracted continuation labels; empty operand-read lists
are independently requested semantics, not hardware memory-access traces.
Six register-only owned semantic mutations must fail: wrong condition, reversed
operands, 32-bit narrowing, flag damage, unconditional RSP write on a false
condition and wrong source. Their observations are excluded from positive
replay. Altered extraction must reject before probing and emit no Lean output.
Memory-source CMOV is outside this interface: its unconditional source loading
requires a separate memory/fault contract even when its condition is false.
W=0, extra/repeated prefixes and memory forms are not positive model cases.
These finite checks establish no universal ISA/CPU/OS conformance, fault delivery,
timing, speculation, concurrent visibility, atomicity or whole-kernel safety.
The harness is non-PIE and assumes ordinary selected user-mode flags, disabled
alignment checking/CET and no asynchronous interference with the capture.
SCOPE
sha256sum fixtures/sequential-cmov64-check.c fixtures/sequential-cmov64-probe.S \
    scripts/verify-sequential-cmov64.sh lean-toolchain lakefile.lean \
    EDSL/X86/Sequential/Condition.lean EDSL/X86/Sequential/Model.lean \
    EDSL/X86/Sequential/Decode.lean EDSL/X86/Sequential/Machine.lean \
    "$output/native-check.elf" "$output/instructions.bin" "$output/NativeSequentialCmov64.lean" \
    "$output/native-results.txt" "$output/kernel-check.txt" "$output/altered.bin" \
    "$output/altered.lean" "$output/altered-results.txt" "$output/compiler.txt" \
    "$output/platform.txt" "$output/objcopy.txt" "$output/arguments.txt" \
    "$output/disassembly.txt" "$output/elf.txt" "$output/scope.txt" > "$output/SHA256SUMS"
echo 'Sequential register CMOV64 native contracts and actual-step kernel replay passed'
