#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail
if [[ $(uname -sm) != 'Linux x86_64' ]]; then
    echo 'Sequential MOV32 native integration requires Linux x86_64' >&2
    exit 2
fi
cd "$(dirname "${BASH_SOURCE[0]}")/.."
output=artifacts/sequential-moves
mkdir -p "$output"
compiler=${EDSL_CLANG:-clang}
"$compiler" --version > "$output/compiler.txt"
uname -srmo > "$output/platform.txt"
objcopy --version > "$output/objcopy.txt"
arguments=(-std=gnu23 -O2 -Wall -Wextra -Werror -fcf-protection=none -fno-lto -no-pie
    '-Wl,--build-id=none,-z,noexecstack' fixtures/sequential-moves-check.c
    fixtures/sequential-moves-probe.S -o "$output/native-check.elf")
printf '%q ' "$compiler" "${arguments[@]}" > "$output/arguments.txt"
printf '\n' >> "$output/arguments.txt"
"$compiler" "${arguments[@]}"
objcopy --dump-section ".edsl_moves=$output/instructions.bin" "$output/native-check.elf"
objdump -d -j .edsl_moves "$output/native-check.elf" > "$output/disassembly.txt"
readelf -h -l -S -s -r -W "$output/native-check.elf" > "$output/elf.txt"
timeout 30 "$output/native-check.elf" "$output/instructions.bin" \
    > "$output/NativeSequentialMoves.lean" 2> "$output/native-results.txt"
cat "$output/native-results.txt"
# A malformed artifact must fail the executed-byte identity check before any
# probe runs; the synthetic alteration is never executed as machine code.
cp "$output/instructions.bin" "$output/altered.bin"
printf '\x00' | dd of="$output/altered.bin" bs=1 count=1 conv=notrunc status=none
status=0
timeout 30 "$output/native-check.elf" "$output/altered.bin" \
    > "$output/altered.lean" 2> "$output/altered-results.txt" || status=$?
if [[ $status -ne 2 ]]; then
    echo "Expected ELF byte identity rejection 2, got $status" >&2
    exit 1
fi
flock /tmp/edsl-lean-build.lock lake build EDSL.X86.Sequential.Machine EDSL.Audit
flock /tmp/edsl-lean-build.lock lake env lean -DwarningAsError=true "$output/NativeSequentialMoves.lean" \
    > "$output/kernel-check.txt" 2>&1
cat "$output/kernel-check.txt"
cat > "$output/scope.txt" <<'SCOPE'
Finite native/model conformance evidence for owned Linux x86-64 MOV32 fixtures.
The assembler and linker produce one-instruction windows with capture jumps.
The native observer checks that the final ELF section extracted by objcopy is
identical to the executed linked section. Its independent requested contracts
check all 16 GPRs, complete captured RFLAGS and all 32 observed data bytes.
Each successful actual CPU snapshot is replayed through public Sequential.step
with both AF choices and checked by Lean's kernel using rfl, followed by the
project theorem-dependency audit. This creates no new trusted model module.
The capture harness supports arbitrary modeled RSP: it performs no stack access
until restoring its saved host RSP. Both 89/8b directions, every low register,
self zero-extension, all plain admitted bases, all SIB scales, RSP base/RBP index,
base/index/source/destination aliases and addresses above 4GiB are covered.
Data offsets 2 and 28 check unaligned and last-four-observed-byte operands.
The observed 32-byte region is inside an owned writable page with guard pages;
these runs do not test inaccessible operands or establish universal ISA/OS
correctness, concurrency, timing, fault behavior, speculation or kernel safety.
RIP expectations use the extracted next-instruction labels; operand-read lists
are independent requested footprints, not observations of hardware reads.
Width, direction, omitted-store and neighboring-byte mutants are safe owned
fixtures rejected by the independent C contract observer and never replayed as
supported MOV32. The intentionally altered extraction is rejected before use.
The harness is single-threaded, non-PIE, and assumes the selected user-mode
RFLAGS profile with alignment checking/CET disabled.
SCOPE
sha256sum fixtures/sequential-moves-check.c fixtures/sequential-moves-probe.S \
    scripts/verify-sequential-moves.sh "$output/native-check.elf" "$output/instructions.bin" \
    "$output/NativeSequentialMoves.lean" "$output/native-results.txt" "$output/kernel-check.txt" \
    "$output/compiler.txt" "$output/arguments.txt" "$output/scope.txt" > "$output/SHA256SUMS"
echo 'Sequential MOV32 native/model replay passed'
