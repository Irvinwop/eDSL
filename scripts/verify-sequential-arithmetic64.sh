#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail
if [[ $(uname -sm) != 'Linux x86_64' ]]; then
    echo 'Sequential LEA64/register ADD64 native integration requires Linux x86_64' >&2
    exit 2
fi
cd "$(dirname "${BASH_SOURCE[0]}")/.."
output=artifacts/sequential-arithmetic64
mkdir -p "$output"
compiler=${EDSL_CLANG:-clang-18}
"$compiler" --version > "$output/compiler.txt"
uname -srmo > "$output/platform.txt"
objcopy --version > "$output/objcopy.txt"
arguments=(-std=gnu23 -O2 -Wall -Wextra -Werror -fcf-protection=none -fno-lto -no-pie
    '-Wl,--build-id=none,-z,noexecstack' fixtures/sequential-arithmetic64-check.c
    fixtures/sequential-arithmetic64-probe.S -o "$output/native-check.elf")
printf '%q ' "$compiler" "${arguments[@]}" > "$output/arguments.txt"
printf '\n' >> "$output/arguments.txt"
"$compiler" "${arguments[@]}"
objcopy --dump-section ".edsl_arithmetic64=$output/instructions.bin" "$output/native-check.elf"
objdump -d -j .edsl_arithmetic64 "$output/native-check.elf" > "$output/disassembly.txt"
readelf -h -l -S -s -r -W "$output/native-check.elf" > "$output/elf.txt"
timeout 30 "$output/native-check.elf" "$output/instructions.bin" \
    > "$output/NativeSequentialArithmetic64.lean" 2> "$output/native-results.txt"
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
flock /tmp/edsl-lean-build.lock lake env lean -DwarningAsError=true "$output/NativeSequentialArithmetic64.lean" \
    > "$output/kernel-check.txt" 2>&1
cat "$output/kernel-check.txt"
cat > "$output/scope.txt" <<'SCOPE'
Finite owned Linux x86-64 native/model conformance for LEA64 effective-address
arithmetic and register ADD64. One linked ELF section holds 116 positive windows
and nine safe owned negative windows, each with a direct capture jump. Before
any probe, the observer requires exact identity between the extracted final
section and the executed linked section, including capture jumps and negatives.
An independently requested C contract checks all 16 GPRs and complete captured
RFLAGS. LEA checks full-width base+index*scale arithmetic and unchanged flags;
ADD uses a mathematical 65-bit unsigned sum, nibble addition, sign comparison and
low-byte population count for CF/PF/AF/ZF/SF/OF, preserving all remaining flags.
The 240 LEA observations cover 60 windows: all 16 destination registers, all 12
admitted plain bases, every REX.W byte and R/X/B combination, ignored X without
SIB, all scales, extended operands, RSP/R12 bases, RBP/R12 indices and aliases
between destination/base/index. Four value profiles include high, noncanonical
and wrapping arithmetic. These are values, not memory addresses being accessed.
The 672 ADD observations cover 56 windows: 01/03 opcode directions with all 16
registers as source/destination, all 16 self-adds, RSP on either side, all R/B
banks and ignored X combinations. Twelve value profiles include zero, full64
carry, signed overflow, nibble carry, parity, high halves and modular wrap.
Flags requests alternate 0x202/0xed7; expectations use actual effective user-mode
flags captured immediately before each instruction, not arbitrary RFLAGS.
No stack access occurs while the arbitrary modeled RSP is installed; RIP-relative
capture restores the host stack before pushfq. The fixture is single-threaded.
Each of the 912 actual positive CPU snapshots is replayed through public
Sequential.step for both AF choices using kernel-checked rfl, followed by the
project transitive axiom audit. Replay models only the exact instruction bytes
as accessible memory, so effective-address arithmetic cannot rely on data reads.
RIP uses extracted continuation labels; the empty operand-read list is an
independently requested footprint, not a hardware memory-access trace.
Nine safe register-only mutations must fail the C oracle: wrong LEA scale/base,
narrow LEA, changed LEA flags, wrong ADD source, narrow ADD, omitted ADD flags,
cleared carry and wrong direction. Negative observations are excluded from
positive replay. The altered extraction rejects before any probe executes.
This does not establish universal ISA/CPU/OS correctness, memory-fault delivery,
timing, speculation, concurrent visibility, atomicity or whole-kernel safety.
The harness is non-PIE and assumes ordinary selected user-mode flags with CET
and alignment checking disabled. No asynchronous-interference result is claimed.
SCOPE
sha256sum fixtures/sequential-arithmetic64-check.c fixtures/sequential-arithmetic64-probe.S \
    scripts/verify-sequential-arithmetic64.sh lean-toolchain lakefile.lean \
    EDSL/X86/Sequential/Model.lean EDSL/X86/Sequential/Decode.lean \
    EDSL/X86/Sequential/Machine.lean EDSL/X86/Sequential/Flags.lean EDSL/X86/Flags.lean \
    "$output/native-check.elf" "$output/instructions.bin" "$output/NativeSequentialArithmetic64.lean" \
    "$output/native-results.txt" "$output/kernel-check.txt" "$output/altered.bin" \
    "$output/altered.lean" "$output/altered-results.txt" "$output/compiler.txt" \
    "$output/platform.txt" "$output/objcopy.txt" "$output/arguments.txt" \
    "$output/disassembly.txt" "$output/elf.txt" "$output/scope.txt" > "$output/SHA256SUMS"
echo 'Sequential LEA64/register ADD64 native contracts and actual-step kernel replay passed'
