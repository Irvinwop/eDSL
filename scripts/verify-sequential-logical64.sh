#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail
if [[ $(uname -sm) != 'Linux x86_64' ]]; then
    echo 'Sequential register AND64/OR64/XOR64 native integration requires Linux x86_64' >&2
    exit 2
fi
cd "$(dirname "${BASH_SOURCE[0]}")/.."
output=artifacts/sequential-logical64
mkdir -p "$output"
compiler=${EDSL_CLANG:-clang-18}
"$compiler" --version > "$output/compiler.txt"
uname -srmo > "$output/platform.txt"
objcopy --version > "$output/objcopy.txt"
arguments=(-std=gnu23 -O2 -Wall -Wextra -Werror -fcf-protection=none -fno-lto -no-pie
    '-Wl,--build-id=none,-z,noexecstack' fixtures/sequential-logical64-check.c
    fixtures/sequential-logical64-probe.S -o "$output/native-check.elf")
printf '%q ' "$compiler" "${arguments[@]}" > "$output/arguments.txt"
printf '\n' >> "$output/arguments.txt"
"$compiler" "${arguments[@]}"
objcopy --dump-section ".edsl_logical64=$output/instructions.bin" "$output/native-check.elf"
objdump -d -j .edsl_logical64 "$output/native-check.elf" > "$output/disassembly.txt"
readelf -h -l -S -s -r -W "$output/native-check.elf" > "$output/elf.txt"
timeout 30 "$output/native-check.elf" "$output/instructions.bin" \
    > "$output/NativeSequentialLogical64.lean" 2> "$output/native-results.txt"
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
flock /tmp/edsl-lean-build.lock lake env lean -DwarningAsError=true "$output/NativeSequentialLogical64.lean" \
    > "$output/kernel-check.txt" 2>&1
cat "$output/kernel-check.txt"
cat > "$output/scope.txt" <<'SCOPE'
Finite owned Linux x86-64 native/model conformance for register AND64, OR64 and
XOR64. One linked ELF section holds 216 positive windows and 15 safe owned
negative windows, each with a direct capture jump. Before any probe, the observer
requires exact identity between the extracted final section and the executed
linked section, including capture jumps and negatives. An independently
requested C contract defines operations as finite sets of bit positions and
checks all 16 GPRs and effective captured RFLAGS. CF/OF must clear; PF/ZF/SF
follow the mathematical result; every other bit except undefined AF must remain
unchanged. The C oracle masks exactly AF bit4. Each actual captured AF value is
then an explicit choice witnessing complete flags in kernel replay. The harness
does not require both AF values to occur on this CPU or claim a canonical AF.
There are 2592 actual positive CPU snapshots: 864 per operation, 12 value profiles
per window. For each operation both opcode directions cover all 16 registers as
source and destination, all 16 self aliases in both directions, RSP on either
side, all R/B banks and ignored X combinations. Profiles include zero, high
halves, sign-only results, low-byte parity, equal and complementary operands.
Flags requests alternate 0x202/0xed7; expectations use actual effective user-mode
flags captured immediately before the instruction, not arbitrary RFLAGS.
No stack access occurs while arbitrary modeled RSP is installed; RIP-relative
capture restores the host stack before pushfq. The fixture is single-threaded.
Every complete captured register/flags snapshot is replayed through public
Sequential.step using the actual captured AF witness and kernel-checked rfl,
followed by the project transitive axiom audit. Replay models only exact
instruction bytes as accessible memory. RIP uses extracted continuation labels;
the empty operand-read list is an independently requested footprint rather than
a hardware memory-access trace. Fifteen safe register-only mutations must fail
the C oracle: per operation wrong operator, wrong written register/direction,
wrong source, narrow width and set carry. Negative observations are excluded
from positive replay. The altered extraction rejects before any probe executes.
This does not establish universal ISA/CPU/OS correctness, memory-fault delivery,
timing, speculation, concurrent visibility, atomicity or whole-kernel safety.
The harness is non-PIE and assumes ordinary selected user-mode flags with CET
and alignment checking disabled. No asynchronous-interference result is claimed.
SCOPE
sha256sum fixtures/sequential-logical64-check.c fixtures/sequential-logical64-probe.S \
    scripts/verify-sequential-logical64.sh lean-toolchain lakefile.lean \
    EDSL/X86/Sequential/Model.lean EDSL/X86/Sequential/Decode.lean \
    EDSL/X86/Sequential/Machine.lean EDSL/X86/Sequential/Flags.lean EDSL/X86/Flags.lean \
    "$output/native-check.elf" "$output/instructions.bin" "$output/NativeSequentialLogical64.lean" \
    "$output/native-results.txt" "$output/kernel-check.txt" "$output/altered.bin" \
    "$output/altered.lean" "$output/altered-results.txt" "$output/compiler.txt" \
    "$output/platform.txt" "$output/objcopy.txt" "$output/arguments.txt" \
    "$output/disassembly.txt" "$output/elf.txt" "$output/scope.txt" > "$output/SHA256SUMS"
echo 'Sequential register AND64/OR64/XOR64 native contracts and actual-step kernel replay passed'
