#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail
export PATH="${HOME}/.elan/bin:$PATH"
export LEAN_NUM_THREADS=1
cd "$(dirname "${BASH_SOURCE[0]}")/.."
root=$PWD
output_root=artifacts/sequential-compare32
output=$output_root/run-$(date -u +%Y%m%dT%H%M%S)-$$
mkdir -p "$output"
printf '%s\n' "$output" > "$output_root/latest-run.txt"
exec 3> "$output/commands-exits.log"
exec 4> "$output/shell-trace.log"
export BASH_XTRACEFD=4
set -x
run() {
    printf 'command:' >&3
    printf ' %q' "$@" >&3
    printf '\n' >&3
    local status=0
    "$@" || status=$?
    printf 'exit: %u\n' "$status" >&3
    return "$status"
}
finish() {
    local status=$?
    set +x
    printf '%u\n' "$status" > "$output/script.exit"
    sha256sum fixtures/sequential-compare32-check.c fixtures/sequential-compare32-probe.S \
        scripts/verify-sequential-compare32.sh > "$output/SOURCES.sha256"
    printf 'Fixture logs: %s/%s (exit %u)\n' "$root" "$output" "$status"
}
trap finish EXIT
{
    printf '%s\n' lean-toolchain lakefile.lean EDSL.lean EDSL/Audit.lean
    find EDSL -type f -name '*.lean'
    printf '%s\n' tests/SequentialCompare32.lean tests/SequentialPadding.lean
    printf '%s\n' fixtures/sequential-compare32-check.c fixtures/sequential-compare32-probe.S
    printf '%s\n' scripts/verify-sequential-compare32.sh
} | LC_ALL=C sort -u | xargs -d '\n' sha256sum > "$output/MODEL-SOURCES.sha256"
if [[ $(uname -sm) != 'Linux x86_64' ]]; then
    echo 'Sequential CMP32/TEST32 native integration requires Linux x86_64' >&2
    exit 2
fi
compiler=${EDSL_CLANG:-clang-18}
run "$compiler" --version > "$output/compiler.txt"
run uname -srmo > "$output/platform.txt"
run objcopy --version > "$output/objcopy.txt"
arguments=(-std=gnu23 -O2 -Wall -Wextra -Werror -fcf-protection=none -fno-lto -no-pie
    '-Wl,--build-id=none,-z,noexecstack' fixtures/sequential-compare32-check.c
    fixtures/sequential-compare32-probe.S -o "$output/native-check.elf")
run "$compiler" "${arguments[@]}" > "$output/compiler.log" 2>&1
run objcopy --dump-section ".edsl_compare32=$output/instructions.bin" "$output/native-check.elf" \
    > "$output/extraction.log" 2>&1
run objdump -d -j .edsl_compare32 "$output/native-check.elf" > "$output/disassembly.txt"
run readelf -h -l -S -s -r -W "$output/native-check.elf" > "$output/elf.txt"
run timeout 30 "$output/native-check.elf" "$output/instructions.bin" \
    > "$output/NativeSequentialCompare32.lean" 2> "$output/native-results.txt"
cat "$output/native-results.txt"
# Changed, truncated, and overlong extraction must reject before every probe
# and before any Lean text. The C identity gate is first in main.
run cp "$output/instructions.bin" "$output/altered.bin"
printf '\x00' | run dd of="$output/altered.bin" bs=1 count=1 conv=notrunc status=none
size=$(stat -c %s "$output/instructions.bin")
run head -c "$((size - 1))" "$output/instructions.bin" > "$output/truncated.bin"
run cp "$output/instructions.bin" "$output/overlong.bin"
printf '\x00' >> "$output/overlong.bin"
for kind in altered truncated overlong; do
    status=0
    run timeout 30 "$output/native-check.elf" "$output/$kind.bin" \
        > "$output/$kind.lean" 2> "$output/$kind-results.txt" || status=$?
    printf '%u\n' "$status" > "$output/$kind.exit"
    if [[ $status -ne 2 || -s "$output/$kind.lean" ||
        $(< "$output/$kind-results.txt") != 'Final ELF section extraction differs from executed bytes' ]]; then
        echo "Expected pre-probe ELF identity rejection 2 with empty Lean output: $kind, got $status" >&2
        exit 1
    fi
done
cat > "$output/scope.txt" <<'SCOPE'
Finite owned Linux x86-64 native/model conformance for low32 register CMP/TEST,
ENDBR64 under the CET/IBT/shadow-stack-disabled target profile, and the exact
NOPs 90,6690,0f1f00,0f1f4000,0f1f440000. Multi-byte NOP support is assumed.
One final linked ELF section contains 150 positive windows and eleven safe
synthetic mutations. Every window directly jumps to capture after its bytes.
Before any probe or Lean output, the extracted section (including capture
jumps and mutations) must equal the actual linked executable section exactly.
Changed, short and overlong extractions must fail with exit2 and empty stdout.

The independent C contract checks all sixteen complete 64-bit GPRs and all
captured effective before/after RFLAGS. CMP uses mathematical low32 subtraction,
unsigned comparison, signed integer difference range, low-nibble borrow and
low-byte population count. TEST computes low32 set intersection, CF/OF0 and
PF/ZF/SF; only AF is unconstrained. All other flags and every GPR must survive.
ENDBR and NOP preserve every captured flag and register. Input flag requests
alternate 0x202/0xed7; the oracle uses actual effective pre-instruction flags,
not an assumption that arbitrary RFLAGS can be installed by user-mode POPFQ.

There are 1,500 positive snapshots: 960 CMP (39/3b), 480 TEST (85), 60 ENDBR/NOP.
For each of the three opcode forms, 48 windows include all sixteen registers
on both sides, all sixteen self aliases, eight unprefixed pairs, and every
non-W REX40..47, including ignored X and every R/B bank. Ten input profiles
include high-half differences, equal low32 but different high64, zero, unsigned
borrow, both signed overflow directions, nibble borrow and even/odd parity.
The NOP address bases/indexes include unmapped and noncanonical values. Those
values must not be dereferenced. Arbitrary modeled RSP is safe: the harness
uses only RIP-relative loads/stores and jumps while it is installed, then
restores the host RSP before PUSHFQ. The harness is single-threaded/non-PIE.

Generated replay applies public Sequential.step to the actual bytes, actual
GPRs, effective before flags and captured after flags. Only TEST uses captured
AF as a choice witness; the parent generic theorem covers both AF choices.
Each generated snapshot requests a kernel-checked rfl equality with linked RIP
and empty operand-read footprint, followed by the project transitive axiom
audit. Replay memory exposes only instruction bytes: no operand memory is
accessible. The requested empty read footprint is not a physical memory trace.
Replay/audit is pending unless kernel-check.exit records 0.

The eleven safe register-only mutations must fail the independent oracle:
CMP wrong width/direction/register, SUB writing a register, cleared CMP carry,
TEST wrong width/register, AND writing a register, set TEST carry, NOP register
write and NOP flag change. Each failure identifies its input profile in logs;
mutations are excluded from positive Lean replay. No malformed or unsafe
decode-negative instruction is executed natively. No universal ISA/CPU/OS,
CET-enabled behavior, faults, timing, speculation, asynchronous interference,
concurrent visibility, physical TSO or whole-kernel safety claim is made.
SCOPE
run flock /tmp/edsl-lean-build.lock lake build EDSL.X86.Sequential.CFGDiscovery \
    EDSL.X86.Sequential.ConditionFlags EDSL.X86.Sequential.Return EDSL.Sum32.Artifact EDSL.Audit \
    > "$output/build.log" 2>&1
for leaf in SequentialCompare32 SequentialPadding; do
    status=0
    run flock /tmp/edsl-lean-build.lock lake env lean -DwarningAsError=true \
        "tests/$leaf.lean" > "$output/$leaf.log" 2>&1 || status=$?
    printf '%u\n' "$status" > "$output/$leaf.exit"
    cat "$output/$leaf.log"
    if [[ $status -ne 0 ]]; then exit "$status"; fi
done
status=0
run flock /tmp/edsl-lean-build.lock lake env lean -DwarningAsError=true \
    "$output/NativeSequentialCompare32.lean" > "$output/kernel-check.txt" 2>&1 || status=$?
printf '%u\n' "$status" > "$output/kernel-check.exit"
cat "$output/kernel-check.txt"
if [[ $status -ne 0 ]]; then exit "$status"; fi
run sha256sum -c "$output/MODEL-SOURCES.sha256" > "$output/source-stability.log" 2>&1
echo 'Sequential CMP32/TEST32/ENDBR/NOP regression, native contract, kernel replay/audit passed'
run sha256sum "$output/native-check.elf" "$output/instructions.bin" "$output/NativeSequentialCompare32.lean" \
    "$output/native-results.txt" "$output/scope.txt" > "$output/ARTIFACTS.sha256"
