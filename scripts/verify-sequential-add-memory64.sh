#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail
native_only=false
case ${1-} in
    '') [[ $# -eq 0 ]] || exit 2 ;;
    --native-only) [[ $# -eq 1 ]] || exit 2; native_only=true ;;
    *) echo 'Usage: verify-sequential-add-memory64.sh [--native-only]' >&2; exit 2 ;;
esac
if [[ $(uname -sm) != 'Linux x86_64' ]]; then
    echo 'Sequential memory-source ADD64 native conformance requires Linux x86_64' >&2
    exit 2
fi
cd "$(dirname "${BASH_SOURCE[0]}")/.."
source_root=$PWD
output=${EDSL_ADD_MEMORY64_OUTPUT:-artifacts/sequential-add-memory64}
mkdir -p "$output"
output=$(realpath "$output")
compiler=${EDSL_CLANG:-clang-18}
lean_root=${EDSL_ADD_MEMORY64_LEAN_ROOT:-$source_root}
native_status='NOT RUN'
model_status='NOT RUN'
: > "$output/commands.txt"
printf 'NOT RUN\n' > "$output/kernel-check.txt"
sha256sum fixtures/sequential-add-memory64-check.c fixtures/sequential-add-memory64-probe.S \
    scripts/verify-sequential-add-memory64.sh > "$output/source-SHA256SUMS"
cp fixtures/sequential-add-memory64-check.c "$output/source-check.c"
cp fixtures/sequential-add-memory64-probe.S "$output/source-probe.S"
cp scripts/verify-sequential-add-memory64.sh "$output/source-runner.sh"
finalize() {
    local result=$?
    if ! sha256sum -c "$output/source-SHA256SUMS" > "$output/source-integrity.txt" 2>&1; then result=1; fi
    trap - EXIT
    printf 'native=%s\nmodel_replay_both_AF=%s\nuniversal_ISA_CPU_OS=NOT RUN (outside scope)\nexit=%s\n' \
        "$native_status" "$model_status" "$result" > "$output/status.txt"
    (cd "$output"; find . -maxdepth 1 -type f ! -name SHA256SUMS -print0 | \
        LC_ALL=C sort -z | xargs -0 sha256sum) > "$output/SHA256SUMS"
    exit "$result"
}
trap finalize EXIT
run() {
    printf '%q ' "$@" >> "$output/commands.txt"
    printf '\n' >> "$output/commands.txt"
    "$@"
}
{
    printf 'source_root=%s\noutput=%s\nlean_root=%s\nnative_only=%s\nPATH=%s\n' \
        "$source_root" "$output" "$lean_root" "$native_only" "$PATH"
    for tool in "$compiler" objcopy objdump readelf ld timeout sha256sum flock; do
        resolved=$(command -v "$tool")
        printf '%s=%s -> %s\n' "$tool" "$resolved" "$(realpath "$resolved")"
    done
} > "$output/environment.txt"
if git rev-parse --show-toplevel > /dev/null 2>&1; then
    git rev-parse HEAD > "$output/source-git.txt"
    git status --short >> "$output/source-git.txt"
else
    printf 'No Git metadata; exact native sources recorded by SHA and copies.\n' > "$output/source-git.txt"
fi
run "$compiler" --version > "$output/compiler.txt"
run uname -srmo > "$output/platform.txt"
run date -u +%FT%TZ > "$output/time.txt"
run lscpu > "$output/cpu.txt"
run objcopy --version > "$output/objcopy.txt"
run objdump --version > "$output/objdump.txt"
run readelf --version > "$output/readelf.txt"
run ld --version > "$output/linker.txt"
cat > "$output/scope.txt" <<'SCOPE'
Finite owned ordinary Linux x86-64 user-mode memory-source ADD64 conformance.
64 positive windows, 12 profiles each (768 CPU observations), with single
REX.W 48..4f, opcode 03 and admitted mod00 plain/indexed addressing. Exact GCC
48 03 14 c7 and Clang 48 03 04 cf scalar sum64 windows are included. Coverage:
all 16 destinations including RSP, all 12 admitted plain bases, every scale and
R/B/X combination, ignored X without SIB, RSP/R12 bases, RBP/R13/R12 indices,
base/index/destination aliases and high64 indices with compensating bases.
Overlapping base/index operands solve the real EA equation modulo 2^64;
constrained destination inputs and all other GPRs are captured from the CPU.
No GPR carries a hidden recovery pointer. Global capture is single-threaded.
Each case fills and snapshots an entire owned padded data page, then makes it
read-only between inaccessible guard pages. Positive targets include unaligned
qwords and the aligned final qword immediately before the guard. C compares all
16 captured GPRs, complete RFLAGS and the entire page snapshot. It independently
uses a 65-bit unsigned sum, nibble carry, sign comparisons and low-byte population
for the six arithmetic flags. Requested arithmetic flags, DF and ID vary; actual
effective flags are captured and checked. Every other flag must survive ADD.
RIP-relative MOV capture restores the real CALL stack before PUSHFQ, and saved
host flags/DF and callee-saved registers before returning to C. No stack access
occurs while arbitrary RSP is installed. Capture JMPs preserve ADD flags.
The supplied extraction is compared with the complete final executable ELF
section (including harness, positive/negative windows and capture jumps) before
any probe or stdout. Input files are never executable targets. Altered,
truncated and extended extractions must return 2, the exact recorded diagnostic,
and empty Lean stdout. No changed code is executed.
Nine safe owned mutants must fail their named C-oracle categories: narrow32
sum/load, narrow32 load with full64 sum, wrong operation/destination, wrong
scale/EA within padded mapped memory, omitted ADD flags, cleared carry and
changed nonarithmetic flag (DF). No intentional invalid-memory mutant runs;
signals/timeouts are failures, never semantic counterexamples.
Generated Lean records actual instruction bytes, RIP, all initial/final GPRs,
effective flags, EA, literal source bytes from the actual snapshot, next PC and
one successful DATA8 read. Public Sequential.step is checked with rfl for both
AF choices followed by #audit_edsl. Full modeled RAM and both permission maps
must equal the initial memory. The sparse replay has exactly the instruction
and eight source bytes accessible, no writable bytes. C additionally checks the
entire native owned page. Operand footprints are independent contracts, not
hardware access traces. Negative windows are excluded from positive replay.
Status.txt records whether replay actually ran. --native-only leaves model
replay NOT RUN and does not establish model conformance. Default success requires
completed replay and the transitive dependency audit. Optional
EDSL_ADD_MEMORY64_LEAN_ROOT selects an existing checkout/cache for replay;
Lean/lake come from the caller's PATH, LEAN_NUM_THREADS=1, under the shared lock.
No displacements, RIP-relative/no-base/no-index operand forms, opcode 01 memory
destinations, LOCK, repeated prefixes or W=0 are positive admitted encodings.
No universal ISA/CPU/whole-OS or source-preservation claim; no fault delivery,
timing, speculation, concurrency, atomicity or asynchronous-interference claim.
The environment uses ordinary selected user flags with alignment checking and
CET disabled. Bootstrap compiler gates are distinct from these native checks.
SCOPE
# GNU2x is the accepted GNU23 spelling on both the Clang18 and GCC12 hosts.
common=(-v -O2 -Wall -Wextra -Werror -fno-pie -fcf-protection=none -fno-lto)
run "$compiler" -std=gnu2x "${common[@]}" -c fixtures/sequential-add-memory64-check.c \
    -o "$output/check.o" > "$output/compile-check.txt" 2>&1
run "$compiler" "${common[@]}" -c fixtures/sequential-add-memory64-probe.S \
    -o "$output/probe.o" > "$output/compile-probe.txt" 2>&1
run "$compiler" -v -fno-lto -no-pie -fcf-protection=none '-Wl,--build-id=none,-z,noexecstack' \
    "$output/check.o" "$output/probe.o" -o "$output/native-check.elf" > "$output/link.txt" 2>&1
for object in check.o probe.o native-check.elf; do
    run readelf -h -l -S -s -r -W "$output/$object" > "$output/$object.readelf.txt"
    run objdump -drw "$output/$object" > "$output/$object.disassembly.txt"
done
run objcopy --dump-section ".edsl_add_memory64=$output/instructions.bin" "$output/native-check.elf"
run objdump -d -j .edsl_add_memory64 "$output/native-check.elf" > "$output/disassembly.txt"
native_status='FAILED'
run timeout 30 "$output/native-check.elf" "$output/instructions.bin" \
    > "$output/NativeSequentialAddMemory64.lean" 2> "$output/native-results.txt"
cat "$output/native-results.txt"
printf 'Final ELF section extraction differs from executed bytes\n' > "$output/rejection-diagnostic.txt"
cp "$output/instructions.bin" "$output/altered.bin"
printf '\x00' | dd of="$output/altered.bin" bs=1 count=1 conv=notrunc status=none
size=$(stat -c %s "$output/instructions.bin")
head -c "$((size - 1))" "$output/instructions.bin" > "$output/truncated.bin"
cp "$output/instructions.bin" "$output/extended.bin"
printf '\x00' >> "$output/extended.bin"
for mutation in altered truncated extended; do
    status=0
    run timeout 30 "$output/native-check.elf" "$output/$mutation.bin" \
        > "$output/$mutation.lean" 2> "$output/$mutation-results.txt" || status=$?
    printf '%s\n' "$status" > "$output/$mutation.status"
    if [[ $status -ne 2 || -s "$output/$mutation.lean" ]] || \
        ! cmp -s "$output/rejection-diagnostic.txt" "$output/$mutation-results.txt"; then
        echo "Expected pre-probe $mutation extraction rejection 2, exact diagnostic, empty Lean stdout; got $status" >&2
        exit 1
    fi
done
native_status='PASS'
if "$native_only"; then
    echo 'Native-only ADD64 memory contracts passed; model replay and universal claims NOT RUN'
    exit 0
fi
# Reuse a checkout's build cache; never create an uncached duplicate project.
if [[ ! -f "$lean_root/lean-toolchain" || ! -f "$lean_root/lakefile.lean" ]]; then
    echo 'Native PASS; model replay NOT RUN: select an existing Lean checkout via EDSL_ADD_MEMORY64_LEAN_ROOT' >&2
    exit 2
fi
export LEAN_NUM_THREADS=1
model_status=FAILED
{
    printf 'LEAN_NUM_THREADS=%s\n' "$LEAN_NUM_THREADS"
    for tool in lean lake; do
        resolved=$(command -v "$tool")
        printf '%s=%s -> %s\n' "$tool" "$resolved" "$(realpath "$resolved")"
    done
} >> "$output/environment.txt"
(
    cd "$lean_root"
    run lean --version > "$output/lean.txt"
    run lake --version > "$output/lake.txt"
    { printf '%s\0' lean-toolchain lakefile.lean; find EDSL -type f -name '*.lean' -print0; } | \
        LC_ALL=C sort -z | xargs -0 sha256sum > "$output/model-source-SHA256SUMS"
    exec 9>/tmp/edsl-lean-build.lock
    run flock 9
    run lake build EDSL.X86.Sequential.Machine EDSL.Audit > "$output/model-build.txt" 2>&1
    run lake env lean -DwarningAsError=true "$output/NativeSequentialAddMemory64.lean" \
        > "$output/kernel-check.txt" 2>&1
    sha256sum -c "$output/model-source-SHA256SUMS" > "$output/model-source-integrity.txt"
)
cat "$output/kernel-check.txt"
model_status='PASS'
echo 'Sequential ADD64 memory native contracts and actual-step kernel replay for both AF choices passed'
