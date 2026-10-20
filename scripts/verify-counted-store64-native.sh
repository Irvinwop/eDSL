#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
if [[ $(uname -sm) != 'Linux x86_64' ]]; then
    echo 'Counted-store native evidence requires Linux x86_64' >&2
    exit 2
fi
gcc=${EDSL_GCC:-gcc-13}
if [[ $("$gcc" -dumpversion) != 13 ]]; then
    echo 'Counted-store native evidence selects GCC13' >&2
    exit 2
fi
output=artifacts/counted-store64-native
mkdir -p "$output"
"$gcc" --version > "$output/compiler.txt"
uname -srmo > "$output/platform.txt"
ld --version > "$output/linker.txt"
objcopy --version > "$output/objcopy.txt"
compile=(-std=gnu2x -Os -Wall -Wextra -Werror -fno-lto -fcf-protection=none
    -ffunction-sections -c fixtures/counted-store64.c -o "$output/function.o")
link=(-m elf_x86_64 --build-id=none --gc-sections -z noexecstack
    -e publish_counted -Ttext=0x401000 -o "$output/function.elf" "$output/function.o")
{
    printf '%q ' "$gcc" "${compile[@]}"; printf '\n'
    printf '%q ' ld "${link[@]}"; printf '\n'
} > "$output/arguments.txt"
"$gcc" "${compile[@]}"
ld "${link[@]}"
objcopy --dump-section ".text=$output/function.bin" "$output/function.elf"
readelf -h -l -r -W "$output/function.elf" > "$output/elf.txt"
readelf -rW "$output/function.elf" > "$output/relocations.txt"
if ! grep -q '^There are no relocations in this file\.' "$output/relocations.txt"; then
    echo 'Relocated native window is outside this evidence profile' >&2
    exit 2
fi
objdump -d -Mintel "$output/function.elf" > "$output/disassembly.txt"
# Transparent identity gate for this one compiler configuration, not a proof.
# A mismatching compiler output is unsupported, not evidence of a compiler bug.
expected=4889f04885d2740b48ffc048ffca488907ebf0c3
actual=$(od -An -tx1 -v "$output/function.bin" | tr -d ' \n')
if [[ "$actual" != "$expected" ]]; then
    echo "Unsupported counted-store byte shape: $actual" >&2
    exit 3
fi
"$gcc" -std=gnu2x -O2 -Wall -Wextra -Werror -fcf-protection=none -fno-lto \
    fixtures/counted-store64-check.c fixtures/cfg/trampoline.S -o "$output/native-check"
timeout 45 "$output/native-check" "$output/function.bin" > "$output/native.txt" 2>&1
cat "$output/native.txt"
cat > "$output/scope.txt" <<'SCOPE'
Owned Linux x86-64 counted-store native evidence: GCC13 GNU23 (gnu2x), -Os,
LTO/CET disabled, explicit empty GNU asm count-register barrier in the fixture.
The final linked ELF's entire .text is extracted and compared with a literal
20-byte identity gate, then those bytes are executed. This script supplies
finite native observations; it does not claim a Lean proof or source preservation.
The independent closed-form oracle checks full64 RAX = argument + count modulo64,
target = old value when count0 and target = RAX otherwise, and every data-page
byte outside the eight-byte target. There are 504 calls: seven arguments,
six practical counts {0,1,2,3,31,257}, six aligned/unaligned/page-edge locations
above4GiB, and two distinct old values. Full64 counts near UINT64_MAX are not
executed. The external SysV observer checks saved registers, stack balance/canary
and DF. It does not independently observe the other nonarithmetic flags.
Data/code mappings have inaccessible neighboring guard pages; owned mutants run
in separate children with core dumps disabled. Six owned synthetic defects
(missing/narrow store, wrong iteration count, wrong increment, neighboring write,
saved-register clobber) must fail the independent oracle. Timeout or an unexpected
signal is inconclusive and causes failure, not acceptance as a detected defect.
This assumes ordinary Linux/CPU RAM behavior with alignment checking/CET disabled;
it proves no whole-OS safety, concurrency, timing or unrestricted optimality.
SCOPE
{
    sha256sum fixtures/counted-store64.c fixtures/counted-store64-check.c \
        fixtures/cfg/trampoline.S scripts/verify-counted-store64-native.sh
    find "$output" -type f ! -name SHA256SUMS -print0 | sort -z | xargs -0 sha256sum
} > "$output/SHA256SUMS"
echo 'Counted-store final-byte identity, native contract and owned-mutant checks passed'
