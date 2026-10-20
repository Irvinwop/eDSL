#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
if [[ $(uname -sm) != 'Linux x86_64' ]]; then
    echo 'Clang counted-store native evidence requires Linux x86_64' >&2
    exit 2
fi
clang=${EDSL_CLANG:-clang-18}
output=artifacts/counted-store64-clang-native
mkdir -p "$output"
"$clang" --version > "$output/compiler.txt"
if ! grep -q 'clang version 18\.' "$output/compiler.txt"; then
    echo 'Clang counted-store native evidence selects Clang18' >&2
    exit 2
fi
uname -srmo > "$output/platform.txt"
ld --version > "$output/linker.txt"
objcopy --version > "$output/objcopy.txt"
compile=(-std=gnu2x -O1 -falign-loops=1 -Wall -Wextra -Werror -fno-lto
    -fcf-protection=none -ffunction-sections -c fixtures/counted-store64.c
    -o "$output/function.o")
link=(-m elf_x86_64 --build-id=none --gc-sections -z noexecstack
    -e publish_counted -Ttext=0x401000 -o "$output/function.elf" "$output/function.o")
observer=(-std=gnu2x -O2 -Wall -Wextra -Werror -fcf-protection=none -fno-lto
    fixtures/counted-store64-check.c fixtures/cfg/trampoline.S -o "$output/native-check")
{
    printf '%q ' "$clang" "${compile[@]}"; printf '\n'
    printf '%q ' ld "${link[@]}"; printf '\n'
    printf '%q ' "$clang" "${observer[@]}"; printf '\n'
} > "$output/arguments.txt"
"$clang" "${compile[@]}"
ld "${link[@]}"
objcopy --dump-section ".text=$output/function.bin" "$output/function.elf"
readelf -h -l -r -W "$output/function.elf" > "$output/elf.txt"
readelf -rW "$output/function.elf" > "$output/relocations.txt"
if ! grep -q '^There are no relocations in this file\.' "$output/relocations.txt"; then
    echo 'Relocated native window is outside this evidence profile' >&2
    exit 2
fi
objdump -d -Mintel "$output/function.elf" > "$output/disassembly.txt"
# Transparent identity gate for this compiler configuration, not a proof.
# A mismatching compiler output is unsupported, not evidence of a compiler bug.
expected=4889f04885d2740b48ffc048890748ffca75f5c3
actual=$(od -An -tx1 -v "$output/function.bin" | tr -d ' \n')
if [[ "$actual" != "$expected" ]]; then
    echo "Unsupported Clang counted-store byte shape: $actual" >&2
    exit 3
fi
"$clang" "${observer[@]}"
timeout 45 "$output/native-check" "$output/function.bin" > "$output/native.txt" 2>&1
cat "$output/native.txt"
cat > "$output/scope.txt" <<'SCOPE'
Owned Linux x86-64 counted-store native evidence: Clang18 GNU23 (gnu2x),
-O1 -falign-loops=1, LTO/CET disabled, explicit empty GNU asm count-register
barrier in the fixture. arguments.txt records the complete fixture compilation,
link and independent observer compilation commands.
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
in separate children with core dumps disabled. The unchanged independent harness
also checks six generic owned synthetic defects using GCC-shaped byte windows:
missing/narrow store, wrong iteration count, wrong increment, neighboring write,
and saved-register clobber. These are oracle checks, not mutations of this Clang
output. Each must fail the independent oracle. Timeout or an unexpected signal
is inconclusive and causes failure, not acceptance as a detected defect.
This assumes ordinary Linux/CPU RAM behavior with alignment checking/CET disabled;
it proves no whole-OS safety, concurrency, timing or unrestricted optimality.
SCOPE
{
    sha256sum fixtures/counted-store64.c fixtures/counted-store64-check.c \
        fixtures/cfg/trampoline.S scripts/verify-counted-store64-clang-native.sh
    find "$output" -type f ! -name SHA256SUMS -print0 | sort -z | xargs -0 sha256sum
} > "$output/SHA256SUMS"
echo 'Clang counted-store final-byte identity, native contract and generic owned-mutant checks passed'
