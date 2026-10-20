#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
if [[ $(uname -sm) != 'Linux x86_64' ]]; then
    echo 'Store-return32 native evidence requires Linux x86_64' >&2
    exit 2
fi
output=artifacts/store-return32
mkdir -p "$output"
gcc=${EDSL_GCC:-gcc-13}
clang=${EDSL_CLANG:-clang-18}
if [[ $("$gcc" -dumpversion) != 13 ]] ||
    ! "$clang" --version | head -n 1 | grep -q 'clang version 18\.'; then
    echo 'Store-return32 evidence selects GCC13 and Clang18' >&2
    exit 2
fi
uname -srmo > "$output/platform.txt"
ld --version > "$output/linker.txt"
objcopy --version > "$output/objcopy.txt"

prepare() {
    local compiler=$1 dialect=$2 name=$3 symbol=$4 source=$5
    shift 5
    local directory="$output/$name"
    mkdir -p "$directory"
    "$compiler" --version > "$directory/compiler.txt"
    local compile=("-std=$dialect" -Wall -Wextra -Werror -fno-lto
        -fcf-protection=none -ffunction-sections "$@" -c "$source" -o "$directory/function.o")
    if [[ $source == *.S ]]; then
        compile=(-c "$source" -o "$directory/function.o")
    fi
    local link=(-m elf_x86_64 --build-id=none --gc-sections -z noexecstack
        -e "$symbol" -Ttext=0x401000 -o "$directory/function.elf" "$directory/function.o")
    {
        printf '%q ' "$compiler" "${compile[@]}"; printf '\n'
        printf '%q ' ld "${link[@]}"; printf '\n'
    } > "$directory/arguments.txt"
    "$compiler" "${compile[@]}"
    ld "${link[@]}"
    objcopy --dump-section ".text=$directory/function.bin" "$directory/function.elf"
    readelf -h -l -s -r -W "$directory/function.elf" > "$directory/elf.txt"
    readelf -rW "$directory/function.elf" > "$directory/relocations.txt"
    if ! grep -q '^There are no relocations in this file\.' "$directory/relocations.txt"; then
        echo "Relocated native window is outside this evidence profile: $name" >&2
        exit 2
    fi
    objdump -d -Mintel "$directory/function.elf" > "$directory/disassembly.txt"
}

prepare "$gcc" gnu2x gcc store_return32 fixtures/store-return.c -Os \
    -fno-tree-vectorize -fno-tree-slp-vectorize -fno-unroll-loops
prepare "$clang" gnu23 clang store_return32 fixtures/store-return.c -Oz \
    -fno-vectorize -fno-slp-vectorize -fno-unroll-loops
prepare "$clang" gnu23 copied store_return32_copied fixtures/store-return-copy.S
# A valid compiler output may lie outside the supported instruction profile.
prepare "$gcc" gnu2x unsupported-oz store_return32 fixtures/store-return.c -Oz \
    -fno-tree-vectorize -fno-tree-slp-vectorize -fno-unroll-loops
if cmp -s "$output/gcc/function.bin" "$output/clang/function.bin"; then
    echo 'Selected compiler profiles no longer exercise two distinct orderings' >&2
    exit 2
fi

"$clang" -std=gnu23 -O2 -Wall -Wextra -Werror -fcf-protection=none -fno-lto \
    fixtures/store-return-check.c fixtures/cfg/trampoline.S -o "$output/native-check"
timeout 20 "$output/native-check" "$output/gcc/function.bin" \
    "$output/clang/function.bin" "$output/copied/function.bin" > "$output/native.txt" 2>&1
cat "$output/native.txt"

flock /tmp/edsl-lean-build.lock lake build edsl-certify-store-return32
certifier=(lake env .lake/build/bin/edsl-certify-store-return32)
for name in gcc clang copied; do
    "${certifier[@]}" "$output/$name/function.bin" "$output/$name/Raw.lean" \
        > "$output/$name/raw-check.txt" 2>&1
    "${certifier[@]}" --elf "$output/$name/function.elf" "$output/$name/ELF.lean" \
        > "$output/$name/elf-check.txt" 2>&1
done

expect_status() {
    local expected=$1 name=$2
    shift 2
    local status=0
    "$@" > "$output/$name.txt" 2>&1 || status=$?
    if [[ $status -ne $expected ]]; then
        cat "$output/$name.txt"
        echo "Unexpected certifier status for $name: wanted $expected, got $status" >&2
        exit 1
    fi
}
expect_status 3 unsupported-oz/raw "${certifier[@]}" "$output/unsupported-oz/function.bin" \
    "$output/unsupported-oz/Raw.lean"
expect_status 3 unsupported-oz/elf "${certifier[@]}" --elf "$output/unsupported-oz/function.elf" \
    "$output/unsupported-oz/ELF.lean"
printf '\211\370\211\067\303' > "$output/truncated-pointer.bin"
printf '\211\067\110\215\107\004\303' > "$output/wrong-pointer.bin"
cp "$output/gcc/function.bin" "$output/trailing.bin"
printf '\303' >> "$output/trailing.bin"
: > "$output/empty.bin"
expect_status 3 truncated-pointer "${certifier[@]}" "$output/truncated-pointer.bin" "$output/Truncated.lean"
expect_status 3 wrong-pointer "${certifier[@]}" "$output/wrong-pointer.bin" "$output/Wrong.lean"
expect_status 3 trailing "${certifier[@]}" "$output/trailing.bin" "$output/Trailing.lean"
expect_status 4 empty "${certifier[@]}" "$output/empty.bin" "$output/Empty.lean"
expect_status 4 empty-elf "${certifier[@]}" --elf "$output/empty.bin" "$output/EmptyELF.lean"
cp "$output/gcc/function.elf" "$output/altered.elf"
printf '\000' | dd of="$output/altered.elf" bs=1 count=1 conv=notrunc status=none
expect_status 4 altered-elf "${certifier[@]}" --elf "$output/altered.elf" "$output/AlteredELF.lean"
expect_status 2 missing-elf-input "${certifier[@]}" --elf "$output/MissingELF.lean"
# A valid ELF with a large zero-filled segment exceeds our admitted image
# profile; rejection must not label the container malformed.
cat > "$output/large-bss.S" <<'ASSEMBLY'
.section .bss
.zero 65537
.section .note.GNU-stack,"",@progbits
ASSEMBLY
"$clang" -c "$output/large-bss.S" -o "$output/large-bss.o"
ld -m elf_x86_64 --build-id=none -z noexecstack -e store_return32 -Ttext=0x401000 \
    -o "$output/large-bss.elf" "$output/gcc/function.o" "$output/large-bss.o"
readelf -lW "$output/large-bss.elf" > "$output/large-bss-headers.txt"
expect_status 3 large-bss "${certifier[@]}" --elf "$output/large-bss.elf" "$output/LargeBSS.lean"

cat > "$output/scope.txt" <<'SCOPE'
Owned Linux x86-64 callable-function evidence for GNU23 GCC13 -Os (spelled
gnu2x), Clang18 -Oz, and a separate copied-RAX assembly store. Exact final
linked .text files are both certified as raw bytes and executed natively.
Full restricted ELF containers receive separate literal parser/loader and
functional certificates. The function contract universally proves low32
store, full returned pointer, RAM/permission/ABI frames, exactly3 instructions
and the original stack8 operand read for all admitted AF choices. Managed
proofs retain the actual checked owner update/current OS history and loans.
Independent native checks require pointers above4GiB, seven full64 arguments,
six aligned/unaligned/page-edge positions and two fills:252 calls across three
positive artifacts. They observe every data-page byte, full returned pointer,
saved registers, stack balance/canary and DF. Six owned semantic mutants fail,
including returned-pointer truncation and pointer+4. Other RFLAGS bits are not
independently observed. Ordinary RAM and disabled alignment checking/CET are
selected environmental assumptions. Observations are finite; they establish
no source preservation, universal CPU/kernel conformance, concurrency, timing
or whole-program/whole-OS result. The compiler's GCC13 -Oz register-XCHG output
is valid native code outside this direct shape API; verify-store-return-xchg.sh
checks it through the independent client proof and general grader. Raw
windows must match in full; extra trailing bytes reject. ELF selects the first
RET-terminated decoded entry window within64 bytes/32 instructions, without
skipping unsupported code. No certificate filename alone establishes success.
The existing write32 registered grader leaves RAX unconstrained. A separate
storeReturn32 task grades proofs of the stronger result under the same present
domains and policies; this script exercises the direct certificate API only.
SCOPE
{
    sha256sum fixtures/store-return.c fixtures/store-return-copy.S fixtures/store-return-check.c \
        fixtures/cfg/trampoline.S scripts/verify-store-return32.sh Tools/Certify/StoreReturn32.lean \
        EDSL/StoreReturn32.lean EDSL/StoreReturn32/Model.lean EDSL/StoreReturn32/RawProof.lean \
        EDSL/StoreReturn32/Resources.lean EDSL/StoreReturn32/Artifact.lean lean-toolchain lakefile.lean
    find "$output" -type f ! -name SHA256SUMS -print0 | sort -z | xargs -0 sha256sum
} > "$output/SHA256SUMS"
echo 'Store-return32 compiler/assembly raw and ELF certificates and native contracts passed'
