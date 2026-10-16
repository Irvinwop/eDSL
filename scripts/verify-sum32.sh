#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail

if [[ $(uname -sm) != 'Linux x86_64' ]]; then
    echo 'sum32 native evidence requires Linux x86_64' >&2
    exit 2
fi
cd "$(dirname "${BASH_SOURCE[0]}")/.."
output=artifacts/sum32-fixtures
mkdir -p "$output"
gcc=${EDSL_GCC:-gcc-13}
clang=${EDSL_CLANG:-clang-18}
if [[ $("$gcc" -dumpversion) != 13 ]] ||
    ! "$clang" --version | head -n 1 | rg -q 'clang version 18\.'; then
    echo 'Unsupported compiler profile: this evidence selects GCC 13 and Clang 18' >&2
    exit 2
fi
uname -srmo > "$output/platform.txt"
ld --version > "$output/linker.txt"
objcopy --version > "$output/objcopy.txt"
objdump --version > "$output/objdump.txt"
readelf --version > "$output/readelf.txt"
cat > "$output/scope.txt" <<'EOF'
Literal raw/ELF certificates use the shared Lean sum32 checker and correctness
theorem. Its all-choice function contract is conditional on current code,
input, return-stack and environmental/resource preconditions. Native observations
remain separate evidence; loading a file does not establish runtime admission.
Selected x86-64 SysV leaf windows: GCC13 pointer/count -Os -fno-ivopts and
Clang18 index -Oz, scalar, no CET, no LTO. Other compilers/optimization profiles
are outside this evidence selection. GNU23 is named gnu2x by GCC13.
Each function.elf is a final linked ET_EXEC callable-function container,
without process startup. function.bin is its complete .text, extracted AFTER
linking. Native checks mmap those exact file bytes RX and call through an
external SysV assembly trampoline. No object-only code is executed as evidence.
The loaded window is position independent within this selected no-relocation
leaf profile. Relocation/table rejection and semantic proof belong to Lean.
Tests cover full RAX zero extension, six callee-saved registers, DF, practical
return/stack behavior, null/guard zero inputs, closed algebraic sums, modular
wrap, and readonly data ending at a guard page. They do not establish total
correctness, speculative behavior, a concurrent ISA backend, or C correctness.
EOF

prepare() {
    local compiler=$1 dialect=$2 name=$3 symbol=$4
    shift 4
    local directory="$output/$name"
    mkdir -p "$directory"
    "$compiler" --version > "$directory/compiler.txt"
    "$compiler" -dumpmachine > "$directory/target.txt"
    local compile_args=("-std=$dialect" "$@" -Wall -Wextra -Werror
        -fno-unroll-loops -ffunction-sections -fcf-protection=none -fno-lto
        -c fixtures/sum32.c -o "$directory/function.o")
    local link_args=(-m elf_x86_64 --build-id=none --gc-sections -z noexecstack
        -e "$symbol" -Ttext=0x401000 -o "$directory/function.elf" "$directory/function.o")
    local harness_args=("-std=$dialect" -O2 -Wall -Wextra -Werror
        -fcf-protection=none -fno-lto fixtures/sum32-check.c fixtures/sum32-trampoline.S
        -o "$directory/native-check")
    {
        printf '%q ' "$compiler" "${compile_args[@]}"; printf '\n'
        printf '%q ' ld "${link_args[@]}"; printf '\n'
        printf '%q ' objcopy --dump-section ".text=$directory/function.bin" "$directory/function.elf"; printf '\n'
        printf '%q ' "$compiler" "${harness_args[@]}"; printf '\n'
    } > "$directory/arguments.txt"
    "$compiler" "${compile_args[@]}"
    ld "${link_args[@]}"
    objcopy --dump-section ".text=$directory/function.bin" "$directory/function.elf"
    LC_ALL=C readelf -rW "$directory/function.elf" > "$directory/relocations.txt"
    if ! rg -q '^There are no relocations in this file\.' "$directory/relocations.txt"; then
        echo "Unsupported relocated native window: $name" >&2
        exit 2
    fi
    objdump -drw -Mintel "$directory/function.elf" > "$directory/disassembly.txt"
    readelf -h -l -s -W "$directory/function.elf" > "$directory/elf.txt"
    od -An -v -tx1 "$directory/function.bin" > "$directory/bytes.txt"
    "$compiler" "${harness_args[@]}"
    timeout 15 "$directory/native-check" "$directory/function.bin" > "$directory/native-results.txt" 2>&1
    cat "$directory/native-results.txt"
    sha256sum fixtures/sum32.c fixtures/sum32-check.c fixtures/sum32-trampoline.S \
        scripts/verify-sum32.sh "$directory/function.o" "$directory/function.elf" \
        "$directory/function.bin" "$directory/native-check" "$directory/native-results.txt" \
        "$directory/compiler.txt" "$directory/arguments.txt" > "$directory/SHA256SUMS"
}

# These native operations are independent of the shared Lean proof lock.
prepare "$gcc" gnu2x gcc sum32_ptr -Os -fno-ivopts -fno-tree-vectorize -fno-tree-slp-vectorize
prepare "$clang" gnu23 clang sum32_index -Oz -fno-vectorize -fno-slp-vectorize
if cmp -s "$output/gcc/function.bin" "$output/clang/function.bin"; then
    echo 'Expected two distinct final linked windows' >&2
    exit 1
fi

# A different initialization and commuting updates exercise the structural
# checker beyond the two compiler windows. This is an owned positive fixture.
variant="$output/variant"
mkdir -p "$variant"
cat > "$variant/function.S" <<'EOF'
/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
.text
.globl edsl_sum32_variant
.type edsl_sum32_variant,@function
edsl_sum32_variant:
    xorl %ecx, %ecx
    movl $0, %eax
    xorl %ecx, %ecx
1:
    testq %rsi, %rsi
    je 2f
    addl (%rdi), %eax
    addq $4, %rdi
    decq %rsi
    jmp 1b
2:
    ret
.size edsl_sum32_variant,.-edsl_sum32_variant
.section .note.GNU-stack,"",@progbits
EOF
"$clang" -c "$variant/function.S" -o "$variant/function.o"
ld -m elf_x86_64 --build-id=none -z noexecstack -e edsl_sum32_variant -Ttext=0x401000 \
    -o "$variant/function.elf" "$variant/function.o"
objcopy --dump-section ".text=$variant/function.bin" "$variant/function.elf"
timeout 15 "$output/gcc/native-check" "$variant/function.bin" > "$variant/native-results.txt" 2>&1
cat "$variant/native-results.txt"

lean_locked() {
    flock /tmp/edsl-lean-build.lock "$@"
}
lean_locked lake build edsl-certify-sum32
lean_locked lake env lean -DwarningAsError=true tests/Sum32Artifact.lean
certifier=.lake/build/bin/edsl-certify-sum32

certify() {
    local directory=$1
    # The certifier locks its kernel subprocess itself; no outer lock here.
    lake env "$certifier" "$directory/function.bin" "$directory/Certificate.lean" \
        > "$directory/certificate-check.txt" 2>&1
    lake env "$certifier" --elf "$directory/function.elf" "$directory/ELFCertificate.lean" \
        > "$directory/elf-certificate-check.txt" 2>&1
    cat "$directory/certificate-check.txt" "$directory/elf-certificate-check.txt"
    sha256sum "$directory/function.bin" "$directory/function.elf" \
        "$directory/Certificate.lean" "$directory/ELFCertificate.lean" \
        "$directory/native-results.txt" > "$directory/certified-SHA256SUMS"
}
certify "$output/gcc"
certify "$output/clang"
certify "$variant"

reject() {
    local candidate=$1 mode=${2:-raw} expected=${3:-3}
    local arguments=("$candidate" "$candidate.lean")
    if [[ $mode == elf ]]; then arguments=(--elf "${arguments[@]}"); fi
    local status=0
    lake env "$certifier" "${arguments[@]}" > "$candidate.certificate-log.txt" 2>&1 || status=$?
    if [[ $status -ne $expected || -e $candidate.lean ]]; then
        cat "$candidate.certificate-log.txt"
        echo "Expected unverified admission with status $expected and no certificate: $candidate (got $status)" >&2
        exit 1
    fi
}

# Synthetic negative variants belong to this project. Faulting overreads run
# only in isolated child processes, with core dumps disabled by the harness.
negative="$output/rejections"
mkdir -p "$negative"
for mutation in result stride overread; do
    define=-DEDSL_SUM32_BIAS=1
    case "$mutation" in
        stride) define=-DEDSL_SUM32_STRIDE=2 ;;
        overread) define=-DEDSL_SUM32_OVERREAD=1 ;;
    esac
    target="$negative/$mutation"
    local_args=(-std=gnu2x -Os -fno-ivopts -fno-tree-vectorize -fno-tree-slp-vectorize
        -fno-unroll-loops -ffunction-sections -fcf-protection=none -fno-lto
        -Wall -Wextra -Werror "$define" -c fixtures/sum32.c -o "$target.o")
    {
        printf '%q ' "$gcc" "${local_args[@]}"; printf '\n'
        printf '%q ' ld -m elf_x86_64 --build-id=none --gc-sections -z noexecstack \
            -e sum32_ptr -Ttext=0x401000 -o "$target.elf" "$target.o"; printf '\n'
    } > "$target.arguments.txt"
    "$gcc" "${local_args[@]}"
    ld -m elf_x86_64 --build-id=none --gc-sections -z noexecstack \
        -e sum32_ptr -Ttext=0x401000 -o "$target.elf" "$target.o"
    objcopy --dump-section ".text=$target.bin" "$target.elf"
    timeout 15 "$output/gcc/native-check" --expect-reject "$target.bin" > "$target.native.txt" 2>&1
    cat "$target.native.txt"
    reject "$target.bin"
    reject "$target.elf" elf
done
size=$(wc -c < "$output/gcc/function.bin")
head -c "$((size - 1))" "$output/gcc/function.bin" > "$negative/truncated.bin"
head -c 64 "$output/gcc/function.elf" > "$negative/truncated.elf"
reject "$negative/truncated.bin"
reject "$negative/truncated.elf" elf 4
head -c 3 "$output/gcc/function.bin" > "$negative/incomplete-instruction.bin"
reject "$negative/incomplete-instruction.bin" raw 4
: > "$negative/empty.bin"
reject "$negative/empty.bin" raw 4
sha256sum "$negative"/*.o "$negative"/*.elf "$negative"/*.bin \
    "$negative"/*.native.txt "$negative"/*.arguments.txt > "$negative/SHA256SUMS"
printf 'Certified and observed two compiler windows and a distinct MOV/XOR/reordered-update variant through one sum32 checker.\n'
printf 'Owned result/stride/overread mutations, truncation and empty input artifacts remain unverified.\n'
