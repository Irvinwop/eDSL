#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail

if [[ $(uname -sm) != 'Linux x86_64' ]]; then
    echo 'Publication-client native integration requires Linux x86_64' >&2
    exit 2
fi
output=artifacts/futex-client-fixtures
mkdir -p "$output"
uname -sr > "$output/kernel.txt"
ld --version > "$output/linker.txt"
profile=publish-payload-wake
certifier=.lake/build/bin/edsl-certify-futex-client

lean_locked() {
    flock /tmp/edsl-lean-build.lock "$@"
}

prepare_native() {
    local compiler=$1 dialect=$2 name=$3
    local directory="$output/$name"
    mkdir -p "$directory"
    "$compiler" --version > "$directory/compiler.txt"
    local assemble_args=(-c fixtures/futex-publish.S -o "$directory/function.o")
    local link_args=(--build-id=none -e edsl_futex_publish_stub -Ttext=0x400000
        "$directory/function.o" -o "$directory/function.elf")
    # --unique preserves the publication section in the final native ELF. The
    # exact linked window is compared and certified after this final link too.
    local native_args=("-std=$dialect" -O2 -Wall -Wextra -Werror -fcf-protection=none -pthread
        fixtures/futex-client-check.c fixtures/futex-client-trampoline.S
        '-Wl,--unique=.text.edsl_futex_publish_stub' "$directory/function.o"
        -o "$directory/native-check")
    {
        printf '%q ' "$compiler" "${assemble_args[@]}"
        printf '\n'
        printf '%q ' ld "${link_args[@]}"
        printf '\n'
        printf '%q ' "$compiler" "${native_args[@]}"
        printf '\n'
    } > "$directory/arguments.txt"
    "$compiler" "${assemble_args[@]}"
    ld "${link_args[@]}"
    objcopy --only-section=.text -O binary "$directory/function.elf" "$directory/function.bin"
    "$compiler" "${native_args[@]}"
    objcopy --only-section=.text.edsl_futex_publish_stub -O binary \
        "$directory/native-check" "$directory/native-linked.bin"
    cmp "$directory/function.bin" "$directory/native-linked.bin"
    objdump -d "$directory/function.elf" > "$directory/disassembly.txt"
    readelf -h -l -s "$directory/function.elf" > "$directory/elf.txt"
    objdump -d "$directory/native-check" > "$directory/native-disassembly.txt"
    local status=0
    local race_args=()
    if [[ ${EDSL_FUTEX_CLIENT_RACE:-1} == 0 ]]; then race_args=(--no-race); fi
    timeout 15 "$directory/native-check" "${race_args[@]}" > "$directory/native-results.txt" 2>&1 || status=$?
    cat "$directory/native-results.txt"
    if [[ $status -eq 124 || $status -eq 3 ]]; then
        echo "INCONCLUSIVE: native publication observer reached its scheduling bound ($name)" >&2
        exit 3
    fi
    if [[ $status -ne 0 ]]; then
        echo "Native publication observer failed ($name, status $status)" >&2
        exit 1
    fi
}

# Native C/assembly work is independent of the shared proof build lock.
prepare_native "${EDSL_CLANG:-clang}" gnu23 clang
# GCC 13 names its GNU C23 dialect gnu2x.
prepare_native "${EDSL_GCC:-gcc}" gnu2x gcc
lean_locked lake env lean --version > "$output/lean.txt"
lean_locked lake build edsl-certify-futex-client
lean_locked lake env lean -DwarningAsError=true tests/FutexClientCertificate.lean

certify() {
    local directory=$1
    lean_locked lake env "$certifier" "$profile" "$directory/function.bin" \
        "$directory/Certificate.lean" > "$directory/certificate-check.txt" 2>&1
    lean_locked lake env "$certifier" --elf "$profile" "$directory/function.elf" \
        "$directory/ELFCertificate.lean" > "$directory/elf-certificate-check.txt" 2>&1
    lean_locked lake env "$certifier" "$profile" "$directory/native-linked.bin" \
        "$directory/NativeCertificate.lean" > "$directory/native-certificate-check.txt" 2>&1
    cat "$directory/certificate-check.txt" "$directory/elf-certificate-check.txt" \
        "$directory/native-certificate-check.txt"
    sha256sum fixtures/futex-publish.S fixtures/futex-client-trampoline.S fixtures/futex-client-check.c \
        "$directory/function.o" "$directory/function.elf" "$directory/function.bin" \
        "$directory/native-check" "$directory/native-linked.bin" "$directory/native-results.txt" \
        "$directory/Certificate.lean" "$directory/ELFCertificate.lean" \
        "$directory/NativeCertificate.lean" > "$directory/SHA256SUMS"
}
certify "$output/clang"
certify "$output/gcc"

reject() {
    local candidate=$1 mode=${2:-raw}
    local arguments=("$profile" "$candidate" "$candidate.lean")
    if [[ $mode == elf ]]; then arguments=(--elf "${arguments[@]}"); fi
    local status=0
    lean_locked lake env "$certifier" "${arguments[@]}" > "$candidate.log" 2>&1 || status=$?
    if [[ $status -ne 3 || -e $candidate.lean ]]; then
        cat "$candidate.log"
        echo "Expected admission rejection 3 with no certificate ($candidate), got $status" >&2
        exit 1
    fi
}

# Project-owned synthetic negatives are admitted nowhere and never run natively.
mkdir -p "$output/rejections"
for mutation in store-word exchange-word payload exchange-value wake-count return; do
    define=-DEDSL_FUTEX_CLIENT_STORE=0x07
    case "$mutation" in
        exchange-word) define=-DEDSL_FUTEX_CLIENT_EXCHANGE=0x06 ;;
        payload) define=-DEDSL_FUTEX_CLIENT_PAYLOAD=0x11223345 ;;
        exchange-value) define=-DEDSL_FUTEX_CLIENT_EXCHANGE_VALUE=2 ;;
        wake-count) define=-DEDSL_FUTEX_CLIENT_WAKE_COUNT=2 ;;
        return) define=-DEDSL_FUTEX_CLIENT_RETURN=0x90 ;;
    esac
    target="$output/rejections/$mutation"
    "${EDSL_CLANG:-clang}" "$define" -c fixtures/futex-publish.S -o "$target.o"
    ld --build-id=none -e edsl_futex_publish_stub -Ttext=0x400000 "$target.o" -o "$target.elf"
    objcopy --only-section=.text -O binary "$target.elf" "$target.bin"
    reject "$target.bin"
    reject "$target.elf" elf
done
head -c 31 "$output/clang/function.bin" > "$output/rejections/truncated.bin"
head -c 64 "$output/clang/function.elf" > "$output/rejections/truncated.elf"
reject "$output/rejections/truncated.bin"
reject "$output/rejections/truncated.elf" elf
"${EDSL_CLANG:-clang}" -c fixtures/futex-wake.S -o "$output/rejections/invocation-only.o"
ld --build-id=none -e edsl_futex_wake_stub -Ttext=0x400000 \
    "$output/rejections/invocation-only.o" -o "$output/rejections/invocation-only.elf"
objcopy --only-section=.text -O binary "$output/rejections/invocation-only.elf" \
    "$output/rejections/invocation-only.bin"
reject "$output/rejections/invocation-only.bin"
reject "$output/rejections/invocation-only.elf" elf
printf 'Rejected wrong STORE/XCHG destination, payload/exchange value, WAKE count, RET, truncation and invocation-only artifacts\n'
printf 'Artifact contracts are conditional on current admission and publishing-member/code binding; trampoline/pthread/kernel conformance and progress remain external\n'
