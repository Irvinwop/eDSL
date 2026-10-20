#!/usr/bin/env bash
set -euo pipefail

if [[ $(uname -sm) != 'Linux x86_64' ]]; then
    echo 'Counter-worker native integration requires Linux x86_64' >&2
    exit 2
fi

output=artifacts/counter-worker-fixtures
mkdir -p "$output"
lake build edsl-certify-counter
certifier=.lake/build/bin/edsl-certify-counter
clang_c=${EDSL_CLANG:-clang}
driver_args=(-std=gnu23 -O2 -Wall -Wextra -Werror -fcf-protection=none -pthread
             fixtures/counter-check.c fixtures/counter-call.S -o "$output/native-check")
printf '%q ' "$clang_c" "${driver_args[@]}" > "$output/driver-arguments.txt"
printf '\n' >> "$output/driver-arguments.txt"
"$clang_c" "${driver_args[@]}"
ld --version > "$output/linker.txt"
lake env lean --version > "$output/lean.txt"

verify_one() {
    local compiler=$1 name=$2
    local directory="$output/$name"
    mkdir -p "$directory"
    local build_args=(-c fixtures/counter-loop.S -o "$directory/function.o")
    local link_args=(--build-id=none -e edsl_counter_loop -Ttext=0x400000
                     "$directory/function.o" -o "$directory/function.elf")
    "$compiler" --version > "$directory/compiler.txt"
    {
        printf '%q ' "$compiler" "${build_args[@]}"
        printf '\n'
        printf '%q ' ld "${link_args[@]}"
        printf '\n'
    } > "$directory/arguments.txt"
    "$compiler" "${build_args[@]}"
    ld "${link_args[@]}"
    objcopy --only-section=.text -O binary "$directory/function.elf" "$directory/function.bin"
    objdump -d "$directory/function.elf" > "$directory/disassembly.txt"
    readelf -h -l -s "$directory/function.elf" > "$directory/elf.txt"
    lake env "$certifier" "$directory/function.bin" "$directory/Certificate.lean"
    lake env "$certifier" --elf "$directory/function.elf" "$directory/ELFCertificate.lean"
    timeout 30 "$output/native-check" "$directory/function.bin" > "$directory/native.txt"
    sha256sum fixtures/counter-loop.S fixtures/counter-check.c fixtures/counter-call.S \
        "$output/native-check" "$directory/function.o" "$directory/function.elf" \
        "$directory/function.bin" "$directory/Certificate.lean" \
        "$directory/ELFCertificate.lean" > "$directory/SHA256SUMS"
    echo "Certified counter workers and passed independent sequential/contended native observations ($name)"
}

verify_one "$clang_c" clang
verify_one "${EDSL_GCC:-gcc}" gcc

# Project-owned mutations independently exercise the guard, backedge, atomicity,
# width, arithmetic and return contracts. Only terminating semantic mutants
# are passed to the native observer; unsafe control flow is never run.
directory="$output/rejections"
mkdir -p "$directory"
printf '\xe3\x0a\xb8\x01\x00\x00\x00\xf0\x0f\xc1\x07\xe2\xf5\xb8\x00\x00\x00\x00\xc3' > "$directory/guard.bin"
printf '\xe3\x0b\xb8\x01\x00\x00\x00\xf0\x0f\xc1\x07\xe2\xf6\xb8\x00\x00\x00\x00\xc3' > "$directory/backedge.bin"
printf '\xe3\x0b\xb8\x01\x00\x00\x00\x90\x0f\xc1\x07\xe2\xf5\xb8\x00\x00\x00\x00\xc3' > "$directory/unlocked.bin"
printf '\xe3\x0b\xb8\x01\x00\x00\x00\x66\x0f\xc1\x07\xe2\xf5\xb8\x00\x00\x00\x00\xc3' > "$directory/word16.bin"
printf '\xe3\x0b\xb8\x02\x00\x00\x00\xf0\x0f\xc1\x07\xe2\xf5\xb8\x00\x00\x00\x00\xc3' > "$directory/add-two.bin"
printf '\xe3\x0b\xb8\x01\x00\x00\x00\x90\x90\x87\x07\xe2\xf5\xb8\x00\x00\x00\x00\xc3' > "$directory/exchange.bin"
printf '\xe3\x0b\xb8\x01\x00\x00\x00\xf0\x0f\xc1\x07\xe2\xf5\xb8\x01\x00\x00\x00\xc3' > "$directory/return-one.bin"
printf '\xe3\x0b\xb8\x01\x00\x00\x00\xf0\x48\x0f\xc1\x07\xe2\xf5\xb8\x00\x00\x00\x00\xc3' > "$directory/word64.bin"
head -c 18 "$output/clang/function.bin" > "$directory/truncated.bin"
for candidate in "$directory"/*.bin; do
    status=0
    lake env "$certifier" "$candidate" "$candidate.lean" > "$candidate.log" 2>&1 || status=$?
    if [[ $status -ne 3 ]]; then
        cat "$candidate.log"
        echo "Expected counter profile rejection 3, got $status ($candidate)" >&2
        exit 1
    fi
done
objcopy --update-section ".text=$directory/backedge.bin" \
    "$output/clang/function.elf" "$directory/backedge.elf"
status=0
lake env "$certifier" --elf "$directory/backedge.elf" "$directory/ELF.lean" \
    > "$directory/ELF.log" 2>&1 || status=$?
if [[ $status -ne 3 ]]; then
    cat "$directory/ELF.log"
    echo "Expected changed counter ELF rejection 3, got $status" >&2
    exit 1
fi
for mutation in word16 add-two exchange return-one; do
    status=0
    timeout 30 "$output/native-check" "$directory/$mutation.bin" \
        > "$directory/native-$mutation.log" 2>&1 || status=$?
    if [[ $status -ne 1 ]]; then
        cat "$directory/native-$mutation.log"
        echo "Expected independent native contract rejection 1, got $status ($mutation)" >&2
        exit 1
    fi
done
echo 'Guard/backedge, missing LOCK, wrong width/operation/addend/return, truncation and changed ELF remain unverified; four safe semantic mutants rejected by native observations'
