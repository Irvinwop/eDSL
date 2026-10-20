#!/usr/bin/env bash
set -euo pipefail

if [[ $(uname -sm) != 'Linux x86_64' ]]; then
    echo 'Mutex-worker native integration requires Linux x86_64' >&2
    exit 2
fi

output=artifacts/mutex-worker-fixtures
mkdir -p "$output"
lake build edsl-certify-mutex-worker
certifier=.lake/build/bin/edsl-certify-mutex-worker
clang_c=${EDSL_CLANG:-clang}
driver_args=(-std=gnu23 -O2 -Wall -Wextra -Werror -fcf-protection=none -pthread
             fixtures/mutex-worker-check.c -o "$output/native-check")
printf '%q ' "$clang_c" "${driver_args[@]}" > "$output/driver-arguments.txt"
printf '\n' >> "$output/driver-arguments.txt"
"$clang_c" "${driver_args[@]}"
ld --version > "$output/linker.txt"
lake env lean --version > "$output/lean.txt"

verify_one() {
    local compiler=$1 name=$2
    local directory="$output/$name"
    mkdir -p "$directory"
    local build_args=(-c fixtures/mutex-worker.S -o "$directory/function.o")
    local link_args=(--build-id=none -e edsl_mutex_worker -Ttext=0x400000
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
    sha256sum fixtures/mutex-worker.S fixtures/mutex-worker-check.c \
        "$output/native-check" "$directory/function.o" "$directory/function.elf" \
        "$directory/function.bin" "$directory/Certificate.lean" \
        "$directory/ELFCertificate.lean" > "$directory/SHA256SUMS"
    echo "Certified mutex worker bytes and passed independent sequential/contended native observations ($name)"
}

verify_one "$clang_c" clang
verify_one "${EDSL_GCC:-gcc}" gcc

# Owned mutations cover acquisition control flow, payload width/arithmetic,
# invariant restoration, release and return. Only terminating mutants which
# keep the acquisition/release protocol are passed to the native observer.
directory="$output/rejections"
mkdir -p "$directory"
printf '\xb8\x01\x00\x00\x00\x87\x07\x83\xf8\x01\x75\xf4\x8b\x06\x8d\x40\x01\x89\x06\x8d\x40\x01\x89\x06\xb8\x00\x00\x00\x00\x87\x07\xb8\x00\x00\x00\x00\xc3' > "$directory/compare-one.bin"
printf '\xb8\x01\x00\x00\x00\x87\x07\x83\xf8\x00\x75\xf5\x8b\x06\x8d\x40\x01\x89\x06\x8d\x40\x01\x89\x06\xb8\x00\x00\x00\x00\x87\x07\xb8\x00\x00\x00\x00\xc3' > "$directory/backedge.bin"
printf '\xb8\x01\x00\x00\x00\x87\x07\x83\xf8\x00\x75\xf4\x8b\x06\x8d\x40\x01\x89\x06\x8d\x40\x02\x89\x06\xb8\x00\x00\x00\x00\x87\x07\xb8\x00\x00\x00\x00\xc3' > "$directory/add-three.bin"
printf '\xb8\x01\x00\x00\x00\x87\x07\x83\xf8\x00\x75\xf4\x8b\x06\x8d\x40\x01\x89\x06\x8d\x40\x01\x88\x06\xb8\x00\x00\x00\x00\x87\x07\xb8\x00\x00\x00\x00\xc3' > "$directory/byte-store.bin"
printf '\xb8\x01\x00\x00\x00\x87\x07\x83\xf8\x00\x75\xf4\x8b\x06\x8d\x40\x01\x89\x06\x8d\x40\x01\x90\x90\xb8\x00\x00\x00\x00\x87\x07\xb8\x00\x00\x00\x00\xc3' > "$directory/no-restore-store.bin"
printf '\xb8\x01\x00\x00\x00\x87\x07\x83\xf8\x00\x75\xf4\x8b\x06\x8d\x40\x01\x89\x06\x8d\x40\x01\x89\x06\xb8\x01\x00\x00\x00\x87\x07\xb8\x00\x00\x00\x00\xc3' > "$directory/no-release.bin"
printf '\xb8\x01\x00\x00\x00\x87\x07\x83\xf8\x00\x75\xf4\x8b\x06\x8d\x40\x01\x89\x06\x8d\x40\x01\x89\x06\xb8\x00\x00\x00\x00\x87\x07\xb8\x01\x00\x00\x00\xc3' > "$directory/return-one.bin"
head -c 36 "$output/clang/function.bin" > "$directory/truncated.bin"
for candidate in "$directory"/*.bin; do
    status=0
    lake env "$certifier" "$candidate" "$candidate.lean" > "$candidate.log" 2>&1 || status=$?
    if [[ $status -ne 3 ]]; then
        cat "$candidate.log"
        echo "Expected mutex worker profile rejection 3, got $status ($candidate)" >&2
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
    echo "Expected changed mutex worker ELF rejection 3, got $status" >&2
    exit 1
fi
for mutation in add-three byte-store no-restore-store return-one; do
    status=0
    timeout 30 "$output/native-check" "$directory/$mutation.bin" \
        > "$directory/native-$mutation.log" 2>&1 || status=$?
    if [[ $status -ne 1 ]]; then
        cat "$directory/native-$mutation.log"
        echo "Expected independent native contract rejection 1, got $status ($mutation)" >&2
        exit 1
    fi
done
echo 'Changed compare/backedge, payload width/addend/restore store, release/return, truncation and ELF remain unverified; four safe semantic mutants rejected by native observations'
