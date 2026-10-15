#!/usr/bin/env bash
set -euo pipefail

if [[ $(uname -sm) != 'Linux x86_64' ]]; then
    echo 'Loop integration currently requires Linux x86_64' >&2
    exit 2
fi

output=artifacts/loop-fixtures
mkdir -p "$output"
lake build edsl-certify
certifier=.lake/build/bin/edsl-certify
ld --version > "$output/linker.txt"
lake env lean --version > "$output/lean.txt"
driver_args=(-std=gnu23 -O2 -Wall -Wextra -Werror -fcf-protection=none
             -pthread fixtures/native-check.c -o "$output/native-check")
printf '%q ' "${EDSL_CLANG:-clang}" "${driver_args[@]}" > "$output/driver-arguments.txt"
printf '\n' >> "$output/driver-arguments.txt"
"${EDSL_CLANG:-clang}" "${driver_args[@]}"

verify_one() {
    local compiler=$1 name=$2
    local directory="$output/$name"
    mkdir -p "$directory"
    local build_args=(-c fixtures/increment-loop.S -o "$directory/function.o")
    local link_args=(--build-id=none -e edsl_increment_loop -Ttext=0x400000
                     "$directory/function.o" -o "$directory/function.elf")
    "$compiler" --version > "$directory/compiler.txt"
    printf '%q ' "$compiler" "${build_args[@]}" > "$directory/arguments.txt"
    printf '\n' >> "$directory/arguments.txt"
    printf '%q ' ld "${link_args[@]}" >> "$directory/arguments.txt"
    printf '\n' >> "$directory/arguments.txt"
    "$compiler" "${build_args[@]}"
    ld "${link_args[@]}"
    objcopy --only-section=.text -O binary "$directory/function.elf" "$directory/function.bin"
    readelf -h -l -s "$directory/function.elf" > "$directory/elf.txt"
    objdump -d "$directory/function.elf" > "$directory/disassembly.txt"
    lake env "$certifier" increment-loop "$directory/function.bin" "$directory/Certificate.lean"
    lake env "$certifier" --elf increment-loop "$directory/function.elf" "$directory/ELFCertificate.lean"
    timeout 10 "$output/native-check" increment-loop "$directory/function.bin"
    sha256sum fixtures/increment-loop.S fixtures/native-check.c "$output/native-check" \
        "$directory/function.o" "$directory/function.elf" "$directory/function.bin" \
        "$directory/Certificate.lean" "$directory/ELFCertificate.lean" > "$directory/SHA256SUMS"
    echo "Certified all-count loop and passed bounded native observations ($name)"
}

verify_one "${EDSL_CLANG:-clang}" clang
verify_one "${EDSL_GCC:-gcc}" gcc

# Owned mutations exercise the independently selected arithmetic contract and
# each control-flow edge. Negative code is never executed.
directory="$output/rejections"
mkdir -p "$directory"
printf '\x89\xf8\xe3\x04\x8d\x40\x01\xe2\xfb\xc3' > "$directory/guard.bin"
printf '\x89\xf8\xe3\x05\x8d\x40\x01\xe2\xfc\xc3' > "$directory/backedge.bin"
printf '\x89\xf8\xe3\x05\x8d\x40\x02\xe2\xfb\xc3' > "$directory/increment.bin"
printf '\x67\x89\xf8\xe3\x05\x8d\x40\x01\xe2\xfb\xc3' > "$directory/prefix.bin"
head -c 9 "$output/clang/function.bin" > "$directory/truncated.bin"
for candidate in "$directory"/*.bin; do
    status=0
    lake env "$certifier" increment-loop "$candidate" "$candidate.lean" > "$candidate.log" 2>&1 || status=$?
    if [[ $status -ne 3 ]]; then
        cat "$candidate.log"
        echo "Expected loop-profile rejection 3, got $status ($candidate)" >&2
        exit 1
    fi
done
objcopy --update-section ".text=$directory/backedge.bin" \
    "$output/clang/function.elf" "$directory/backedge.elf"
status=0
lake env "$certifier" --elf increment-loop "$directory/backedge.elf" "$directory/ELF.lean" \
    > "$directory/ELF.log" 2>&1 || status=$?
if [[ $status -ne 3 ]]; then
    cat "$directory/ELF.log"
    echo "Expected changed ELF loop rejection 3, got $status" >&2
    exit 1
fi
echo 'Wrong arithmetic, guard/backedge, prefix, truncation and changed ELF remain unverified'
