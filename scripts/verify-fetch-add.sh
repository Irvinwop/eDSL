#!/usr/bin/env bash
set -euo pipefail
if [[ $(uname -sm) != 'Linux x86_64' ]]; then
    echo 'Fetch-add native integration requires Linux x86_64' >&2
    exit 2
fi
output=artifacts/fetch-add-fixtures
mkdir -p "$output"
lake build edsl-certify
certifier=.lake/build/bin/edsl-certify
clang_c=${EDSL_CLANG:-clang}
clang_cpp=${EDSL_CLANGXX:-clang++}
"$clang_c" -std=gnu23 -O2 -Wall -Wextra -Werror -fcf-protection=none -pthread \
    fixtures/fetch-add-check.c fixtures/fetch-add-flags.S -o "$output/native-check"

verify_one() {
    local compiler=$1 dialect=$2 source=$3 name=$4
    local directory="$output/$name"
    mkdir -p "$directory"
    local flags=("-std=$dialect" -O2 -fno-stack-protector -fcf-protection=none
        -fno-asynchronous-unwind-tables -c "$source" -o "$directory/function.o")
    "$compiler" --version > "$directory/compiler.txt"
    printf '%q ' "$compiler" "${flags[@]}" > "$directory/arguments.txt"
    printf '\n' >> "$directory/arguments.txt"
    "$compiler" "${flags[@]}"
    ld --build-id=none -e edsl_fetch_add32 -Ttext=0x400000 "$directory/function.o" -o "$directory/function.elf"
    objcopy --only-section=.text -O binary "$directory/function.elf" "$directory/function.bin"
    objdump -d "$directory/function.elf" > "$directory/disassembly.txt"
    readelf -h -l -s "$directory/function.elf" > "$directory/elf.txt"
    lake env "$certifier" fetch-add32 "$directory/function.bin" "$directory/Certificate.lean"
    lake env "$certifier" --elf fetch-add32 "$directory/function.elf" "$directory/ELFCertificate.lean"
    timeout 30 "$output/native-check" "$directory/function.bin" > "$directory/NativeFlags.lean"
    lake env lean -DwarningAsError=true "$directory/NativeFlags.lean"
    sha256sum "$source" "$directory/function.o" "$directory/function.elf" "$directory/function.bin" \
        "$directory/Certificate.lean" "$directory/ELFCertificate.lean" "$directory/NativeFlags.lean" > "$directory/SHA256SUMS"
    echo "Certified fetch-add and checked 144 native flag pairs and 800000 contended old values ($name)"
}
verify_one "$clang_c" gnu23 fixtures/fetch-add32.c clang-c
verify_one "$clang_cpp" gnu++26 fixtures/fetch-add32.cpp clang-cpp
verify_one "${EDSL_GCC:-gcc}" gnu2x fixtures/fetch-add32.c gcc-c

mkdir -p "$output/rejections"
printf '\x89\xf0\x0f\xc1\x07\xc3' > "$output/rejections/unlocked.bin"
printf '\x89\xf0\xf0\x48\x0f\xc1\x07\xc3' > "$output/rejections/wrong-width.bin"
printf '\x89\xf0\x66\x0f\xc1\x07\xc3' > "$output/rejections/word16.bin"
printf '\x89\xf0\x87\x07\xc3' > "$output/rejections/exchange.bin"
printf '\x89\xf0\xf0\x0f\xc1\x07' > "$output/rejections/truncated.bin"
for candidate in "$output"/rejections/*.bin; do
    status=0
    lake env "$certifier" fetch-add32 "$candidate" "$candidate.lean" > "$candidate.log" 2>&1 || status=$?
    if [[ $status -ne 3 ]]; then
        cat "$candidate.log"
        echo "Expected fetch-add profile rejection 3, got $status ($candidate)" >&2
        exit 1
    fi
done
status=0
timeout 30 "$output/native-check" "$output/rejections/word16.bin" > "$output/rejections/native-word16.log" 2>&1 || status=$?
if [[ $status -ne 1 ]]; then
    echo "Expected independent native width/result rejection 1, got $status" >&2
    exit 1
fi
echo 'Unlocked, wrong-width, wrong-operation and truncated candidates remain unverified; native width mutant rejected'
