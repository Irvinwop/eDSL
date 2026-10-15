#!/usr/bin/env bash
set -euo pipefail

if [[ $(uname -sm) != 'Linux x86_64' ]]; then
    echo 'Native integration currently requires Linux x86_64' >&2
    exit 2
fi

output=artifacts/compiler-fixtures
mkdir -p "$output"
lake build edsl-certify
certifier=.lake/build/bin/edsl-certify
clang_c=${EDSL_CLANG:-clang}
clang_cpp=${EDSL_CLANGXX:-clang++}
"$clang_c" -std=gnu23 -O2 -Wall -Wextra -Werror -fcf-protection=none \
    fixtures/native-check.c -o "$output/native-check"

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
    # A static function container, not a Linux startup/process proof.
    # Verify the code after native linking; there is no CRT or external callee.
    ld --build-id=none -e edsl_increment -Ttext=0x400000 \
        "$directory/function.o" -o "$directory/function.elf"
    objcopy --only-section=.text -O binary "$directory/function.elf" "$directory/function.bin"
    readelf -h -l -s "$directory/function.elf" > "$directory/elf.txt"
    objdump -d "$directory/function.elf" > "$directory/disassembly.txt"
    lake env "$certifier" "$directory/function.bin" "$directory/Certificate.lean"
    "$output/native-check" "$directory/function.bin"
    sha256sum "$source" "$directory/function.o" "$directory/function.elf" \
        "$directory/function.bin" "$directory/Certificate.lean" > "$directory/SHA256SUMS"
    echo "Verified and executed $name"
}

verify_one "$clang_c" gnu23 fixtures/increment.c clang-c
verify_one "$clang_cpp" gnu++26 fixtures/increment.cpp clang-cpp
# GCC 13 uses its older gnu2x spelling. Record it explicitly; this is an
# independent compiler-output check, not a claim of complete C23 support.
verify_one "${EDSL_GCC:-gcc}" gnu2x fixtures/increment.c gcc-c

mkdir -p "$output/rejections"
printf '\x8d\x47\x02\xc3' > "$output/rejections/wrong-immediate.bin"
printf '\x8d\x47\x01' > "$output/rejections/truncated.bin"
printf '\x8d\x47\x01\xc3\x90' > "$output/rejections/trailing.bin"
printf '\x0f\x0b' > "$output/rejections/unsupported.bin"
: > "$output/rejections/empty.bin"
for candidate in "$output"/rejections/*.bin; do
    status=0
    lake env "$certifier" "$candidate" "$candidate.lean" > "$candidate.log" 2>&1 || status=$?
    if [[ $status -ne 3 ]]; then
        cat "$candidate.log"
        echo "Expected an unsupported-profile rejection for $candidate, got $status" >&2
        exit 1
    fi
done
echo 'Wrong, truncated, trailing, unsupported and empty candidates remain unverified'
