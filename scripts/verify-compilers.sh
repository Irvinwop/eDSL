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
    local compiler=$1 dialect=$2 source=$3 name=$4 profile=$5 symbol=$6
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
    ld --build-id=none -e "$symbol" -Ttext=0x400000 \
        "$directory/function.o" -o "$directory/function.elf"
    objcopy --only-section=.text -O binary "$directory/function.elf" "$directory/function.bin"
    readelf -h -l -s "$directory/function.elf" > "$directory/elf.txt"
    objdump -d "$directory/function.elf" > "$directory/disassembly.txt"
    lake env "$certifier" "$profile" "$directory/function.bin" "$directory/Certificate.lean"
    "$output/native-check" "$profile" "$directory/function.bin"
    sha256sum "$source" "$directory/function.o" "$directory/function.elf" \
        "$directory/function.bin" "$directory/Certificate.lean" > "$directory/SHA256SUMS"
    echo "Verified and executed $name"
}

verify_one "$clang_c" gnu23 fixtures/increment.c clang-c increment edsl_increment
verify_one "$clang_cpp" gnu++26 fixtures/increment.cpp clang-cpp increment edsl_increment
# GCC 13 uses its older gnu2x spelling. Record it explicitly; this is an
# independent compiler-output check, not a claim of complete C23 support.
verify_one "${EDSL_GCC:-gcc}" gnu2x fixtures/increment.c gcc-c increment edsl_increment
for profile in load32 store32; do
    verify_one "$clang_c" gnu23 "fixtures/$profile.c" "clang-c-$profile" "$profile" "edsl_$profile"
    verify_one "$clang_cpp" gnu++26 "fixtures/$profile.cpp" "clang-cpp-$profile" "$profile" "edsl_$profile"
    verify_one "${EDSL_GCC:-gcc}" gnu2x "fixtures/$profile.c" "gcc-c-$profile" "$profile" "edsl_$profile"
done

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

# A certificate must also be bound to the requested contract, not just a
# decodable encoding: swapping load/store profiles must remain unverified.
for specification in load32 store32; do
    other=load32
    if [[ $specification == load32 ]]; then other=store32; fi
    status=0
    lake env "$certifier" "$specification" "$output/clang-c-$other/function.bin" \
        "$output/rejections/wrong-$specification.lean" > "$output/rejections/wrong-$specification.log" 2>&1 || status=$?
    if [[ $status -ne 3 ]]; then
        echo "Wrong contract was not rejected for $specification" >&2
        exit 1
    fi
done
echo 'Load/store contract mismatches remain unverified'
