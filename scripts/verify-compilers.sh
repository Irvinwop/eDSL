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
    -pthread fixtures/native-check.c -o "$output/native-check"

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
    lake env "$certifier" --elf "$profile" "$directory/function.elf" "$directory/ELFCertificate.lean"
    timeout 30 "$output/native-check" "$profile" "$directory/function.bin"
    sha256sum "$source" "$directory/function.o" "$directory/function.elf" \
        "$directory/function.bin" "$directory/Certificate.lean" "$directory/ELFCertificate.lean" > "$directory/SHA256SUMS"
    echo "Verified and executed $name"
}

verify_one "$clang_c" gnu23 fixtures/increment.c clang-c increment edsl_increment
verify_one "$clang_cpp" gnu++26 fixtures/increment.cpp clang-cpp increment edsl_increment
# GCC 13 uses its older gnu2x spelling. Record it explicitly; this is an
# independent compiler-output check, not a claim of complete C23 support.
verify_one "${EDSL_GCC:-gcc}" gnu2x fixtures/increment.c gcc-c increment edsl_increment
for profile in load32 store32 exchange32; do
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
# decodable encoding: mismatched memory-operation profiles remain unverified.
for specification in load32 store32 exchange32; do
    for other in load32 store32 exchange32; do
        if [[ $specification == "$other" ]]; then continue; fi
        status=0
        lake env "$certifier" "$specification" "$output/clang-c-$other/function.bin" \
            "$output/rejections/wrong-$specification-$other.lean" \
            > "$output/rejections/wrong-$specification-$other.log" 2>&1 || status=$?
        if [[ $status -ne 3 ]]; then
            echo "Wrong $other contract was not rejected for $specification" >&2
            exit 1
        fi
    done
done
echo 'Load/store/exchange contract mismatches remain unverified'

# The ELF path must bind the complete file and its selected contract. These are
# owned mutations of the fixture, never third-party findings or reproducers.
objcopy --update-section ".text=$output/rejections/wrong-immediate.bin" \
    "$output/clang-c/function.elf" "$output/rejections/wrong-elf-immediate.elf"
for specification in increment load32 store32 exchange32; do
    candidate="$output/rejections/wrong-elf-immediate.elf"
    if [[ $specification == load32 ]]; then candidate="$output/clang-c-store32/function.elf"; fi
    if [[ $specification == store32 ]]; then candidate="$output/clang-c-load32/function.elf"; fi
    if [[ $specification == exchange32 ]]; then candidate="$output/clang-c-store32/function.elf"; fi
    status=0
    lake env "$certifier" --elf "$specification" "$candidate" \
        "$output/rejections/wrong-elf-$specification.lean" > "$output/rejections/wrong-elf-$specification.log" 2>&1 || status=$?
    if [[ $status -ne 3 ]]; then
        cat "$output/rejections/wrong-elf-$specification.log"
        echo "Wrong ELF contract was not rejected for $specification" >&2
        exit 1
    fi
done
echo 'Mutated ELF code and load/store/exchange ELF contract mismatches remain unverified'

# This equally short routine returns the old word and writes the replacement,
# but has separate load/store instructions. Sequential results alone cannot
# establish the selected indivisible-exchange contract. Never execute this
# owned negative fixture concurrently in CI.
printf '\x8b\x07\x89\x37\xc3' > "$output/rejections/non-atomic-exchange.bin"
objcopy --update-section ".text=$output/rejections/non-atomic-exchange.bin" \
    "$output/clang-c-exchange32/function.elf" "$output/rejections/non-atomic-exchange.elf"
for format in bin elf; do
    options=()
    if [[ $format == elf ]]; then options=(--elf); fi
    status=0
    lake env "$certifier" "${options[@]}" exchange32 "$output/rejections/non-atomic-exchange.$format" \
        "$output/rejections/non-atomic-exchange-$format.lean" \
        > "$output/rejections/non-atomic-exchange-$format.log" 2>&1 || status=$?
    if [[ $status -ne 3 ]]; then
        cat "$output/rejections/non-atomic-exchange-$format.log"
        echo "Separate load/store routine was not rejected for atomic exchange ($format)" >&2
        exit 1
    fi
done
echo 'Separate load/store routines remain unverified under the atomic-exchange contract'

# Independent Linux observations for the abstract address-space contracts.
# Faults are deliberate owned fixtures in child processes with core dumps off.
"$clang_c" -std=gnu23 -O2 -Wall -Wextra -Werror \
    fixtures/vm-contract.c -o "$output/vm-contract"
"$output/vm-contract"
