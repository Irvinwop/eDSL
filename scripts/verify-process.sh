#!/usr/bin/env bash
set -euo pipefail

if [[ $(uname -sm) != 'Linux x86_64' ]]; then
    echo 'Process integration currently requires Linux x86_64' >&2
    exit 2
fi

output=artifacts/process-fixtures
mkdir -p "$output"
ld --version > "$output/linker.txt"
uname -sr > "$output/kernel.txt"
lake env lean --version > "$output/lean.txt"
lake build edsl-certify-process
certifier=.lake/build/bin/edsl-certify-process
driver_args=(-std=gnu23 -O2 -Wall -Wextra -Werror fixtures/process-stream.c
             -o "$output/process-stream")
printf '%q ' "${EDSL_CLANG:-clang}" "${driver_args[@]}" > "$output/driver-arguments.txt"
printf '\n' >> "$output/driver-arguments.txt"
"${EDSL_CLANG:-clang}" "${driver_args[@]}"

verify_one() {
    local compiler_path=$1 compiler_name=$2 profile=$3
    local directory="$output/$compiler_name"
    local fixture=fixtures/exit42.S
    if [[ $profile == write-exit42 ]]; then fixture=fixtures/write-exit42.S; fi
    mkdir -p "$directory"
    local build_args=(-c "$fixture" -o "$directory/process.o")
    local link_args=(--build-id=none -e _start -Ttext=0x400000
                     "$directory/process.o" -o "$directory/process.elf")
    "$compiler_path" --version > "$directory/compiler.txt"
    printf '%q ' "$compiler_path" "${build_args[@]}" > "$directory/arguments.txt"
    printf '\n' >> "$directory/arguments.txt"
    printf '%q ' ld "${link_args[@]}" >> "$directory/arguments.txt"
    printf '\n' >> "$directory/arguments.txt"
    "$compiler_path" "${build_args[@]}"
    ld "${link_args[@]}"
    readelf -h -l -s "$directory/process.elf" > "$directory/elf.txt"
    objdump -d "$directory/process.elf" > "$directory/disassembly.txt"
    lake env "$certifier" "$profile" "$directory/process.elf" "$directory/Certificate.lean"
    if [[ $profile == write-exit42 ]]; then
        timeout 10 "$output/process-stream" "$directory/process.elf" | tee "$directory/native-results.txt"
    else
        local observed_status=0
        timeout 10 "$directory/process.elf" || observed_status=$?
        printf '%s\n' "$observed_status" > "$directory/native-exit-status.txt"
        if [[ $observed_status -ne 42 ]]; then
            echo "Expected native process exit 42, got $observed_status ($compiler_name)" >&2
            exit 1
        fi
    fi
    sha256sum "$fixture" fixtures/process-stream.c "$output/process-stream" \
        "$directory/process.o" "$directory/process.elf" \
        "$directory/Certificate.lean" > "$directory/SHA256SUMS"
    echo "Certified and observed native exit 42 ($compiler_name)"
}

verify_one "${EDSL_CLANG:-clang}" clang exit42
verify_one "${EDSL_GCC:-gcc}" gcc exit42
verify_one "${EDSL_CLANG:-clang}" clang-write write-exit42
verify_one "${EDSL_GCC:-gcc}" gcc-write write-exit42

# Owned negative fixtures are checked, never executed. Both changing the result
# and changing the syscall must fail the independently selected exit42 contract.
mkdir -p "$output/rejections"
for mutation in status syscall; do
    define=-DEDSL_EXIT_STATUS=43
    if [[ $mutation == syscall ]]; then define=-DEDSL_EXIT_SYSCALL=39; fi
    "${EDSL_CLANG:-clang}" "$define" -c fixtures/exit42.S -o "$output/rejections/$mutation.o"
    ld --build-id=none -e _start -Ttext=0x400000 "$output/rejections/$mutation.o" \
        -o "$output/rejections/$mutation.elf"
    result=0
    lake env "$certifier" "$output/rejections/$mutation.elf" "$output/rejections/$mutation.lean" \
        > "$output/rejections/$mutation.log" 2>&1 || result=$?
    if [[ $result -ne 3 ]]; then
        cat "$output/rejections/$mutation.log"
        echo "Expected unsupported process-contract result 3, got $result ($mutation)" >&2
        exit 1
    fi
done
echo 'Wrong exit status and wrong syscall remain unverified'

# Input/output binding must include the buffer bytes, count and descriptor.
for mutation in data count descriptor; do
    define=-DEDSL_WRITE_FIRST_BYTE=0x58
    if [[ $mutation == count ]]; then define=-DEDSL_WRITE_COUNT=4; fi
    if [[ $mutation == descriptor ]]; then define=-DEDSL_WRITE_DESCRIPTOR=2; fi
    "${EDSL_CLANG:-clang}" "$define" -c fixtures/write-exit42.S -o "$output/rejections/write-$mutation.o"
    ld --build-id=none -e _start -Ttext=0x400000 "$output/rejections/write-$mutation.o" \
        -o "$output/rejections/write-$mutation.elf"
    result=0
    lake env "$certifier" write-exit42 "$output/rejections/write-$mutation.elf" \
        "$output/rejections/write-$mutation.lean" > "$output/rejections/write-$mutation.log" 2>&1 || result=$?
    if [[ $result -ne 3 ]]; then
        cat "$output/rejections/write-$mutation.log"
        echo "Expected write-profile rejection 3, got $result ($mutation)" >&2
        exit 1
    fi
done
for profile in exit42 write-exit42; do
    candidate="$output/clang-write/process.elf"
    if [[ $profile == write-exit42 ]]; then candidate="$output/clang/process.elf"; fi
    result=0
    lake env "$certifier" "$profile" "$candidate" "$output/rejections/cross-$profile.lean" \
        > "$output/rejections/cross-$profile.log" 2>&1 || result=$?
    if [[ $result -ne 3 ]]; then
        echo "Expected process-contract mismatch rejection 3, got $result ($profile)" >&2
        exit 1
    fi
done
echo 'Changed stream data/count/descriptor and process-contract mismatches remain unverified'
