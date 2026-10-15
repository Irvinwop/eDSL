#!/usr/bin/env bash
set -euo pipefail

if [[ $(uname -sm) != 'Linux x86_64' ]]; then
    echo 'Futex native integration requires Linux x86_64' >&2
    exit 2
fi
output=artifacts/futex-fixtures
mkdir -p "$output"
uname -sr > "$output/kernel.txt"
ld --version > "$output/linker.txt"
lake env lean --version > "$output/lean.txt"
lake build edsl-certify-futex
certifier=.lake/build/bin/edsl-certify-futex

verify_compiler() {
    local compiler=$1 dialect=$2 name=$3
    local directory="$output/$name"
    mkdir -p "$directory"
    "$compiler" --version > "$directory/compiler.txt"
    for profile in wait wake-one; do
        local fixture=fixtures/futex-wait.S symbol=edsl_futex_wait_stub
        if [[ $profile == wake-one ]]; then fixture=fixtures/futex-wake.S; symbol=edsl_futex_wake_stub; fi
        local target="$directory/$profile"
        mkdir -p "$target"
        local compile_args=(-c "$fixture" -o "$target/function.o")
        local link_args=(--build-id=none -e "$symbol" -Ttext=0x400000 "$target/function.o" -o "$target/function.elf")
        {
            printf '%q ' "$compiler" "${compile_args[@]}"
            printf '\n'
            printf '%q ' ld "${link_args[@]}"
            printf '\n'
        } > "$target/arguments.txt"
        "$compiler" "${compile_args[@]}"
        ld "${link_args[@]}"
        objcopy --only-section=.text -O binary "$target/function.elf" "$target/function.bin"
        objdump -d "$target/function.elf" > "$target/disassembly.txt"
        readelf -h -l -s "$target/function.elf" > "$target/elf.txt"
        lake env "$certifier" "$profile" "$target/function.bin" "$target/Certificate.lean"
        lake env "$certifier" --elf "$profile" "$target/function.elf" "$target/ELFCertificate.lean"
        sha256sum "$fixture" "$target/function.o" "$target/function.elf" "$target/function.bin" \
            "$target/Certificate.lean" "$target/ELFCertificate.lean" > "$target/SHA256SUMS"
    done
    # Link those same certified objects, without recompiling their code, into
    # the native observer. The separate trampoline establishes the ABI inputs.
    local native_args=("-std=$dialect" -O2 -Wall -Wextra -Werror -fcf-protection=none -pthread
        fixtures/futex-check.c fixtures/futex-trampoline.S
        "-Wl,--unique=.text.edsl_futex_wait_stub,--unique=.text.edsl_futex_wake_stub"
        "$directory/wait/function.o" "$directory/wake-one/function.o" -o "$directory/native-check")
    printf '%q ' "$compiler" "${native_args[@]}" > "$directory/native-arguments.txt"
    printf '\n' >> "$directory/native-arguments.txt"
    "$compiler" "${native_args[@]}"
    for profile in wait wake-one; do
        local section=.text.edsl_futex_wait_stub
        if [[ $profile == wake-one ]]; then section=.text.edsl_futex_wake_stub; fi
        objcopy --only-section="$section" -O binary "$directory/native-check" "$directory/$profile/native-linked.bin"
        cmp "$directory/$profile/function.bin" "$directory/$profile/native-linked.bin"
    done
    local status=0
    timeout 20 "$directory/native-check" > "$directory/native-results.txt" 2>&1 || status=$?
    cat "$directory/native-results.txt"
    if [[ $status -eq 124 ]]; then
        echo 'INCONCLUSIVE: native futex observer hit its external scheduling bound' >&2
        exit 3
    fi
    if [[ $status -ne 0 ]]; then
        echo "Native futex observer failed ($name, status $status)" >&2
        exit 1
    fi
    case $(cat "$directory/native-results.txt") in
        *'OBSERVED WAKE_PRIVATE/1 selected one waiter while W remained zero'*)
            printf 'observed\n' > "$directory/queued-wake-observation.txt" ;;
        *) printf 'inconclusive\n' > "$directory/queued-wake-observation.txt" ;;
    esac
    sha256sum fixtures/futex-check.c fixtures/futex-trampoline.S "$directory/native-check" \
        "$directory/native-results.txt" "$directory/wait/native-linked.bin" \
        "$directory/wake-one/native-linked.bin" > "$directory/native-SHA256SUMS"
}
verify_compiler "${EDSL_CLANG:-clang}" gnu23 clang
verify_compiler "${EDSL_GCC:-gcc}" gnu2x gcc

reject() {
    local profile=$1 candidate=$2 mode=${3:-raw}
    local arguments=("$profile" "$candidate" "$candidate.lean")
    if [[ $mode == elf ]]; then arguments=(--elf "${arguments[@]}"); fi
    local status=0
    lake env "$certifier" "${arguments[@]}" > "$candidate.log" 2>&1 || status=$?
    if [[ $status -ne 3 ]]; then
        cat "$candidate.log"
        echo "Expected unsupported futex contract result 3, got $status ($candidate)" >&2
        exit 1
    fi
}

# Owned non-executed mutations target independent ABI and continuation facts.
mkdir -p "$output/rejections"
for mutation in syscall operation return wake-count; do
    fixture=fixtures/futex-wait.S
    profile="wait"
    symbol=edsl_futex_wait_stub
    define=-DEDSL_FUTEX_SYSCALL=203
    if [[ $mutation == operation ]]; then define=-DEDSL_FUTEX_WAIT_OP=0; fi
    if [[ $mutation == return ]]; then define=-DEDSL_FUTEX_RETURN=0x90; fi
    if [[ $mutation == wake-count ]]; then
        fixture=fixtures/futex-wake.S
        profile=wake-one
        symbol=edsl_futex_wake_stub
        define=-DEDSL_FUTEX_WAKE_COUNT=2
    fi
    target="$output/rejections/$mutation"
    "${EDSL_CLANG:-clang}" "$define" -c "$fixture" -o "$target.o"
    ld --build-id=none -e "$symbol" -Ttext=0x400000 "$target.o" -o "$target.elf"
    objcopy --only-section=.text -O binary "$target.elf" "$target.bin"
    reject "$profile" "$target.bin"
    reject "$profile" "$target.elf" elf
done
head -c 12 "$output/clang/wait/function.bin" > "$output/rejections/truncated.bin"
reject wait "$output/rejections/truncated.bin"
head -c 64 "$output/clang/wait/function.elf" > "$output/rejections/truncated.elf"
reject wait "$output/rejections/truncated.elf" elf
reject wait "$output/clang/wake-one/function.bin"
reject wake-one "$output/clang/wait/function.bin"
reject wait "$output/clang/wake-one/function.elf" elf
reject wake-one "$output/clang/wait/function.elf" elf
echo 'Wrong syscall/operation/wake count/RET, truncated artifacts and mismatched profiles remain unverified'
echo 'Certificates prove userspace ABI/RET contracts; native observations do not prove kernel implementation or progress'
