#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail
export LC_ALL=C
if [[ $# -ne 0 ]]; then
    echo 'usage: verify-atomic-set64-native.sh' >&2
    exit 2
fi
if [[ $(uname -sm) != 'Linux x86_64' ]]; then
    echo 'LockedSet64 native evidence requires Linux x86_64 / System V' >&2
    exit 2
fi
cd "$(dirname "${BASH_SOURCE[0]}")/.."
# All evidence stays in this checkout on the invoking HOME machine. No SSH,
# unknown program loader, executable mmap, or existing binary input is used.
archive=${EDSL_SET64_NATIVE_OUTPUT:-artifacts/atomic-set64-native}
mkdir -p "$archive"
archive=$(cd "$archive" && pwd -P)
output=$(mktemp -d "$archive/run.XXXXXXXX")
printf 'LockedSet64 native evidence: %s\n' "$output"
exec 3>&1 4>&2
exec > "$output/script.log" 2>&1
ulimit -c 0
complete=0
phase=initialization
record_command() { printf '%q ' "$@"; printf '\n'; }
run() { record_command "$@" >> "$output/commands.txt"; "$@"; }
write_hashes() {
    (cd "$output" && find . -type f ! -name SHA256SUMS -print0 | sort -z | xargs -0 sha256sum) \
        > "$output/SHA256SUMS"
}
finish() {
    local status=$? manifest_status=0
    trap - EXIT
    set +e
    if [[ $status -ne 0 || $complete -ne 1 ]]; then
        [[ $status -ne 0 ]] || status=1
        printf 'INCOMPLETE: exit=%s phase=%s; retained partial evidence; no successful native claim\n' \
            "$status" "$phase" > "$output/result.txt"
    fi
    printf '%s\n' "$status" > "$output/script-status.txt"
    printf 'exit=%s phase=%s UTC=%s proof-status=NOT_RUN\n' "$status" "$phase" \
        "$(date -u +%FT%TZ)" > "$output/terminal-status.txt"
    # First retain the actual verification output, then cover it in the final
    # manifest and verify again without changing any hashed file.
    write_hashes 2>&4 && (cd "$output" && sha256sum --check SHA256SUMS) \
        > "$output/manifest-verification.txt" 2>&1 || manifest_status=$?
    write_hashes 2>&4 && (cd "$output" && sha256sum --quiet --check SHA256SUMS) >&4 2>&4 \
        || manifest_status=$?
    if [[ $manifest_status -ne 0 ]]; then
        status=1
        echo 'INCOMPLETE: evidence manifest creation/verification failed' > "$output/result.txt"
        printf '%s\n' "$status" > "$output/script-status.txt"
        printf 'exit=1 phase=manifest_verification UTC=%s proof-status=NOT_RUN\n' \
            "$(date -u +%FT%TZ)" > "$output/terminal-status.txt"
        printf 'INCOMPLETE: manifest operation exit=%s\n' "$manifest_status" > "$output/manifest-failure.txt"
        write_hashes 2>&4
        (cd "$output" && sha256sum --quiet --check SHA256SUMS) >&4 2>&4
        printf 'LockedSet64 manifest verification failed: %s\n' "$output" >&4
    fi
    if [[ $status -eq 0 ]]; then
        printf 'PASS finite native evidence; manifest verified; proof-status NOT RUN: %s\n' "$output" >&3
    else
        printf 'INCOMPLETE native evidence (exit %s): %s\n' "$status" "$output" >&4
    fi
    exit "$status"
}
trap finish EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
trap 'exit 129' HUP
echo 'INCOMPLETE: native checks have not finished' > "$output/result.txt"
echo 'NOT RUN: Lean proofs/builds/imports, kernel replay, theorem audit, C/C++ source preservation' \
    > "$output/proof-status.txt"

phase=snapshot
source_files=(fixtures/atomic-set64.c fixtures/atomic-set64.cpp fixtures/atomic-set64-check.c
    fixtures/atomic-set64-check.S scripts/verify-atomic-set64-native.sh)
run sha256sum "${source_files[@]}" > "$output/source-SHA256SUMS"
for file in "${source_files[@]}"; do
    run install -D -m 0644 "$file" "$output/source/$file"
done
(cd "$output/source" && sha256sum --check "$output/source-SHA256SUMS") > "$output/source-copy-check.txt"
run bash -n "$output/source/scripts/verify-atomic-set64-native.sh"
run shellcheck -s bash "$output/source/scripts/verify-atomic-set64-native.sh" \
    > "$output/shellcheck.txt" 2>&1

phase=toolchain
run uname -srmo > "$output/platform.txt"
run hostname > "$output/hostname.txt"
run lscpu > "$output/cpu.txt"
run getconf GNU_LIBC_VERSION > "$output/libc.txt"
run getconf PAGESIZE > "$output/page-size.txt"
run git rev-parse HEAD > "$output/repository-head.txt"
run date -u +%FT%TZ > "$output/start-utc.txt"
tools=(gcc-13 clang-18 clang++-18 as ld objcopy objdump readelf shellcheck timeout bash sha256sum)
for tool in "${tools[@]}"; do
    tool_path=$(command -v "$tool")
    printf '%s\t%s\t%s\n' "$tool" "$tool_path" "$(realpath "$tool_path")" >> "$output/tool-paths.tsv"
    run sha256sum "$(realpath "$tool_path")" >> "$output/tool-SHA256SUMS"
    run "$tool" --version > "$output/tool-$tool.txt" 2>&1
done
compilers=(gcc-13 clang-18 clang++-18)
variants=(gcc_c clang_c clang_cpp)
majors=(13 18 18)
operations=(and or xor)
for i in "${!compilers[@]}"; do
    compiler=${compilers[$i]}
    directory="$output/${variants[$i]}"
    mkdir -p "$directory"
    run "$compiler" -dumpversion > "$directory/compiler-version.txt"
    run "$compiler" -dumpmachine > "$directory/compiler-target.txt"
    version=$(< "$directory/compiler-version.txt")
    target=$(< "$directory/compiler-target.txt")
    if [[ ${version%%.*} != "${majors[$i]}" || $target != x86_64*linux* ]]; then
        printf 'Unsupported compiler: %s version=%s target=%s\n' "$compiler" "$version" "$target" >&2
        exit 3
    fi
    run "$compiler" -print-prog-name=as > "$directory/compiler-assembler.txt"
    run "$compiler" -print-prog-name=ld > "$directory/compiler-linker.txt"
done

admit_raw() {
    local file=$1 receipt=$2 operation=$3 size actual opcode expected
    case "$operation" in and) opcode=21 ;; or) opcode=09 ;; xor) opcode=31 ;; *) return 3 ;; esac
    expected="f048${opcode}37c3"
    size=$(wc -c < "$file")
    actual=$(od -An -tx1 -v "$file" | tr -d ' \n')
    printf 'operation=%s\nspan=%s\nactual=%s\nexpected=%s\n' "$operation" "$size" "$actual" "$expected" > "$receipt"
    if [[ $size -ne 5 || $actual != "$expected" ]]; then
        echo 'UNSUPPORTED: exact whole five-byte profile mismatch; no defect claim' >> "$receipt"
        return 3
    fi
}

# Admission uses the entire final .text AND the defined ELF FUNC span. A
# matching interior substring or a shortened symbol cannot certify a routine.
admit_elf() {
    local elf=$1 directory=$2 operation=$3 header text_index symbol
    symbol="atomic_${operation}64_discard"
    local -a text_rows symbol_rows
    mkdir -p "$directory"
    run readelf -h -l -S -s -r -n -W "$elf" > "$directory/elf.txt" || return 3
    run readelf -hW "$elf" > "$directory/header.txt" || return 3
    run readelf -SW "$elf" > "$directory/sections.txt" || return 3
    run readelf -sW "$elf" > "$directory/symbols.txt" || return 3
    run readelf -rW "$elf" > "$directory/relocations.txt" || return 3
    run objdump -h "$elf" > "$directory/section-spans.txt" || return 3
    run objdump -d -Mintel "$elf" > "$directory/disassembly.txt" || return 3
    header=$(< "$directory/header.txt")
    if [[ $header != *ELF64* || $header != *"2's complement, little endian"* ||
        $header != *'EXEC (Executable file)'* || $header != *'Advanced Micro Devices X86-64'* ||
        $(< "$directory/relocations.txt") != *'There are no relocations in this file.'* ]]; then
        echo 'UNSUPPORTED: expected final x86-64 little-endian EXEC without relocations' \
            > "$directory/rejection.txt"
        return 3
    fi
    mapfile -t text_rows < <(awk '$2 == ".text" {print $3, $4, $6}' "$directory/section-spans.txt")
    mapfile -t symbol_rows < <(awk -v expected_symbol="$symbol" '$4 == "FUNC" && $8 == expected_symbol {
        print $2, $3, $5, $6, $7}' "$directory/symbols.txt")
    if [[ ${#text_rows[@]} -ne 1 || ${#symbol_rows[@]} -ne 1 ]]; then
        echo 'UNSUPPORTED: expected one complete .text and one named FUNC' > "$directory/rejection.txt"
        return 3
    fi
    local text_size text_address text_offset symbol_address symbol_size binding visibility section entry
    read -r text_size text_address text_offset <<< "${text_rows[0]}"
    read -r symbol_address symbol_size binding visibility section <<< "${symbol_rows[0]}"
    text_index=$(awk '/\[[ 0-9]+\] \.text / {
        line=$0; sub(/^[[:space:]]*\[/,"",line); sub(/\].*/,"",line);
        gsub(/[[:space:]]/,"",line); print line}' "$directory/sections.txt")
    entry=$(awk '/Entry point address:/ {print $4}' "$directory/header.txt")
    printf 'text_address=%s\ntext_size_hex=%s\ntext_file_offset_hex=%s\nfunction_address=%s\nfunction_size=%s\nfunction_section=%s\ntext_section=%s\nentry=%s\n' \
        "$text_address" "$text_size" "$text_offset" "$symbol_address" "$symbol_size" \
        "$section" "$text_index" "$entry" > "$directory/span.txt"
    if [[ ! $text_size =~ ^[0-9a-fA-F]+$ || ! $text_address =~ ^[0-9a-fA-F]+$ ||
        ! $symbol_address =~ ^[0-9a-fA-F]+$ || ! $symbol_size =~ ^[0-9]+$ ||
        ! $entry =~ ^0x[0-9a-fA-F]+$ || $binding != GLOBAL || $visibility != DEFAULT ||
        $section != "$text_index" || ! $text_index =~ ^[0-9]+$ ]]; then
        echo 'UNSUPPORTED: invalid defined full function span' > "$directory/rejection.txt"
        return 3
    fi
    if (( 16#$text_address != 16#$symbol_address || 16#$text_size != symbol_size ||
        entry != 16#$symbol_address )); then
        echo 'UNSUPPORTED: partial span, extra text or mismatched entry' > "$directory/rejection.txt"
        return 3
    fi
    if ! awk '/^[ ]*[0-9]+ / {name=$2; getline;
        if (/CODE/) {if (name != ".text") bad=1; else found=1}}
        END {exit (bad || !found)}' "$directory/section-spans.txt"; then
        echo 'UNSUPPORTED: unexpected executable section layout' > "$directory/rejection.txt"
        return 3
    fi
    run objcopy --dump-section ".text=$directory/function.bin" "$elf" \
        > "$directory/extraction-stdout.txt" 2> "$directory/extraction-stderr.txt" || return 3
    admit_raw "$directory/function.bin" "$directory/identity.txt" "$operation" || return 3
    run sha256sum "$elf" "$directory/function.bin" > "$directory/file-code-SHA256SUMS"
}

phase=compilation_and_full_span_extraction
binaries=()
names=()
slot_operations=()
for i in "${!compilers[@]}"; do
    compiler=${compilers[$i]}
    standard=gnu2x
    source="$output/source/fixtures/atomic-set64.c"
    [[ ${variants[$i]} != clang_cpp ]] || {
        standard=gnu++2c
        source="$output/source/fixtures/atomic-set64.cpp"
    }
    for operation in "${operations[@]}"; do
        directory="$output/${variants[$i]}/$operation"
        mkdir -p "$directory"
        compile=(-std="$standard" -Os -Wall -Wextra -Werror -fno-lto -fcf-protection=none
            -ffunction-sections -v -c "$source" -o "$directory/function.o")
        record_command "$compiler" "${compile[@]}" > "$directory/compile-arguments.txt"
        run "$compiler" "${compile[@]}" > "$directory/compile-stdout.txt" 2> "$directory/compile-stderr.txt"
        link=(-m elf_x86_64 --build-id=none --gc-sections -z noexecstack
            -e "atomic_${operation}64_discard" -Ttext=0x401000
            -o "$directory/function.elf" "$directory/function.o")
        record_command ld "${link[@]}" > "$directory/link-arguments.txt"
        run ld "${link[@]}" > "$directory/link-stdout.txt" 2> "$directory/link-stderr.txt"
        admit_elf "$directory/function.elf" "$directory" "$operation"
        binaries+=("$directory/function.bin")
        names+=("${variants[$i]}_${operation}64")
        slot_operations+=("$operation")
    done
done

# Owned final ELF negatives independently exercise complete-symbol/text gates.
# The partial span has the correct five .text bytes but a four-byte FUNC.
phase=elf_span_rejections
mkdir -p "$output/source/generated" "$output/elf-rejections"
elf_rejections=0
for operation in "${operations[@]}"; do
for kind in partial-span suffix prefix extra-text retained-relocation wrong-operation; do
    directory="$output/elf-rejections/$operation/$kind"
    mkdir -p "$directory"
    source="$output/source/generated/$operation-$kind.S"
    symbol="atomic_${operation}64_discard"
    actual_operation=$operation
    [[ $kind != wrong-operation ]] || {
        [[ $operation != and ]] && actual_operation=and || actual_operation=xor
    }
    {
        printf '.text\n'
        [[ $kind != prefix ]] || printf '.byte 0x90\n'
        printf '.globl %s\n.type %s,@function\n%s:\n' "$symbol" "$symbol" "$symbol"
        printf '.incbin "gcc_c/%s/function.bin"\n' "$actual_operation"
        [[ $kind != suffix ]] || printf '.byte 0x90\n'
        if [[ $kind == partial-span ]]; then
            printf '.size %s,4\n' "$symbol"
        else
            printf '.size %s,.-%s\n' "$symbol" "$symbol"
        fi
        [[ $kind != extra-text ]] || printf '.byte 0xc3\n'
        if [[ $kind == retained-relocation ]]; then
            printf '.data\n.globl retain_address\nretain_address: .quad %s\n' "$symbol"
        fi
        printf '.section .note.GNU-stack,"",@progbits\n'
    } > "$source"
    (cd "$output" && run gcc-13 -c "$source" -o "$directory/function.o") \
        > "$directory/compile-stdout.txt" 2> "$directory/compile-stderr.txt"
    extra_link=()
    [[ $kind != retained-relocation ]] || extra_link=(--emit-relocs -u retain_address)
    run ld -m elf_x86_64 --build-id=none --gc-sections -z noexecstack -e "$symbol" \
        -Ttext=0x401000 "${extra_link[@]}" -o "$directory/function.elf" "$directory/function.o" \
        > "$directory/link-stdout.txt" 2> "$directory/link-stderr.txt"
    status=0
    admit_elf "$directory/function.elf" "$directory/check" "$operation" || status=$?
    printf '%s\n' "$status" > "$directory/status.txt"
    if [[ $status -ne 3 ]]; then
        echo "Owned unsupported ELF unexpectedly admitted: $operation/$kind" >&2
        exit 1
    fi
    elf_rejections=$((elf_rejections + 1))
done
done
(cd "$output/source" && sha256sum generated/*.S) > "$output/generated-source-SHA256SUMS"

# Malformed containers remain data. Cover parsing and header/symbol admission
# separately from the valid ELF span/operation controls above.
for operation in "${operations[@]}"; do
for kind in empty raw-as-elf truncated-header wrong-machine wrong-entry stripped-symbols; do
    directory="$output/elf-rejections/$operation/$kind"
    mkdir -p "$directory"
    elf="$directory/function.elf"
    case "$kind" in
        empty) : > "$elf" ;;
        raw-as-elf) cp "$output/gcc_c/$operation/function.bin" "$elf" ;;
        truncated-header) head -c 32 "$output/gcc_c/$operation/function.elf" > "$elf" ;;
        wrong-machine)
            cp "$output/gcc_c/$operation/function.elf" "$elf"
            # ELF64 e_machine=183 (AArch64), leaving all code bytes intact.
            printf '\267\000' | run dd of="$elf" bs=1 seek=18 conv=notrunc status=none
            ;;
        wrong-entry)
            cp "$output/gcc_c/$operation/function.elf" "$elf"
            # ELF64 e_entry=0, leaving its complete .text and FUNC intact.
            printf '\000\000\000\000\000\000\000\000' |
                run dd of="$elf" bs=1 seek=24 conv=notrunc status=none
            ;;
        stripped-symbols)
            run objcopy --strip-all "$output/gcc_c/$operation/function.elf" "$elf"
            ;;
    esac
    status=0
    admit_elf "$elf" "$directory/check" "$operation" || status=$?
    printf '%s\n' "$status" > "$directory/status.txt"
    if [[ $status -ne 3 ]]; then
        echo "Owned malformed ELF unexpectedly admitted: $operation/$kind" >&2
        exit 1
    fi
    elf_rejections=$((elf_rejections + 1))
done
done

phase=raw_rejection_inputs
raw_labels=(missing-lock width32 width16 wrong-source memory-source repeated-lock
    operand-prefix address-prefix segment-prefix wrong-operation suffix partial-instruction
    partial-function empty full-elf extra-gpr-write retained-flags)
raw_rejections=0
for operation in "${operations[@]}"; do
    directory="$output/raw-rejections/$operation"
    mkdir -p "$directory"
    case "$operation" in and) opcode=21 ;; or) opcode=09 ;; xor) opcode=31 ;; esac
    other=21
    [[ $operation != and ]] || other=31
    memory_opcode=$(printf '%02x' "$((16#$opcode + 2))")
    for label in "${raw_labels[@]}"; do
        file="$directory/$label.bin"
        case "$label" in
            missing-lock) printf '%b' "\x48\x${opcode}\x37\xc3" > "$file" ;;
            width32) printf '%b' "\xf0\x${opcode}\x37\xc3" > "$file" ;;
            width16) printf '%b' "\xf0\x66\x${opcode}\x37\xc3" > "$file" ;;
            wrong-source) printf '%b' "\xf0\x48\x${opcode}\x17\xc3" > "$file" ;;
            memory-source) printf '%b' "\xf0\x48\x${memory_opcode}\x37\xc3" > "$file" ;;
            repeated-lock) printf '%b' "\xf0\xf0\x48\x${opcode}\x37\xc3" > "$file" ;;
            operand-prefix) printf '%b' "\x66\xf0\x48\x${opcode}\x37\xc3" > "$file" ;;
            address-prefix) printf '%b' "\x67\xf0\x48\x${opcode}\x37\xc3" > "$file" ;;
            segment-prefix) printf '%b' "\x3e\xf0\x48\x${opcode}\x37\xc3" > "$file" ;;
            wrong-operation) printf '%b' "\xf0\x48\x${other}\x37\xc3" > "$file" ;;
            suffix) cat "$output/gcc_c/$operation/function.bin" > "$file"; printf '\220' >> "$file" ;;
            partial-instruction) head -c 3 "$output/gcc_c/$operation/function.bin" > "$file" ;;
            partial-function) head -c 4 "$output/gcc_c/$operation/function.bin" > "$file" ;;
            empty) : > "$file" ;;
            full-elf) cp "$output/gcc_c/$operation/function.elf" "$file" ;;
            extra-gpr-write) printf '%b' "\xf0\x48\x${opcode}\x37\x48\xf7\xd0\xc3" > "$file" ;;
            retained-flags) printf '%b' "\x9c\xf0\x48\x${opcode}\x37\x9d\xc3" > "$file" ;;
        esac
        status=0
        admit_raw "$file" "$directory/$label.txt" "$operation" || status=$?
        printf '%s\n' "$status" > "$directory/$label.status.txt"
        [[ $status -eq 3 ]]
        raw_rejections=$((raw_rejections + 1))
    done
done

phase=observer_build_and_execution
observers=(gcc-13 clang-18)
observer_variants=(gcc clang)
binding_rejections=0
for i in "${!observers[@]}"; do
    compiler=${observers[$i]}
    directory="$output/observers/${observer_variants[$i]}"
    mkdir -p "$directory"
    observer=(-std=gnu2x -O2 -Wall -Wextra -Werror -Wformat=2 -Wshadow -fno-lto
        -fcf-protection=none -fno-pie -no-pie -pthread -v '-Wl,--build-id=none,-z,noexecstack'
        "$output/source/fixtures/atomic-set64-check.c"
        "$output/source/fixtures/atomic-set64-check.S" -o "$directory/native-check.elf")
    record_command "$compiler" "${observer[@]}" > "$directory/compile-arguments.txt"
    (cd "$output" && run "$compiler" "${observer[@]}") \
        > "$directory/compile-stdout.txt" 2> "$directory/compile-stderr.txt"
    run readelf -h -l -S -s -r -n -W "$directory/native-check.elf" > "$directory/elf.txt"
    run objdump -d -Mintel -j .text -j .edsl_set64 "$directory/native-check.elf" \
        > "$directory/disassembly.txt"
    run objcopy --dump-section ".edsl_set64=$directory/executed-section.bin" "$directory/native-check.elf"
    status=0
    record_command timeout 60 "$directory/native-check.elf" "${binaries[@]}" > "$directory/native-arguments.txt"
    run timeout 60 "$directory/native-check.elf" "${binaries[@]}" \
        > "$directory/native-results.txt" 2> "$directory/native-errors.txt" || status=$?
    printf '%s\n' "$status" > "$directory/native-status.txt"
    if [[ $status -ne 0 ]]; then
        echo "Native run incomplete: ${observer_variants[$i]} exit=$status (timeout/signal is inconclusive)" >&2
        exit "$status"
    fi
    # Invalid raw files and foreign-operation exact extractions stay DATA.
    # Each loaded slot rejects every own-profile mutant before setup/output.
    for index in "${!binaries[@]}"; do
    for label in "${raw_labels[@]}"; do
        operation=${slot_operations[$index]}
        rejection="$directory/rejections/${names[$index]}/$label"
        mkdir -p "$rejection"
        inputs=("${binaries[@]}")
        inputs[index]="$output/raw-rejections/$operation/$label.bin"
        status=0
        record_command timeout 10 "$directory/native-check.elf" "${inputs[@]}" > "$rejection/arguments.txt"
        run timeout 10 "$directory/native-check.elf" "${inputs[@]}" \
            > "$rejection/stdout.txt" 2> "$rejection/stderr.txt" || status=$?
        printf '%s\n' "$status" > "$rejection/status.txt"
        if [[ $status -ne 2 || -s "$rejection/stdout.txt" ||
            $(< "$rejection/stderr.txt") != "Extraction rejected before native execution: ${names[$index]}" ]]; then
            echo "Unexpected extraction rejection: ${observer_variants[$i]}/${names[$index]}/$label exit=$status" >&2
            exit 1
        fi
        binding_rejections=$((binding_rejections + 1))
    done
    # Even an otherwise admitted extraction of a DIFFERENT operation is denied.
    for other_operation in "${operations[@]}"; do
        [[ $other_operation != "${slot_operations[$index]}" ]] || continue
        rejection="$directory/rejections/${names[$index]}/foreign-$other_operation"
        mkdir -p "$rejection"
        inputs=("${binaries[@]}")
        inputs[index]="$output/gcc_c/$other_operation/function.bin"
        status=0
        run timeout 10 "$directory/native-check.elf" "${inputs[@]}" \
            > "$rejection/stdout.txt" 2> "$rejection/stderr.txt" || status=$?
        printf '%s\n' "$status" > "$rejection/status.txt"
        if [[ $status -ne 2 || -s "$rejection/stdout.txt" ||
            $(< "$rejection/stderr.txt") != "Extraction rejected before native execution: ${names[$index]}" ]]; then
            echo "Unexpected foreign-operation extraction acceptance: ${names[$index]}/$other_operation" >&2
            exit 1
        fi
        binding_rejections=$((binding_rejections + 1))
    done
    done
done

phase=provenance_and_source_stability
cat > "$output/native-scope.txt" <<'SCOPE'
OWNED FINITE NATIVE OBSERVATIONS ONLY. Lean proof-status: NOT RUN.
Linux x86-64/System V, fixed compiler majors GCC13 and Clang18. GNU23 C
inputs use -std=gnu2x. Clang18 additionally compiles a GNU++26 SUBSET using
-std=gnu++2c; no complete C++26 implementation/support is asserted. GCC13
is not used for a C++26 input. All nine independently final-linked functions
(three compilers/languages times AND/OR/XOR) discard the fetched old word.
Each entire .text and GLOBAL DEFAULT FUNC span must agree with the entry,
be exactly five bytes f0 48 {21,09,31} 37 c3 for its requested operation,
be the sole executable section, and have no relocations. Compiler drift is
UNSUPPORTED, never a defect. Tool/source/commands and exact spans are saved.

Both GCC13 and Clang18 build the observer C/assembly with warnings as errors.
All nine complete final byte extractions are copied verbatim with .incbin.
Every loaded span and all file bytes are compared before any probe, setup,
worker or positive stdout. Inputs are only data, never entry addresses.
Bare function ELFs are never launched as processes. The five byte positions
are independent of loaded address. No source semantics are inferred by this
byte identity check. Owned malformed/raw/ELF/operation/GPR/flag mutants are
rejected by those byte/span gates BEFORE any native execution. Separately,
safe project-owned assembly semantic mutants exercise the behavior oracle;
they are intentionally executed and must produce a categorized witness.
The nine compiler slots pass the same behavior oracle. This distinction is
recorded explicitly; malformed file inputs are never executed.

All raw slots access actual atomic_init-initialized _Atomic uint64_t storage
with checked lock-free representation, size8, 64-byte alignment and one
virtual 64-byte line/4-KiB page. Its lifetime includes all checked joins.
Stores reset it only quiescently; C loads are atomic, and representation bytes
are inspected only when quiescent. The C++ source takes std::atomic<uint64_t>*,
uses the standard fetch methods, and has C linkage names. The C observer
executes separate assembly slots on its C atomic object. It NEVER casts a C
atomic object to a C++ atomic object, or claims C++ object-model correctness
for executing those bytes. These are machine observations, not calls to a
C++ source function. C/C++ source-to-machine preservation is NOT established.

Independent per-bit finite-set contracts check intersection, union and
symmetric difference; independent byte positions check little-endian memory.
No whole-word AND/OR/XOR operation produces expected values. Defined flags
CF/PF/ZF/SF/OF, all15 non-RSP GPRs, real RSP/return slot, stack qwords, the64
preceding and56 following bytes, and nonarithmetic flag preservation are
checked. All256 arithmetic/DF/ID profiles are effectively installed/captured.
DF=1 is a raw contract probe, restored before C. AF is undefined: explicit
AF=0 and AF=1 controls for EACH operation must both pass. Each operation's
UNLOCKED single-thread control must PASS; finite value/flag/ABI observations
do not establish LOCK atomicity. Unlocked controls never run concurrently.

Cases cover every one-bit membership input, zero/equal/high/low words,
ordered boundaries, three deterministic seeds, repeated/live sequences,
and independently specified endian/cancellation literals. Safe semantic
mutants cover 16/32-bit widths, wrong source/mask/operation, fetched-old RAX,
every non-RSP register, RET imbalance, adjacent guards, each defined flag,
retained flags, DF and ID. Their witnesses are synthetic project-owned
negatives, never real findings or compiler defect claims.

Four pthread workloads per nine-slot extraction use8 workers with257/258
rounds of8 masks (odd, even and mixed multiplicities). All create/join errors,
returned identities and completion counts are checked before quiescent
readback. A separately counted per-bit HISTORY checks AND membership in all
requested masks, OR membership in any mask, and XOR parity of every request;
no idempotence shortcut drops repeated XOR events. Guards and endian bytes
are checked after joins. Initial words, sparse/disjoint/high/overlapping and
zero masks are covered. No event/access trace or all-schedules theorem is
observed. LOCK/CPU physical refinement, C SC/compiler preservation,
pthread/kernel correctness and managed Lean lifecycle remain unestablished.

Raw negatives cover missing LOCK, narrow widths, wrong register/opcode,
repeated/operand/address/segment prefixes, suffixes, truncation, empty/full
ELF-as-raw and appended GPR/flag operations. Final ELF negatives cover partial
FUNC span, hidden prefix, suffix/extra text, retained relocation and wrong
operation under the right symbol. Empty/raw/truncated containers, a foreign
ELF machine, mismatched entry and removed symbols also fail before execution.
Every one of the9 loaded slots rejects all
applicable raw cases and both other admitted operations before execution.
Signals, timeouts, unsupported code and proof failures establish no defect.

Physical interpretation still assumes ordinary coherent WB RAM, stable
translation/permissions/code, contiguous injective physical backing and
compatible physical line/page geometry, no unmanaged aliases/overlapping
mixed-width access, MMIO/DMA/non-temporal interference, normal user control
state, CET off, compatible stack alignment-check state, private context and
accessible canonical stack/return, and native atomic lifetime/access
discipline through joins. Virtual geometry does not verify physical
assumptions. The host may be virtualized; this proves no vendor conformity,
whole OS, C++ object model, compiler/bootstrap, or Lean theorem.
SCOPE
printf 'PASS elf_span_rejections=%s raw_profile_rejections=%s pre_execution_binding_rejections=%s\n' \
    "$elf_rejections" "$raw_rejections" "$binding_rejections" > "$output/extraction-results.txt"
run sha256sum --check "$output/source-SHA256SUMS" > "$output/source-stability.txt"
(cd "$output/source" && sha256sum --check "$output/generated-source-SHA256SUMS") \
    > "$output/generated-source-check.txt"
byte_files=()
for i in "${!compilers[@]}"; do
    for operation in "${operations[@]}"; do
        directory="$output/${variants[$i]}/$operation"
        byte_files+=("$directory/function.o" "$directory/function.elf" "$directory/function.bin")
    done
done
for variant in "${observer_variants[@]}"; do
    byte_files+=("$output/observers/$variant/native-check.elf"
        "$output/observers/$variant/executed-section.bin")
done
run sha256sum "${byte_files[@]}" > "$output/byte-SHA256SUMS"
run sha256sum "$output/commands.txt" > "$output/command-SHA256SUMS"
echo 'PASS: finite native observations, semantic mutants and extraction gates; proof-status NOT RUN' \
    > "$output/result.txt"
phase=complete
complete=1
