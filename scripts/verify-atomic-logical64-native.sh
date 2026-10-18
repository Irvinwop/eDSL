#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail
export LC_ALL=C
if [[ $# -ne 0 ]]; then
    echo 'usage: verify-atomic-logical64-native.sh' >&2
    exit 2
fi
if [[ $(uname -sm) != 'Linux x86_64' ]]; then
    echo 'AtomicLogical64 native evidence requires Linux x86_64 / System V' >&2
    exit 2
fi
cd "$(dirname "${BASH_SOURCE[0]}")/.."
# All evidence stays in this checkout on the invoking HOME machine. No SSH,
# unknown program loader, executable mmap, or existing binary input is used.
archive=${EDSL_ATOMIC64_NATIVE_OUTPUT:-artifacts/atomic-logical64-native}
mkdir -p "$archive"
archive=$(cd "$archive" && pwd -P)
output=$(mktemp -d "$archive/run.XXXXXXXX")
printf 'AtomicLogical64 native evidence: %s\n' "$output"
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
        printf 'AtomicLogical64 manifest verification failed: %s\n' "$output" >&4
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
echo 'NOT RUN: Lean proofs/builds/imports, kernel replay, theorem audit, source/C-SC preservation' \
    > "$output/proof-status.txt"

phase=snapshot
source_files=(fixtures/atomic-logical64.c fixtures/atomic-logical64-check.c
    fixtures/atomic-logical64-check.S scripts/verify-atomic-logical64-native.sh)
run sha256sum "${source_files[@]}" > "$output/source-SHA256SUMS"
for file in "${source_files[@]}"; do
    run install -D -m 0644 "$file" "$output/source/$file"
done
(cd "$output/source" && sha256sum --check "$output/source-SHA256SUMS") > "$output/source-copy-check.txt"
run bash -n "$output/source/scripts/verify-atomic-logical64-native.sh"
run shellcheck -s bash "$output/source/scripts/verify-atomic-logical64-native.sh" \
    > "$output/shellcheck.txt" 2>&1

phase=toolchain
run uname -srmo > "$output/platform.txt"
run hostname > "$output/hostname.txt"
run lscpu > "$output/cpu.txt"
run getconf GNU_LIBC_VERSION > "$output/libc.txt"
run getconf PAGESIZE > "$output/page-size.txt"
run git rev-parse HEAD > "$output/repository-head.txt"
run date -u +%FT%TZ > "$output/start-utc.txt"
tools=(gcc-13 clang-18 as ld objcopy objdump readelf shellcheck timeout bash sha256sum)
for tool in "${tools[@]}"; do
    tool_path=$(command -v "$tool")
    printf '%s\t%s\t%s\n' "$tool" "$tool_path" "$(realpath "$tool_path")" >> "$output/tool-paths.tsv"
    run sha256sum "$(realpath "$tool_path")" >> "$output/tool-SHA256SUMS"
    run "$tool" --version > "$output/tool-$tool.txt" 2>&1
done
compilers=(gcc-13 clang-18)
variants=(gcc clang)
majors=(13 18)
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
    local file=$1 receipt=$2 size actual
    size=$(wc -c < "$file")
    actual=$(od -An -tx1 -v "$file" | tr -d ' \n')
    printf 'span=%s\nactual=%s\nexpected=f0480937c3\n' "$size" "$actual" > "$receipt"
    if [[ $size -ne 5 || $actual != f0480937c3 ]]; then
        echo 'UNSUPPORTED: exact whole five-byte profile mismatch; no defect claim' >> "$receipt"
        return 3
    fi
}

# Admission uses the entire final .text AND the defined ELF FUNC span. A
# matching interior substring or a shortened symbol cannot certify a routine.
admit_elf() {
    local elf=$1 directory=$2 header text_index
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
    mapfile -t symbol_rows < <(awk '$4 == "FUNC" && $8 == "atomic_or64_discard" {
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
    admit_raw "$directory/function.bin" "$directory/identity.txt" || return 3
    run sha256sum "$elf" "$directory/function.bin" > "$directory/file-code-SHA256SUMS"
}

phase=compilation_and_full_span_extraction
for i in "${!compilers[@]}"; do
    compiler=${compilers[$i]}
    directory="$output/${variants[$i]}"
    compile=(-std=gnu2x -Os -Wall -Wextra -Werror -fno-lto -fcf-protection=none
        -ffunction-sections -v -c "$output/source/fixtures/atomic-logical64.c"
        -o "$directory/function.o")
    record_command "$compiler" "${compile[@]}" > "$directory/compile-arguments.txt"
    run "$compiler" "${compile[@]}" > "$directory/compile-stdout.txt" 2> "$directory/compile-stderr.txt"
    link=(-m elf_x86_64 --build-id=none --gc-sections -z noexecstack
        -e atomic_or64_discard -Ttext=0x401000 -o "$directory/function.elf" "$directory/function.o")
    record_command ld "${link[@]}" > "$directory/link-arguments.txt"
    run ld "${link[@]}" > "$directory/link-stdout.txt" 2> "$directory/link-stderr.txt"
    admit_elf "$directory/function.elf" "$directory"
done

# Independently exercise ELF-span rejection with owned generated sources.
# The partial-span ELF has exactly the right five .text bytes but size=4.
phase=elf_span_rejections
mkdir -p "$output/source/generated" "$output/elf-rejections"
elf_rejections=0
for kind in partial-span suffix prefix extra-text retained-relocation; do
    directory="$output/elf-rejections/$kind"
    mkdir -p "$directory"
    source="$output/source/generated/$kind.S"
    {
        printf '.text\n'
        [[ $kind != prefix ]] || printf '.byte 0x90\n'
        printf '.globl atomic_or64_discard\n.type atomic_or64_discard,@function\natomic_or64_discard:\n'
        printf '.incbin "gcc/function.bin"\n'
        [[ $kind != suffix ]] || printf '.byte 0x90\n'
        if [[ $kind == partial-span ]]; then
            printf '.size atomic_or64_discard,4\n'
        else
            printf '.size atomic_or64_discard,.-atomic_or64_discard\n'
        fi
        [[ $kind != extra-text ]] || printf '.byte 0xc3\n'
        if [[ $kind == retained-relocation ]]; then
            printf '.data\n.globl retain_address\nretain_address: .quad atomic_or64_discard\n'
        fi
        printf '.section .note.GNU-stack,"",@progbits\n'
    } > "$source"
    (cd "$output" && run gcc-13 -c "$source" -o "$directory/function.o") \
        > "$directory/compile-stdout.txt" 2> "$directory/compile-stderr.txt"
    extra_link=()
    [[ $kind != retained-relocation ]] || extra_link=(--emit-relocs -u retain_address)
    run ld -m elf_x86_64 --build-id=none --gc-sections -z noexecstack -e atomic_or64_discard \
        -Ttext=0x401000 "${extra_link[@]}" -o "$directory/function.elf" "$directory/function.o" \
        > "$directory/link-stdout.txt" 2> "$directory/link-stderr.txt"
    status=0
    admit_elf "$directory/function.elf" "$directory/check" || status=$?
    printf '%s\n' "$status" > "$directory/status.txt"
    if [[ $status -ne 3 ]]; then
        echo "Owned unsupported ELF unexpectedly admitted: $kind" >&2
        exit 1
    fi
    elf_rejections=$((elf_rejections + 1))
done
(cd "$output/source" && sha256sum generated/*.S) > "$output/generated-source-SHA256SUMS"

phase=raw_rejection_inputs
mkdir -p "$output/raw-rejections"
raw_labels=(missing-lock width32 width16 wrong-source memory-source repeated-lock
    operand-prefix address-prefix segment-prefix suffix partial-instruction partial-function empty full-elf)
for label in "${raw_labels[@]}"; do
    file="$output/raw-rejections/$label.bin"
    case "$label" in
        missing-lock) printf '\110\011\067\303' > "$file" ;;
        width32) printf '\360\011\067\303' > "$file" ;;
        width16) printf '\360\146\011\067\303' > "$file" ;;
        wrong-source) printf '\360\110\011\027\303' > "$file" ;;
        memory-source) printf '\360\110\013\067\303' > "$file" ;;
        repeated-lock) printf '\360\360\110\011\067\303' > "$file" ;;
        operand-prefix) printf '\146\360\110\011\067\303' > "$file" ;;
        address-prefix) printf '\147\360\110\011\067\303' > "$file" ;;
        segment-prefix) printf '\076\360\110\011\067\303' > "$file" ;;
        suffix) cat "$output/gcc/function.bin" > "$file"; printf '\220' >> "$file" ;;
        partial-instruction) head -c 3 "$output/gcc/function.bin" > "$file" ;;
        partial-function) head -c 4 "$output/gcc/function.bin" > "$file" ;;
        empty) : > "$file" ;;
        full-elf) cp "$output/gcc/function.elf" "$file" ;;
    esac
    status=0
    admit_raw "$file" "$output/raw-rejections/$label.txt" || status=$?
    printf '%s\n' "$status" > "$output/raw-rejections/$label.status.txt"
    [[ $status -eq 3 ]]
done

phase=observer_build_and_execution
binaries=("$output/gcc/function.bin" "$output/clang/function.bin")
names=(gcc_or64 clang_or64)
binding_rejections=0
for i in "${!compilers[@]}"; do
    compiler=${compilers[$i]}
    directory="$output/observers/${variants[$i]}"
    mkdir -p "$directory"
    observer=(-std=gnu2x -O2 -Wall -Wextra -Werror -Wformat=2 -Wshadow -fno-lto
        -fcf-protection=none -fno-pie -no-pie -pthread -v '-Wl,--build-id=none,-z,noexecstack'
        "$output/source/fixtures/atomic-logical64-check.c"
        "$output/source/fixtures/atomic-logical64-check.S" -o "$directory/native-check.elf")
    record_command "$compiler" "${observer[@]}" > "$directory/compile-arguments.txt"
    (cd "$output" && run "$compiler" "${observer[@]}") \
        > "$directory/compile-stdout.txt" 2> "$directory/compile-stderr.txt"
    run readelf -h -l -S -s -r -n -W "$directory/native-check.elf" > "$directory/elf.txt"
    run objdump -d -Mintel -j .text -j .edsl_atomic64 "$directory/native-check.elf" \
        > "$directory/disassembly.txt"
    run objcopy --dump-section ".edsl_atomic64=$directory/executed-section.bin" "$directory/native-check.elf"
    status=0
    record_command timeout 60 "$directory/native-check.elf" "${binaries[@]}" > "$directory/native-arguments.txt"
    run timeout 60 "$directory/native-check.elf" "${binaries[@]}" \
        > "$directory/native-results.txt" 2> "$directory/native-errors.txt" || status=$?
    printf '%s\n' "$status" > "$directory/native-status.txt"
    if [[ $status -ne 0 ]]; then
        echo "Native run incomplete: ${variants[$i]} exit=$status (timeout/signal is inconclusive)" >&2
        exit "$status"
    fi
    # Invalid raw files are compared as DATA against both complete loaded
    # slots. Every rejection must occur before setup/probes/positive stdout.
    for index in "${!binaries[@]}"; do
    for label in "${raw_labels[@]}"; do
        rejection="$directory/rejections/${names[$index]}/$label"
        mkdir -p "$rejection"
        inputs=("${binaries[@]}")
        inputs[index]="$output/raw-rejections/$label.bin"
        status=0
        record_command timeout 10 "$directory/native-check.elf" "${inputs[@]}" > "$rejection/arguments.txt"
        run timeout 10 "$directory/native-check.elf" "${inputs[@]}" \
            > "$rejection/stdout.txt" 2> "$rejection/stderr.txt" || status=$?
        printf '%s\n' "$status" > "$rejection/status.txt"
        if [[ $status -ne 2 || -s "$rejection/stdout.txt" ||
            $(< "$rejection/stderr.txt") != "Extraction rejected before native execution: ${names[$index]}" ]]; then
            echo "Unexpected extraction rejection: ${variants[$i]}/${names[$index]}/$label exit=$status" >&2
            exit 1
        fi
        binding_rejections=$((binding_rejections + 1))
    done
    done
done

phase=provenance_and_source_stability
cat > "$output/native-scope.txt" <<'SCOPE'
OWNED FINITE NATIVE OBSERVATIONS ONLY. Lean proof-status: NOT RUN.
Linux x86-64/System V, fixed supported compiler majors GCC13 and Clang18.
Both freshly compile the archived GNU23 C fixture with -std=gnu2x (the GNU23
spelling supported by these versions), -Os -Wall -Wextra -Werror -fno-lto
-fcf-protection=none -ffunction-sections. It discards seq_cst atomic_fetch_or's
old word; no old64 return promise. Source order is not inferred from bytes.
Each final ld-linked ELF must be EXEC/ELF64/little-endian/x86-64, without any
relocations. The entry, GLOBAL DEFAULT defined FUNC address/size, and entire
executable .text span agree. No extra executable section is allowed. The full
five bytes must equal f0 48 09 37 c3. Compiler drift is unsupported, not a
defect. Both files and complete extractions are hashed; metadata/disassembly,
tool paths/versions/hashes, sources and command vectors are retained.

Both compilers also build the owned C/asm observer with warnings as errors.
Its .incbin slots contain the ACTUAL fresh complete extractions. The loaded
start/end span and exact data-file/loaded-byte identity are checked for both
slots before any native probe, worker, or positive stdout. No file input is
used as an entry address. Bare routine ELFs are never launched as processes.
The same position-independent five bytes execute at their new linked slot
addresses. Observer ELF metadata, executed section and hashes are retained.

The actual object is atomic_init-initialized _Atomic uint64_t, lock-free on
this host, 64-byte aligned, and wholly in one virtual line/4-KiB page. Atomic
stores reset it only with no active workers. Atomic loads observe it; raw
object bytes are inspected only while quiescent. Its 64 preceding and 56
following bytes are checked against pre-call snapshots. A separate per-bit
membership oracle checks all64 bits; a byte-position oracle checks endian
readback, plus literal 81 00 00 00 01 00 00 80. All 15 non-RSP GPRs, including
RAX, RDI and source RSI, must match the installed full64 inputs. Real RSP
balance, the actual caller return slot and four stack guard qwords are checked.
The raw observer installs all 256 arithmetic/DF/ID flag profiles, verifies the
effective installation, captures defined CF/PF/ZF/SF/OF, and checks preserved
nonarithmetic flags. AF is unconstrained: separate controls force AF=0 and 1
and must both pass. DF=1 probes exercise the raw machine contract; the observer
restores host DF/flags/stack before returning to ordinary C. Privileged flags
are only their actual effective user values; TF/AC and arbitrary control
states are not installed. Recovery globals are single-threaded only.

Cases include ordered boundary pairs, each bit's four membership combinations
with other bits empty/full, all pre-flag profiles, three deterministic seeds,
zero/equal masks and live sequences of overlapping/repeated/high/low masks.
Safe owned mutants test narrowed widths, wrong mask/source/operation,
fetched-old RAX, every non-RSP GPR, RET imbalance, both adjacent guard sides,
each defined flag, retained arithmetic flags, DF and ID. Each rejection prints
its actual witness/category. Synthetic mutants are not compiler defects or
real security findings. A deliberately UNLOCKED full64 control PASSES the
single-thread observation oracle; this documents its inability to establish
LOCK. It is not used as a concurrent negative or atomicity claim.

Four finite pthread workloads per extraction use eight workers, each making
2048 rounds of eight calls: disjoint high/low bits (including bit63), high
bits with retained low data, overlapping/repeated/zero masks, seeded sparse
masks. Every pthread_create/join and returned identity is checked. A separate
membership set from the initial word and requested masks checks the final
word/bytes after joins; guards and worker completion counts are checked.
These observations do not prove all schedules, physical indivisibility,
LOCK/CPU behavior, C SC axioms, compiler refinement, pthread/kernel correctness,
linearization traces or managed Lean lifecycle. No unlocked-vs-locked
concurrency distinction is claimed. No event/access trace is observed.

Raw rejection cases cover missing LOCK, 16/32-bit width, wrong source/opcode,
duplicate/operand/address/segment prefixes, suffix, truncated instruction/
function, empty input and full ELF-as-raw. Both loaded slots reject every
case before probing under both observers. Owned synthetic final ELFs also
reject partial FUNC span (correct full five .text bytes, symbol size=4),
suffix, hidden prefix/extra text and retained relocations. Unsupported input,
signals, faults, timeouts and failed checks establish no security defect.

Physical interpretation still assumes ordinary coherent WB RAM, stable
translation/permissions/code, contiguous injective physical backing with
compatible physical line/page geometry, no unmanaged aliases/overlapping
mixed-width accesses, MMIO/DMA/non-temporal interference, normal four-level
user control state, CET off, compatible stack alignment-check state, private
context preservation, actual accessible canonical caller stack/return and
native atomic lifetime/access discipline through all joins. Virtual geometry
checks do not verify these physical assumptions. The recorded host is one
environment, potentially virtualized; no architecture/vendor conformance or
whole-OS theorem follows. No Lean/toolchain bootstrap proof is run here.
SCOPE
printf 'PASS elf_span_rejections=%s raw_profile_rejections=%s pre_execution_binding_rejections=%s\n' \
    "$elf_rejections" "${#raw_labels[@]}" "$binding_rejections" > "$output/extraction-results.txt"
run sha256sum --check "$output/source-SHA256SUMS" > "$output/source-stability.txt"
(cd "$output/source" && sha256sum --check "$output/generated-source-SHA256SUMS") \
    > "$output/generated-source-check.txt"
byte_files=("$output/gcc/function.o" "$output/gcc/function.elf" "${binaries[0]}"
    "$output/clang/function.o" "$output/clang/function.elf" "${binaries[1]}"
    "$output/observers/gcc/native-check.elf" "$output/observers/gcc/executed-section.bin"
    "$output/observers/clang/native-check.elf" "$output/observers/clang/executed-section.bin")
run sha256sum "${byte_files[@]}" > "$output/byte-SHA256SUMS"
run sha256sum "$output/commands.txt" > "$output/command-SHA256SUMS"
echo 'PASS: finite native observations, semantic mutants and extraction gates; proof-status NOT RUN' \
    > "$output/result.txt"
phase=complete
complete=1
