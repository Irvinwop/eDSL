#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."
mode=${1:---native}
if (( $# > 1 )) || [[ $mode != --native && $mode != --prepare-only ]]; then
    echo 'usage: verify-futex-predicate-native.sh [--native|--prepare-only]' >&2
    exit 2
fi
if [[ $mode == --native && $(uname -sm) != 'Linux x86_64' ]]; then
    echo 'NOTRUN: native predicate observer requires Linux x86_64; formal=NOTRUN grading=NOTRUN' >&2
    exit 2
fi

output=${EDSL_FUTEX_PREDICATE_OUTPUT:-.cache/futex-predicate-loop/native-$(date -u +%Y%m%dT%H%M%SZ)-$$}
mkdir -p "$(dirname "$output")"
if [[ -e $output ]]; then
    echo "Refusing to overwrite evidence directory: $output" >&2
    exit 2
fi
mkdir "$output"
exec 3> "$output/commands.txt"
sources=(fixtures/futex-predicate-wait.S fixtures/futex-predicate-no-recheck.S
    fixtures/futex-predicate-trampoline.S fixtures/futex-predicate-check.c
    fixtures/futex-publish.S scripts/verify-futex-predicate-native.sh)
native_status=NOTRUN
object_count=0
standalone_count=0
native_count=0

run() {
    printf '+ ' >&3
    printf '%q ' "$@" >&3
    printf '\n' >&3
    local command_status=0
    "$@" || command_status=$?
    printf 'exit=%d\n' "$command_status" >&3
    return "$command_status"
}

hash_sources() {
    if command -v sha256sum > /dev/null 2>&1; then
        run sha256sum "${sources[@]}"
    else
        run shasum -a 256 "${sources[@]}"
    fi
}

finish() {
    local exit_status=$?
    trap - EXIT
    set +e
    hash_sources > "$output/source-after.SHA256SUMS"
    local hash_status=$?
    if (( hash_status != 0 )); then exit_status=1
    elif ! run cmp "$output/source.SHA256SUMS" "$output/source-after.SHA256SUMS"; then
        echo 'FAIL: native sources changed during evidence collection' >&2
        exit_status=1
    fi
    if [[ $native_status == RUNNING ]] && (( exit_status != 0 )); then native_status=FAIL; fi
    {
        printf 'mode=%s\nexit=%d\nnative=%s\nformal=NOTRUN\ngrading=NOTRUN\n' \
            "$mode" "$exit_status" "$native_status"
        printf 'assembled_exact_object_sets=%d\nchecked_standalone_ELF_sets=%d\n' \
            "$object_count" "$standalone_count"
        printf 'checked_final_native_harnesses=%d\n' "$native_count"
        printf 'No proof CLI, raw/ELF certificates, universal resource admission or workflow wiring.\n'
        printf 'Watchdogs/bounds are inconclusive observations, not progress/fairness/kernel refinement.\n'
        printf 'ptrace mismatch injection uses real WAIT -EAGAIN and a stopped-child W/P reset;\n'
        printf 'parent FUTEX_PRIVATE wake is not used to select a child-process waiter.\n'
        printf 'Untraced WAKE selections witness requeue, not individual raw WAIT exits or memory-order refinement.\n'
    } > "$output/result.txt"
    exec 3>&-
    local manifest_status=0
    if command -v sha256sum > /dev/null 2>&1; then
        (cd "$output" && find . -type f ! -name ARTIFACTS.SHA256SUMS -exec sha256sum {} +) \
            > "$output/ARTIFACTS.SHA256SUMS" || manifest_status=$?
    else
        (cd "$output" && find . -type f ! -name ARTIFACTS.SHA256SUMS -exec shasum -a 256 {} +) \
            > "$output/ARTIFACTS.SHA256SUMS" || manifest_status=$?
    fi
    if (( manifest_status != 0 )); then
        echo 'FAIL: evidence manifest could not be completed' >&2
        rm -f "$output/result.txt" "$output/ARTIFACTS.SHA256SUMS"
        exit_status=1
    else
        cat "$output/result.txt"
    fi
    printf 'Evidence: %s\n' "$output"
    exit "$exit_status"
}
trap finish EXIT

hash_sources > "$output/source.SHA256SUMS"
run uname -a > "$output/host.txt"
run git rev-parse HEAD > "$output/git-head.txt"
run git branch --show-current > "$output/git-branch.txt"

find_tool() {
    local requested=$1 llvm_name=$2
    if command -v "$requested" > /dev/null 2>&1; then command -v "$requested"
    elif command -v "$llvm_name" > /dev/null 2>&1; then command -v "$llvm_name"
    elif [[ -x /opt/homebrew/opt/llvm/bin/$llvm_name ]]; then printf '%s\n' "/opt/homebrew/opt/llvm/bin/$llvm_name"
    else echo "Missing tool: $requested or $llvm_name" >&2; return 2
    fi
}
objcopy=$(find_tool "${EDSL_OBJCOPY:-objcopy}" llvm-objcopy)
objdump=$(find_tool "${EDSL_OBJDUMP:-objdump}" llvm-objdump)
readelf=$(find_tool "${EDSL_READELF:-readelf}" llvm-readelf)
if [[ $(uname -s) != Linux && -z ${EDSL_OBJDUMP:-} && -x /opt/homebrew/opt/llvm/bin/llvm-objdump ]]; then
    objdump=/opt/homebrew/opt/llvm/bin/llvm-objdump
fi
run "$objcopy" --version > "$output/objcopy.txt"
run "$objdump" --version > "$output/objdump.txt"
run "$readelf" --version > "$output/readelf.txt"

printf '\x8b\x07\x83\xf8\x00\x75\x16\xb8\xca\x00\x00\x00\xbe\x80\x00\x00\x00\x0f\x05\xb8\x01\x00\x00\x00\x83\xf8\x00\x75\xe3\xc3' > "$output/wait.expected.bin"
printf '\x8b\x07\x83\xf8\x00\x75\x16\xb8\xca\x00\x00\x00\xbe\x80\x00\x00\x00\x0f\x05\xb8\x01\x00\x00\x00\x83\xf8\x00\x75\x00\xc3' > "$output/no-recheck.expected.bin"
printf '\xb8\x44\x33\x22\x11\x89\x06\xb8\x01\x00\x00\x00\x87\x07\xb8\xca\x00\x00\x00\xbe\x81\x00\x00\x00\xba\x01\x00\x00\x00\x0f\x05\xc3' > "$output/publish.expected.bin"

check_window() {
    local image=$1 section=$2 symbol=$3 expected_size=$4 expected=$5 prefix=$6
    run "$readelf" -W -s "$image" > "$prefix.symbols.txt"
    run "$readelf" -W -S "$image" > "$prefix.sections.txt"
    run "$readelf" -h "$image" > "$prefix.header.txt"
    local symbol_value symbol_size symbol_index section_value section_size section_index
    read -r symbol_value symbol_size symbol_index <<< "$(awk -v symbol="$symbol" \
        '$4 == "FUNC" && $8 == symbol { print $2, $3, $7; exit }' "$prefix.symbols.txt")"
    read -r section_value section_size section_index <<< "$(awk -v section="$section" \
        '{ sub(/\[[[:space:]]*/, "["); if ($2 == section) { gsub(/\[|\]/, "", $1); print $4, $6, $1; exit } }' \
        "$prefix.sections.txt")"
    if [[ -z $symbol_value || -z $section_value || $symbol_size != "$expected_size" ||
          $symbol_index != "$section_index" ]] ||
        (( 16#$symbol_value != 16#$section_value || 16#$section_size != expected_size )); then
        echo "FAIL: exact symbol/section entry and size ($image, $symbol)" >&2
        exit 1
    fi
    run "$objcopy" --only-section="$section" -O binary "$image" "$prefix.bin"
    run cmp "$expected" "$prefix.bin"
    run "$objdump" -d "$image" > "$prefix.disassembly.txt"
    printf 'EXACT window %s: symbol=%s value=0x%s size=%s section=%s\n' \
        "$image" "$symbol" "$symbol_value" "$symbol_size" "$section"
}

check_standalone() {
    local linker=$1 object=$2 symbol=$3 expected_size=$4 expected=$5 prefix=$6
    run "$linker" --build-id=none -e "$symbol" -Ttext=0x400000 "$object" -o "$prefix.elf"
    check_window "$prefix.elf" .text "$symbol" "$expected_size" "$expected" "$prefix.linked"
    local entry
    entry=$(awk '$1 == "Entry" && $2 == "point" { print $4 }' "$prefix.linked.header.txt")
    if [[ $entry != 0x400000 ]]; then echo "FAIL: final ELF entry ($entry)" >&2; exit 1; fi
}

native_run() {
    local executable=$1 log=$2
    shift 2
    local run_status=0
    run timeout 15 "$executable" "$@" > "$log" 2>&1 || run_status=$?
    cat "$log"
    if (( run_status == 124 || run_status == 3 )); then
        native_status=INCONCLUSIVE
        exit 3
    fi
    return "$run_status"
}

prepare() {
    local compiler=$1 name=$2
    local directory="$output/$name"
    if ! command -v "$compiler" > /dev/null 2>&1; then
        printf 'NOTRUN: compiler %s unavailable\n' "$compiler" | tee "$output/$name.NOTRUN.txt"
        return
    fi
    mkdir -p "$directory"
    run "$compiler" --version > "$directory/compiler.txt"
    run "$compiler" -std=gnu2x -O2 -Wall -Wextra -Werror -pthread -fsyntax-only \
        fixtures/futex-predicate-check.c > "$directory/portable-syntax.txt" 2>&1
    local target_args=()
    if [[ $(uname -sm) != 'Linux x86_64' ]]; then
        if ! [[ $(< "$directory/compiler.txt") == *clang* ]]; then
            echo 'NOTRUN: non-Clang host compiler cannot cross-assemble this ELF target; portable C syntax only' \
                | tee "$directory/assembly.NOTRUN.txt"
            return
        fi
        target_args=(--target=x86_64-unknown-linux-gnu)
    fi
    run "$compiler" "${target_args[@]}" -c fixtures/futex-predicate-wait.S -o "$directory/wait.o"
    run "$compiler" "${target_args[@]}" -c fixtures/futex-predicate-no-recheck.S -o "$directory/no-recheck.o"
    run "$compiler" "${target_args[@]}" -c fixtures/futex-publish.S -o "$directory/publish.o"
    run "$compiler" "${target_args[@]}" -c fixtures/futex-predicate-trampoline.S -o "$directory/trampoline.o"
    check_window "$directory/wait.o" .text.edsl_futex_predicate_wait_stub \
        edsl_futex_predicate_wait_stub 30 "$output/wait.expected.bin" "$directory/wait.object"
    check_window "$directory/no-recheck.o" .text.edsl_futex_predicate_no_recheck_stub \
        edsl_futex_predicate_no_recheck_stub 30 "$output/no-recheck.expected.bin" "$directory/no-recheck.object"
    check_window "$directory/publish.o" .text.edsl_futex_publish_stub \
        edsl_futex_publish_stub 32 "$output/publish.expected.bin" "$directory/publish.object"
    run "$objdump" -dr "$directory/trampoline.o" > "$directory/trampoline.disassembly.txt"
    object_count=$((object_count + 1))
    local linker=${EDSL_ELF_LD:-}
    if [[ -z $linker ]]; then
        if [[ $(uname -s) == Linux ]]; then linker=ld
        elif command -v ld.lld > /dev/null 2>&1; then linker=$(command -v ld.lld)
        fi
    fi
    if [[ -n $linker ]]; then
        run "$linker" --version > "$directory/linker.txt"
        check_standalone "$linker" "$directory/wait.o" edsl_futex_predicate_wait_stub \
            30 "$output/wait.expected.bin" "$directory/wait"
        check_standalone "$linker" "$directory/no-recheck.o" edsl_futex_predicate_no_recheck_stub \
            30 "$output/no-recheck.expected.bin" "$directory/no-recheck"
        check_standalone "$linker" "$directory/publish.o" edsl_futex_publish_stub \
            32 "$output/publish.expected.bin" "$directory/publish"
        standalone_count=$((standalone_count + 1))
    else
        echo 'NOTRUN: no ELF linker selected; final linked windows and entry pending Linux' \
            | tee "$directory/link.NOTRUN.txt"
    fi
    if [[ $mode == --prepare-only ]]; then return; fi
    if [[ $(< "$directory/compiler.txt") != *clang* && $name == clang ]] ||
       [[ $(< "$directory/compiler.txt") == *clang* && $name == gcc ]]; then
        echo 'NOTRUN: requested independent compiler family is an alias' | tee "$directory/native.NOTRUN.txt"
        return
    fi
    run "$compiler" -std=gnu2x -O2 -Wall -Wextra -Werror -fcf-protection=none -pthread \
        fixtures/futex-predicate-check.c "$directory/trampoline.o" "$directory/wait.o" \
        "$directory/no-recheck.o" "$directory/publish.o" \
        '-Wl,--unique=.text.edsl_futex_predicate_wait_stub,--unique=.text.edsl_futex_predicate_no_recheck_stub,--unique=.text.edsl_futex_publish_stub' \
        -o "$directory/native-check"
    check_window "$directory/native-check" .text.edsl_futex_predicate_wait_stub \
        edsl_futex_predicate_wait_stub 30 "$output/wait.expected.bin" "$directory/wait.native-linked"
    check_window "$directory/native-check" .text.edsl_futex_predicate_no_recheck_stub \
        edsl_futex_predicate_no_recheck_stub 30 "$output/no-recheck.expected.bin" "$directory/no-recheck.native-linked"
    check_window "$directory/native-check" .text.edsl_futex_publish_stub \
        edsl_futex_publish_stub 32 "$output/publish.expected.bin" "$directory/publish.native-linked"
    run cmp "$directory/wait.linked.bin" "$directory/wait.native-linked.bin"
    run cmp "$directory/no-recheck.linked.bin" "$directory/no-recheck.native-linked.bin"
    run cmp "$directory/publish.linked.bin" "$directory/publish.native-linked.bin"
    native_status=RUNNING
    local positive_status=0
    native_run "$directory/native-check" "$directory/positive.txt" || positive_status=$?
    if (( positive_status != 0 )); then native_status=FAIL; exit "$positive_status"; fi
    local negative negative_status
    for negative in wake eagain; do
        negative_status=0
        native_run "$directory/native-check" "$directory/no-recheck-$negative.txt" \
            "--no-recheck-$negative" || negative_status=$?
        if (( negative_status != 1 )) ||
            ! run grep -q '^CONTRACT-FAIL predicate remained zero at loop return$' \
                "$directory/no-recheck-$negative.txt"; then
            echo "FAIL: owned missing-recheck negative lacks the required observed violation ($negative)" >&2
            native_status=FAIL
            exit 1
        fi
    done
    native_count=$((native_count + 1))
    native_status=OBSERVED
}

prepare "${EDSL_CLANG:-clang}" clang
gcc_compiler=${EDSL_GCC:-gcc}
if [[ $(uname -s) != Linux && -z ${EDSL_GCC:-} ]] && command -v gcc-16 > /dev/null 2>&1; then
    gcc_compiler=gcc-16
fi
prepare "$gcc_compiler" gcc
if (( object_count == 0 )); then echo 'FAIL: no exact ELF object checks ran' >&2; exit 2; fi
if [[ $mode == --native ]] && (( native_count == 0 )); then
    echo 'NOTRUN: no supported native compiler harness ran' >&2
    exit 2
fi
