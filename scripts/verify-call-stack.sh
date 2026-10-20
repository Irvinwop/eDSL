#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail
umask 022
native_only=false
if [[ ${1:-} == --native-only && $# == 1 ]]; then
    native_only=true
elif [[ $# != 0 ]]; then
    echo 'usage: scripts/verify-call-stack.sh [--native-only]' >&2
    exit 2
fi
if [[ $(uname -sm) != 'Linux x86_64' ]]; then
    echo 'Nested-call native evidence requires Linux x86_64' >&2
    exit 2
fi
cd "$(dirname "${BASH_SOURCE[0]}")/.."
exec 9>/tmp/edsl-call-stack-native-home.lock
if ! flock -n 9; then
    echo 'A nested-call native harness job is already active; refusing duplicate work' >&2
    exit 2
fi
evidence_root=${CALL_STACK_EVIDENCE_ROOT:-$PWD/.cache/call-stack-native}
mkdir -p "$evidence_root"
output=$(mktemp -d "$evidence_root/run-$(date -u +%Y%m%dT%H%M%S)-XXXXXX")
printf 'Native evidence: %s\n' "$output" >&2
exec 3>"$output/commands.log"
exec 4>"$output/command-status.tsv"
sequence=0
run() {
    sequence=$((sequence + 1))
    printf '[%03d] cwd=%q argv=' "$sequence" "$PWD" >&3
    printf '%q ' "$@" >&3
    printf '\n' >&3
    local status=0
    "$@" || status=$?
    printf '%03d\t%d\n' "$sequence" "$status" >&4
    return "$status"
}
finish() {
    local status=$?
    trap - EXIT
    printf 'script exit=%d UTC=%s native_only=%s\n' "$status" "$(date -u +%FT%TZ)" "$native_only" > "$output/terminal-status.txt"
    # Hash only completed, closed evidence; exclude the manifest and its digest.
    exec 3>&- 4>&-
    (
        cd "$output"
        mapfile -d '' -t manifest_files < <(
            find . -type f ! -name SHA256SUMS ! -name MANIFEST-SHA256.txt -print0 | sort -z)
        sha256sum -- "${manifest_files[@]}" > SHA256SUMS
        sha256sum SHA256SUMS > MANIFEST-SHA256.txt
    ) || status=1
    exit "$status"
}
trap finish EXIT

owned=(fixtures/call-stack-helper.c fixtures/call-stack-caller.c
    fixtures/call-stack-same.c fixtures/call-stack-check.c
    fixtures/call-stack-check.S fixtures/call-stack-inline.c scripts/verify-call-stack.sh
    scripts/check-call-stack-proofs.sh scripts/check-call-stack-grading.sh)
mkdir -p "$output/sources" "$output/metadata"
for source in "${owned[@]}"; do run cp "$source" "$output/sources/$(basename "$source")"; done
run sha256sum "${owned[@]}" > "$output/source-SHA256SUMS"
run bash -n scripts/verify-call-stack.sh
run shellcheck -s bash scripts/verify-call-stack.sh > "$output/shellcheck.txt" 2>&1
{
    run date -u +%FT%TZ
    run uname -a
    run cat /etc/os-release
    run git rev-parse HEAD
    run /usr/bin/gcc-13 --version
    run /usr/bin/gcc-13 -dumpmachine
    run /usr/bin/gcc-13 -print-prog-name=cc1
    run /usr/bin/gcc-13 -print-prog-name=as
    run /usr/bin/clang-18 --version
    run /usr/bin/clang-18 -print-target-triple
    run /usr/bin/clang-18 -print-resource-dir
    run /usr/bin/ld --version
    run /usr/bin/as --version
    run /usr/bin/readelf --version
    run /usr/bin/objcopy --version
    run /usr/bin/objdump --version
    run /usr/bin/shellcheck --version
    run /usr/bin/openssl version -a
    run /usr/bin/readlink -f /usr/bin/gcc-13 /usr/bin/clang-18 /usr/bin/ld /usr/bin/as /usr/bin/objcopy /usr/bin/objdump
} > "$output/metadata/platform-tools.txt" 2>&1
run sha256sum /usr/bin/gcc-13 /usr/bin/clang-18 /usr/bin/ld /usr/bin/as \
    /usr/bin/readelf /usr/bin/objcopy /usr/bin/objdump /usr/bin/shellcheck \
    > "$output/metadata/tool-SHA256SUMS"

probe=${CALL_STACK_PROBE:-}
expected_probe_manifest=7959ffba34ac9bf7c48f80a2ae364964062b17e3527d405a383237849ca1261c
if [[ -n $probe ]]; then
    printf '%s  %s\n' "$expected_probe_manifest" "$probe/SHA256SUMS" > "$output/probe-manifest-expected.txt"
    run sha256sum -c "$output/probe-manifest-expected.txt" > "$output/probe-manifest-check.txt"
    run bash -c 'cd "$1" && sha256sum -c SHA256SUMS' _ "$probe" > "$output/probe-integrity.txt"
    run cp "$probe/terminal-status.txt" "$output/cold-probe-terminal-status.txt"
    run cmp fixtures/call-stack-helper.c "$probe/src/helper.c"
    run cmp fixtures/call-stack-caller.c "$probe/src/caller.c"
    run cmp fixtures/call-stack-same.c "$probe/src/same.c"
else
    printf 'Historical cold probe not supplied; current whole profiles are authenticated independently.\n' > "$output/probe-manifest-check.txt"
fi

# Exactly the recorded cold-probe options; no flag tuning to obtain a profile.
flags=(-std=gnu2x -Os -Wall -Wextra -Werror -fno-lto -fcf-protection=none
    -ffunction-sections -fno-stack-protector -fno-unwind-tables
    -fno-asynchronous-unwind-tables -fno-optimize-sibling-calls)
link_flags=(-m elf_x86_64 --build-id=none --gc-sections -z noexecstack -e caller -Ttext=0x401000)
texts=()
expected_offsets=(5 0 5 0)
for compiler_name in gcc13 clang18; do
    if [[ $compiler_name == gcc13 ]]; then compiler=/usr/bin/gcc-13; else compiler=/usr/bin/clang-18; fi
    same="$output/$compiler_name/same-tu"
    separate="$output/$compiler_name/separate-tu"
    mkdir -p "$same" "$separate"
    run "$compiler" "${flags[@]}" -c fixtures/call-stack-same.c -o "$same/same.o" > "$same/compile.log" 2>&1
    run /usr/bin/ld "${link_flags[@]}" "$same/same.o" -o "$same/function.elf" > "$same/link.log" 2>&1
    run "$compiler" "${flags[@]}" -c fixtures/call-stack-caller.c -o "$separate/caller.o" > "$separate/compile-caller.log" 2>&1
    run "$compiler" "${flags[@]}" -c fixtures/call-stack-helper.c -o "$separate/helper.o" > "$separate/compile-helper.log" 2>&1
    run /usr/bin/ld "${link_flags[@]}" "$separate/caller.o" "$separate/helper.o" -o "$separate/function.elf" > "$separate/link.log" 2>&1
    for config in same-tu separate-tu; do
        directory="$output/$compiler_name/$config"
        for artifact in "$directory"/*.o "$directory/function.elf"; do
            run /usr/bin/readelf -aW "$artifact" > "$artifact.readelf.txt"
            run /usr/bin/objdump -drwC -Mintel --show-raw-insn "$artifact" > "$artifact.disasm.txt"
            run /usr/bin/objdump -s "$artifact" > "$artifact.sections-hex.txt"
            run /usr/bin/nm -n -S --defined-only "$artifact" > "$artifact.symbols.txt"
            run /usr/bin/file "$artifact" > "$artifact.file.txt"
        done
        run /usr/bin/readelf -rW "$directory/function.elf" > "$directory/final-relocations.txt"
        if ! grep -Fxq 'There are no relocations in this file.' "$directory/final-relocations.txt"; then
            echo 'Final function ELF retains relocations' >&2
            exit 1
        fi
        run /usr/bin/objdump -h "$directory/function.elf" > "$directory/final-sections.txt"
        # Bind the actual ELF entry, caller symbol and whole .text section to
        # the entry offset used by the observer, including helper-before-entry.
        elf_entry=$(awk '/Entry point address:/ {print $NF}' "$directory/function.elf.readelf.txt")
        caller_address=$(awk '$4 == "caller" {print "0x" $1}' "$directory/function.elf.symbols.txt")
        helper_address=$(awk '$4 == "helper" {print "0x" $1}' "$directory/function.elf.symbols.txt")
        text_address=$(awk '$2 == ".text" {print "0x" $4}' "$directory/final-sections.txt")
        text_size=$(awk '$2 == ".text" {print "0x" $3}' "$directory/final-sections.txt")
        profile_index=${#texts[@]}
        if [[ -z $elf_entry || -z $caller_address || -z $helper_address ||
              -z $text_address || -z $text_size ]] ||
            (( elf_entry != caller_address || text_address != 0x401000 ||
               caller_address - text_address != expected_offsets[profile_index] ||
               helper_address < text_address || helper_address >= text_address + text_size )); then
            echo 'Final ELF entry/symbol/whole-text binding differs from the observed profile' >&2
            exit 1
        fi
        printf 'profile=%d text=%s size=%s entry=%s caller=%s helper=%s entry_offset=%d\n' \
            "$profile_index" "$text_address" "$text_size" "$elf_entry" "$caller_address" \
            "$helper_address" "${expected_offsets[profile_index]}" > "$directory/entry-binding.txt"
        run /usr/bin/objcopy --dump-section ".text=$directory/text.bin" "$directory/function.elf"
        if [[ -n $probe ]]; then
            run cmp "$directory/text.bin" "$probe/$compiler_name/$config/text.bin"
        fi
        run sha256sum "$directory"/*.o "$directory/function.elf" "$directory/text.bin" > "$directory/artifact-SHA256SUMS"
        texts+=("$directory/text.bin")
    done
done

cat > "$output/scope.txt" <<'SCOPE'
Finite synthetic owned Linux x86-64/SysV native observations only. GNU23 is
spelled gnu2x for the pinned GCC 13/Clang 18 fixture options from the cold probe.
Four complete 14/16/16/16-byte final texts include helper and caller; entries
are offsets 5/0/5/0. An optional historical cold probe, when supplied, is checked
against its pinned manifest. It is not required for a clean checkout or CI.
Object PLT32 CALL relocations are resolved in actual linked final texts. The
observer is PIE and all actual text/root addresses must be above 4 GiB.
Four data-file extractions, exact embedded slots bounded by end labels, and
independent expected complete profiles must all match before evidence or probes.
Input data files are never executable targets. Sixteen altered/truncated/extended/
cross-profile inputs per observer must reject with status 2, exact diagnostic,
empty stdout and an empty evidence directory. Signals/timeouts fail the suite.

The root entry is JMP with RSP=S and a preinstalled root RA, NOT an observed
CPU root CALL. Internal E8 CALLs and all RETs are actual instructions using RAM.
S is owned page+24 (mod16=8); private frame is [S-16,S) = page offsets [8,24).
The preceding mapped 8 bytes permit a safe negative write at S-24. Two PROT_NONE
guard pages surround the RW/NX page. Before snapshots follow RA installation.
Every case saves full independent pre/post pages, all 16 actual GPRs, requested
and effective flags, result, actual root/entry/helper/internal return addresses,
and private slots. MOV captures registers and restores host RSP before PUSHFQ;
MOV preserves flags. Recovery uses RIP-relative globals, no hidden GPR pointer,
and handles RET $8 without touching the shifted alternate stack. Host flags/DF
are restored before C resumes. All blockable signals are blocked during capture.

The independent byte-carry oracle checks (natural input+2) mod 2^64. Twenty-four
literal edge vectors validate its carries/wrap; 64 random operands per effective
flag profile and compiler profile exercise distinct data. Each profile tests
all 64 combinations of CF/PF/AF/ZF/SF/OF, with both effective ID settings. DF is
clear on positive entry. Requested flags and all GPR installations must actually
be observed or the experiment fails. Initial RAX is nonzero and arbitrary saved
GPR values vary. Result, S+8 return, all six callee-saved GPRs, every nonarithmetic
flag and every page byte outside private16 (including root RA) are checked.
Endpoint /proc/self/maps equality checks all process mapping permissions; guard
and stack permissions are checked explicitly. These are endpoint observations,
not per-access hardware traces or assertions about RAM outside the owned page.
Positive-only extra checks bind dirty internal return slots to actual labels:
GCC same writes S-8 and leaves S-16 intact; the others PUSH old RAX at S-8 and
CALL-write S-16. GCC separate POPs old RAX into RDX, Clang into RCX.

Nine owned safe mutants must fail their specified common-contract category:
missing helper increment, +3, narrowing, RBX/R12 clobbers, mapped out-of-private
write, RET $8, DF damage and ID damage. Their private-slot patterns are not
required to match positive compilers. No fault is intentionally triggered.
No real security findings, source-preservation proof, timing, concurrency,
physical-fault priority, CET/privileged-flag behavior or universal CPU theorem.
Assumptions: ordinary Linux x86-64 user-mode RAM, AC and CET disabled, SysV,
single-threaded capture and no asynchronous interference. SHSTK status is
recorded; unavailable status does not prove CET support. Compiler/link flags
disable CET instrumentation, and these observers carry no CET enable property.

observations.jsonl indexes pairs of complete raw pages in pages.bin by byte
offset; each page also has a SHA256. Register/flag/address words are hex strings.
private_before/private_after concatenate numeric S-16 and S-8 words, not raw
little-endian byte strings. Actual whole code bytes and labels are in
identity.jsonl and ELF/extraction/disassembly evidence. The native observer emits
no Lean source. The default runner separately elaborates contracts for the four
actual extractions and selected entries, audits dependencies and replays them
with a fresh kernel. That is a universal theorem instantiation, not replay of
the finite native register/page observations or a source-preservation theorem.
Explicit --native-only reports formal=NOTRUN and skips every formal gate.
SCOPE

printf '%s\n' 'Final whole-text extraction differs from embedded expected profiles' > "$output/rejection-diagnostic.txt"
for compiler_name in gcc13 clang18; do
    if [[ $compiler_name == gcc13 ]]; then compiler=/usr/bin/gcc-13; else compiler=/usr/bin/clang-18; fi
    observer="$output/observer-$compiler_name"
    mkdir -p "$observer/positive" "$observer/rejections"
    observer_flags=(-std=gnu2x -O2 -Wall -Wextra -Werror -Wshadow -Wformat=2
        -Wstrict-prototypes -fno-lto -fcf-protection=none -fPIE -pie
        '-Wl,--build-id=none,-z,noexecstack')
    run "$compiler" "${observer_flags[@]}" fixtures/call-stack-check.c \
        fixtures/call-stack-check.S -lcrypto -o "$observer/check.elf" > "$observer/build.log" 2>&1
    run /usr/bin/readelf -aW "$observer/check.elf" > "$observer/elf.txt"
    run /usr/bin/objdump -d -w -Mintel --show-raw-insn "$observer/check.elf" > "$observer/disassembly.txt"
    run /usr/bin/nm -n -S --defined-only "$observer/check.elf" > "$observer/symbols.txt"
    run /usr/bin/ldd "$observer/check.elf" > "$observer/shared-libraries.txt"
    run /usr/bin/objcopy --dump-section ".edsl_calls=$observer/embedded.bin" \
        --dump-section ".edsl_call_mutants=$observer/owned-mutants.bin" "$observer/check.elf"
    cat "${texts[@]}" > "$observer/compiled-whole-texts.bin"
    run cmp "$observer/compiled-whole-texts.bin" "$observer/embedded.bin"
    # Every file position is tested; same-TU helper-before-entry bytes are included.
    for index in 0 1 2 3; do
        original=${texts[index]}
        length=$(stat -c %s "$original")
        for mutation in altered truncated extended cross-profile; do
            case_dir="$observer/rejections/$index-$mutation"
            mkdir -p "$case_dir/no-probes"
            case $mutation in
                altered)
                    cp "$original" "$case_dir/input.bin"
                    printf '\x00' | dd of="$case_dir/input.bin" bs=1 count=1 conv=notrunc status=none
                    ;;
                truncated) head -c "$((length - 1))" "$original" > "$case_dir/input.bin" ;;
                extended) cat "$original" > "$case_dir/input.bin"; printf '\x00' >> "$case_dir/input.bin" ;;
                cross-profile) cp "${texts[(index + 1) % 4]}" "$case_dir/input.bin" ;;
            esac
            inputs=("${texts[@]}")
            inputs[index]="$case_dir/input.bin"
            status=0
            run timeout -k 5s 20s "$observer/check.elf" "$case_dir/no-probes" "${inputs[@]}" \
                > "$case_dir/stdout.txt" 2> "$case_dir/stderr.txt" || status=$?
            if [[ $status != 2 || -s "$case_dir/stdout.txt" ||
                -n $(find "$case_dir/no-probes" -mindepth 1 -print -quit) ]] ||
                ! cmp -s "$output/rejection-diagnostic.txt" "$case_dir/stderr.txt"; then
                echo "Pre-probe extraction rejection failed: $compiler_name $index $mutation status=$status" >&2
                exit 1
            fi
            printf '%s\t%d\t%s\t%d\tPASS\n' "$compiler_name" "$index" "$mutation" "$status" >> "$output/rejection-status.tsv"
        done
    done
    run timeout -k 5s 120s "$observer/check.elf" "$observer/positive" "${texts[@]}" \
        > "$observer/positive/stdout.txt" 2> "$observer/positive/results.txt"
    if [[ -s "$observer/positive/stdout.txt" ]]; then
        echo 'Native observer unexpectedly emitted stdout/formal input' >&2
        exit 1
    fi
    cat "$observer/positive/results.txt" >&2
done
printf 'native=PASS formal=NOTRUN observers=2 compiler_profiles=4 extraction_rejections=32\n' > "$output/result.txt"
if $native_only; then
    echo 'native=PASS formal=NOTRUN (explicit --native-only)' >&2
else
    run env LEAN_NUM_THREADS=1 flock /tmp/edsl-lean-build.lock \
        bash scripts/check-call-stack-proofs.sh "$output/formal" "${texts[@]}"
    run env LEAN_NUM_THREADS=1 flock /tmp/edsl-lean-build.lock \
        bash scripts/check-call-stack-grading.sh "$output/grading" "${texts[@]}"
    printf 'native=PASS formal=PASS grading=PASS observers=2 compiler_profiles=4 extraction_rejections=32\n' > "$output/result.txt"
    echo 'native=PASS formal=PASS grading=PASS (whole-text contracts, checked packets and fresh kernel)' >&2
fi
