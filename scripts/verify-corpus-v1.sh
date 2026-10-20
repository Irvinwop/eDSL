#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
export PATH="${HOME}/.elan/bin:$PATH"
export LEAN_NUM_THREADS=1
mode=${1:---frozen}
if [[ $# -gt 1 || ! $mode =~ ^--(frozen|rebuild|freeze)$ ]]; then
    echo 'usage: scripts/verify-corpus-v1.sh [--frozen|--rebuild|--freeze]' >&2
    exit 2
fi
root=corpus/v1
mkdir -p artifacts/compiler-corpus-v1
output=$(mktemp -d artifacts/compiler-corpus-v1/run.XXXXXXXX)
output_absolute=$(realpath "$output")
printf '%s\n' "$mode" > "$output/mode.txt"
printf '%s\n' "$output" > artifacts/compiler-corpus-v1/LATEST
exec > >(tee "$output/run.log") 2>&1
trap 'status=$?; printf "%s\n" "$status" > "$output/exit"' EXIT

# Compile and run producers from one agreed immutable input copy. The initial
# digest must match both that snapshot and the live tree at completion.
inputs=(fixtures/corpus-v1/functions.c fixtures/corpus-v1/functions.h fixtures/corpus-v1/check.c
    corpus/v1/specifications.tsv corpus/v1/contracts.md corpus/Extract.lean corpus/Probe.lean scripts/verify-corpus-v1.sh lean-toolchain)
sha256sum "${inputs[@]}" > "$output/source-before.sha256"
snapshot=$output_absolute/input-snapshot
for input in "${inputs[@]}"; do
    mkdir -p "$snapshot/$(dirname "$input")"
    cp "$input" "$snapshot/$input"
done
(cd "$snapshot" && sha256sum --check "$output_absolute/source-before.sha256") > "$output/snapshot-check.txt"
reference=$root
if [[ $mode == --freeze ]]; then
    reference=$output/staged/corpus/v1
    mkdir -p "$reference"
fi

# These select the documented x86-64 Linux ET_EXEC target, without disabling
# vectorization, builtin recognition, loop transforms, or other -O2 behavior.
compile=(-std=gnu2x -O2 -march=x86-64 -mtune=generic -fno-pie -Wall -Wextra -Werror -Wpedantic)
link=(-no-pie -pthread -Wl,--build-id=none)

provenance() {
    local compiler=$1 destination=$2 resolved internal linker
    resolved=$(readlink -f "$(command -v "$compiler")")
    {
        printf 'corpus: edsl.compiler-corpus.v1\ncompiler-label: %s\n' "$compiler"
        printf 'compiler-executable: %s\n' "$resolved"
        printf 'compiler-sha256: '
        sha256sum "$resolved" | cut -d ' ' -f 1
        printf 'compiler-version:\n'
        "$compiler" --version
        printf 'target-triple: '
        "$compiler" -dumpmachine
        printf 'compile-arguments (one per line):\n'
        printf '%s\n' "${compile[@]}" -c fixtures/corpus-v1/functions.c -o functions.o
        printf 'harness-arguments (one per line):\n'
        printf '%s\n' "${compile[@]}" -pthread -c fixtures/corpus-v1/check.c -o check.o
        printf 'link-arguments (one per line):\n'
        printf '%s\n' functions.o check.o "${link[@]}" -o final.elf
        linker=$("$compiler" -print-prog-name=ld)
        linker=$(readlink -f "$(command -v "$linker")")
        printf 'linker-executable: %s\n' "$linker"
        printf 'linker-sha256: '
        sha256sum "$linker" | cut -d ' ' -f 1
        printf 'linker-version:\n'
        "$linker" --version
        if [[ $compiler == gcc ]]; then
            internal=$("$compiler" -print-prog-name=cc1)
            printf 'compiler-internal-sha256: '
            sha256sum "$internal" | cut -d ' ' -f 1
        fi
        printf 'libc-version:\n'
        getconf GNU_LIBC_VERSION
        printf 'lean-toolchain: '
        cat lean-toolchain
    } > "$destination"
}

# Run only executable Lean tooling here. No output of this extractor is counted
# as a kernel proof, decoded function, or end-to-end certificate.
extract() {
    local image=$1 destination=$2 compiler=$3
    flock /tmp/edsl-lean-build.lock lean -DwarningAsError=true --run "$snapshot/corpus/Extract.lean" \
        "$snapshot/corpus/v1/specifications.tsv" "$image" "$destination" "$compiler"
}

if [[ $mode == --freeze ]]; then
    if [[ -e $root/SHA256SUMS || -e $root/gcc/final.elf || -e $root/clang/final.elf ]]; then
        echo 'Refusing to overwrite frozen v1; create a new corpus version for changed inputs.' >&2
        exit 2
    fi
else
    sha256sum --check "$root/SOURCES.sha256"
    sha256sum --check "$root/SHA256SUMS"
fi

# This independent diagnostic uses the production decoder/checker. A successful
# discovery is deliberately kept separate from universal contract certification.
flock /tmp/edsl-lean-build.lock lake build EDSL.X86.Sequential.CFGDiscovery > "$output/cfg-build.txt" 2>&1
git rev-parse HEAD > "$output/checker-base-revision.txt"
find EDSL/X86 -type f -name '*.lean' -print0 | sort -z | xargs -0 sha256sum > "$output/checker-sources.sha256"

for compiler in gcc clang; do
    mkdir -p "$output/$compiler"
    if [[ $mode == --freeze || $mode == --rebuild ]]; then
        provenance "$compiler" "$output/$compiler/provenance.txt"
        if [[ $mode == --rebuild ]]; then
            cmp "$root/$compiler/provenance.txt" "$output/$compiler/provenance.txt"
        fi
        (cd "$snapshot" && "$compiler" "${compile[@]}" -c fixtures/corpus-v1/functions.c -o "$output_absolute/$compiler/functions.o")
        (cd "$snapshot" && "$compiler" "${compile[@]}" -pthread -c fixtures/corpus-v1/check.c -o "$output_absolute/$compiler/check.o")
        "$compiler" "$output/$compiler/functions.o" "$output/$compiler/check.o" "${link[@]}" \
            -o "$output/$compiler/final.elf"
        # Run the exact final ELF from which corpus spans will be selected.
        # A stress run or native contract check is never a formal certificate.
        timeout 30s "$output/$compiler/final.elf" > "$output/$compiler/native.txt" 2>&1
        if [[ $mode == --rebuild ]]; then
            cmp "$root/$compiler/final.elf" "$output/$compiler/final.elf"
        fi
        image=$output/$compiler/final.elf
    else
        image=$root/$compiler/final.elf
        timeout 30s "$image" > "$output/$compiler/native.txt" 2>&1
    fi
    extract "$image" "$output/$compiler/extracted" "$compiler"
    if [[ $mode == --freeze ]]; then
        mkdir -p "$reference/$compiler"
        cp "$image" "$reference/$compiler/final.elf"
        cp "$output/$compiler/provenance.txt" "$reference/$compiler/provenance.txt"
        cp "$output/$compiler/extracted/manifest.json" "$reference/$compiler/manifest.json"
    else
        cmp "$root/$compiler/manifest.json" "$output/$compiler/extracted/manifest.json"
    fi
    flock /tmp/edsl-lean-build.lock lake env lean -DwarningAsError=true --run "$snapshot/corpus/Probe.lean" \
        "$snapshot/corpus/v1/specifications.tsv" "$output/$compiler/extracted" "$output/$compiler/cfg-probe.json"
    if [[ $mode == --freeze ]]; then
        cp "$output/$compiler/cfg-probe.json" "$reference/$compiler/baseline-cfg.json"
    fi
    # Auxiliary human-readable disassembly. It is neither extraction authority
    # nor a substitute for decoded ISA semantics or a universal contract proof.
    objdump -d "$image" > "$output/$compiler/disassembly.txt"
done

# ELF header mutations are independently specified by the ELF64 format. They
# catch accepting another architecture/container or ignoring a truncated header.
reject_image() {
    local name=$1 image=$2 status=0
    extract "$image" "$output/rejections/$name" malformed > "$output/rejections/$name.log" 2>&1 || status=$?
    if [[ $status -ne 1 ]]; then
        echo "Expected malformed ELF rejection for $name; observed $status" >&2
        exit 1
    fi
}
mkdir -p "$output/rejections"
head -c 63 "$reference/gcc/final.elf" > "$output/rejections/truncated.elf"
reject_image truncated "$output/rejections/truncated.elf"
cp "$reference/gcc/final.elf" "$output/rejections/big-endian.elf"
printf '\002' | dd of="$output/rejections/big-endian.elf" bs=1 seek=5 conv=notrunc status=none
reject_image big-endian "$output/rejections/big-endian.elf"
cp "$reference/gcc/final.elf" "$output/rejections/wrong-machine.elf"
printf '\003\000' | dd of="$output/rejections/wrong-machine.elf" bs=1 seek=18 conv=notrunc status=none
reject_image wrong-machine "$output/rejections/wrong-machine.elf"
cp "$reference/gcc/final.elf" "$output/rejections/pie.elf"
printf '\003\000' | dd of="$output/rejections/pie.elf" bs=1 seek=16 conv=notrunc status=none
reject_image pie "$output/rejections/pie.elf"
objcopy --strip-symbol=c_min_u64 "$reference/gcc/final.elf" "$output/rejections/missing-function.elf"
reject_image missing-function "$output/rejections/missing-function.elf"
objcopy --redefine-sym c_max_u64=c_min_u64 "$reference/gcc/final.elf" "$output/rejections/duplicate-function.elf"
reject_image duplicate-function "$output/rejections/duplicate-function.elf"
cp "$reference/gcc/final.elf" "$output/rejections/nonexecutable.elf"
# Use an independent byte reader for the ELF64 e_phoff/e_phnum and program
# header fields; remove executable permission from every PT_LOAD in a copy.
program_offset=$(od -An -tu8 -j32 -N8 "$reference/gcc/final.elf" | tr -d '[:space:]')
program_count=$(od -An -tu2 -j56 -N2 "$reference/gcc/final.elf" | tr -d '[:space:]')
executable_header=-1
spare_header=-1
for ((index=0; index<program_count; ++index)); do
    header=$((program_offset + index * 56))
    kind=$(od -An -tu4 -j"$header" -N4 "$reference/gcc/final.elf" | tr -d '[:space:]')
    if [[ $kind -eq 1 ]]; then
        flags=$(od -An -tu4 -j"$((header + 4))" -N4 "$reference/gcc/final.elf" | tr -d '[:space:]')
        if (( (flags & 5) == 5 )); then executable_header=$header; fi
        printf '\004\000\000\000' | dd of="$output/rejections/nonexecutable.elf" \
            bs=1 seek="$((header + 4))" conv=notrunc status=none
    elif [[ $kind -eq 4 ]]; then
        spare_header=$header
    fi
done
reject_image nonexecutable "$output/rejections/nonexecutable.elf"
if (( executable_header < 0 || spare_header < 0 )); then
    echo 'Frozen ELF lacks expected executable LOAD / spare NOTE for overlap regression' >&2
    exit 1
fi
cp "$reference/gcc/final.elf" "$output/rejections/overlapping-loads.elf"
dd if="$reference/gcc/final.elf" bs=1 skip="$executable_header" count=56 status=none | \
    dd of="$output/rejections/overlapping-loads.elf" bs=1 seek="$spare_header" conv=notrunc status=none
printf '\006\000\000\000' | dd of="$output/rejections/overlapping-loads.elf" \
    bs=1 seek="$((spare_header + 4))" conv=notrunc status=none
reject_image overlapping-loads "$output/rejections/overlapping-loads.elf"
awk -F '\t' 'BEGIN {OFS="\t"} $1=="02" {$1="01"} {print}' "$snapshot/corpus/v1/specifications.tsv" \
    > "$output/rejections/duplicate-id.tsv"
status=0
flock /tmp/edsl-lean-build.lock lean -DwarningAsError=true --run "$snapshot/corpus/Extract.lean" \
    "$output/rejections/duplicate-id.tsv" "$reference/gcc/final.elf" "$output/rejections/duplicate-id" malformed \
    > "$output/rejections/duplicate-id.log" 2>&1 || status=$?
if [[ $status -ne 1 ]]; then echo 'Expected duplicate definition-ID rejection' >&2; exit 1; fi

sha256sum --check "$output/source-before.sha256" > "$output/source-stability.txt"

if [[ $mode == --freeze ]]; then
    cp "$output/checker-base-revision.txt" "$reference/checker-baseline-revision.txt"
    cp "$output/checker-sources.sha256" "$reference/checker-baseline-sources.sha256"
    cp "$output/source-before.sha256" "$reference/SOURCES.sha256"
    (cd "$output/staged" && sha256sum corpus/v1/gcc/final.elf corpus/v1/gcc/manifest.json \
        corpus/v1/gcc/provenance.txt corpus/v1/gcc/baseline-cfg.json corpus/v1/clang/final.elf \
        corpus/v1/clang/manifest.json corpus/v1/clang/provenance.txt corpus/v1/clang/baseline-cfg.json \
        corpus/v1/checker-baseline-revision.txt corpus/v1/checker-baseline-sources.sha256 > corpus/v1/SHA256SUMS)
    # No public v1 output appears until both profiles, negative cases and input
    # stability checks have succeeded. The seal is moved last.
    for item in gcc clang SOURCES.sha256 checker-baseline-revision.txt checker-baseline-sources.sha256 SHA256SUMS; do
        mv "$reference/$item" "$root/$item"
    done
fi
cat > "$output/coverage.tsv" <<'COVERAGE'
metric	count
definitions_frozen	40
compiler_profiles	2
exact_final_elf_function_windows	80
corpus_functions_certified_end_to_end	0
corpus_function_artifacts_certified_end_to_end	0
corpus_concurrency_contracts_proved	0
COVERAGE
cat "$output/coverage.tsv"
find "$output" -type f ! -name SHA256SUMS ! -name run.log ! -name exit -print0 | sort -z | xargs -0 sha256sum > "$output/SHA256SUMS"
echo "Frozen compiler corpus checked ($mode): $output; no end-to-end certificates asserted."
