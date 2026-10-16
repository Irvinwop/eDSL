#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail

if [[ $(uname -sm) != 'Linux x86_64' ]]; then
    echo 'CFG native evidence requires Linux x86_64' >&2
    exit 2
fi
cd "$(dirname "${BASH_SOURCE[0]}")/.."
output=artifacts/cfg-fixtures
mkdir -p "$output"
gcc=${EDSL_GCC:-gcc-13}
if [[ $("$gcc" -dumpversion) != 13 ]]; then
    echo 'Unsupported compiler profile: this evidence selects GCC 13' >&2
    exit 2
fi
uname -srmo > "$output/platform.txt"
ld --version > "$output/linker.txt"
objcopy --version > "$output/objcopy.txt"
objdump --version > "$output/objdump.txt"
readelf --version > "$output/readelf.txt"
cat > "$output/scope.txt" <<'EOF'
CFG imports check the literal full finite window, actual decoding, closed
successors and cutpoint/depth data. They do not establish the task's result,
termination, current read permissions or runtime admission; local semantic
proofs must separately discharge those obligations. An accepted graph can
diverge or compute the wrong answer. Native observations remain separate
evidence and do not establish total correctness or source-language correctness.
The selected GCC13 scalar pointer/count -Os -fno-ivopts profile disables CET,
LTO, vectorization and unrolling. GNU23 is named gnu2x by GCC13. Its final
linked ET_EXEC callable functions have no process startup and no relocations.
The harness maps complete final linked .text bytes RX and calls through an
external SysV assembly trampoline. Readonly inputs terminate at guard pages;
independent algebraic expectations cover strided sums, odd-word independence,
two-buffer sums, identical and overlapping readonly inputs, empty/null/guard
inputs, modular wrap and multiple loop counts.
Full RAX, six callee-saved registers, DF and practical return/stack preservation
are observed. These tests make no timing, speculation or concurrency claim.
All negative fixtures are project-owned synthetic inputs. Static rejection,
failed proof or timeout does not establish a security defect.
EOF
cat >> "$output/scope.txt" <<'EOF'
The supplemental stride RawFunctional/ELFFunctional modules separately bind
the imported observedBytes to the exact Stride32 bytes. They prove the fixed
even-index task contract, exact 6*n+4 retired instructions and ordered operands
for every modeled flag choice, conditional on current memory/ABI premises.
Their OS wrapper retains current ArrayResources admission and read loans; the
ELF wrapper also establishes successful abstract loading from a fresh space.
These are callable-function theorems, without process-startup or native
CPU/kernel conformance proofs. They do not certify arbitrary imported CFGs or
the early fixture. A deliberate wrong-stride binding failure only rejects
reuse of this particular fixed-byte proof instance.
EOF
cat >> "$output/scope.txt" <<'EOF'
The separate pair RawFunctional/ELFFunctional modules, after their kernel
checks succeed, bind fresh observedBytes to Pair32.bytes and prove the sum of
the concatenated mathematical inputs modulo 2^32, full zero-extended RAX,
unchanged RAM and the ABI frame. Their exact 6*(lenA+lenB)+6 count and ordered
A4/B4/stack8 reads hold for every modeled AF stream. Two compatible current
OS admissions permit readonly aliases; empty inputs impose no input loan or
pointer-readability requirement. The full ELF wrapper exposes fresh loading
and explicit current caller-array, full-counter and return-slot premises.
The static pair imports alone establish only their finite CFG obligations.
EOF

harness_args=(-std=gnu2x -O2 -Wall -Wextra -Werror -fcf-protection=none -fno-lto
    fixtures/cfg/check.c fixtures/cfg/trampoline.S -o "$output/native-check")
printf '%q ' "$gcc" "${harness_args[@]}" > "$output/harness-arguments.txt"
printf '\n' >> "$output/harness-arguments.txt"
"$gcc" "${harness_args[@]}"

prepare() {
    local name=$1 source=$2 symbol=$3 mode=$4
    shift 4
    local directory="$output/$name"
    mkdir -p "$directory"
    "$gcc" --version > "$directory/compiler.txt"
    "$gcc" -dumpmachine > "$directory/target.txt"
    local compile_args=(-std=gnu2x -Os -fno-ivopts -fno-tree-vectorize -fno-tree-slp-vectorize
        -fno-unroll-loops -ffunction-sections -fcf-protection=none -fno-lto
        -Wall -Wextra -Werror "$@" -c "$source" -o "$directory/function.o")
    local link_args=(-m elf_x86_64 --build-id=none --gc-sections -z noexecstack
        -e "$symbol" -Ttext=0x401000 -o "$directory/function.elf" "$directory/function.o")
    {
        printf '%q ' "$gcc" "${compile_args[@]}"; printf '\n'
        printf '%q ' ld "${link_args[@]}"; printf '\n'
        printf '%q ' objcopy --dump-section ".text=$directory/function.bin" "$directory/function.elf"; printf '\n'
    } > "$directory/arguments.txt"
    "$gcc" "${compile_args[@]}"
    ld "${link_args[@]}"
    objcopy --dump-section ".text=$directory/function.bin" "$directory/function.elf"
    LC_ALL=C readelf -rW "$directory/function.elf" > "$directory/relocations.txt"
    if ! grep -q '^There are no relocations in this file\.' "$directory/relocations.txt"; then
        echo "Unsupported relocated native window: $name" >&2
        exit 2
    fi
    objdump -drw -Mintel "$directory/function.elf" > "$directory/disassembly.txt"
    readelf -h -l -s -W "$directory/function.elf" > "$directory/elf.txt"
    od -An -v -tx1 "$directory/function.bin" > "$directory/bytes.txt"
    wc -c < "$directory/function.bin" > "$directory/span.txt"
    if [[ $mode == wrong-stride ]]; then
        timeout 15 "$output/native-check" --expect-reject stride "$directory/function.bin" \
            > "$directory/native-results.txt" 2>&1
    else
        timeout 15 "$output/native-check" "$mode" "$directory/function.bin" \
            > "$directory/native-results.txt" 2>&1
    fi
    cat "$directory/native-results.txt"
    sha256sum "$source" fixtures/cfg/check.c fixtures/cfg/trampoline.S scripts/verify-cfg.sh \
        "$directory/function.o" "$directory/function.elf" "$directory/function.bin" \
        "$output/native-check" "$directory/native-results.txt" "$directory/compiler.txt" \
        "$directory/arguments.txt" > "$directory/SHA256SUMS"
}

# Native commands do not need the shared Lean build lock.
prepare stride fixtures/cfg/stride.c sum_stride stride
prepare pair fixtures/cfg/pair.c sum_pair pair
prepare early fixtures/cfg/early.S cfg_early early
prepare wrong-stride fixtures/cfg/stride.c sum_stride wrong-stride -DEDSL_CFG_STRIDE=1

flock /tmp/edsl-lean-build.lock lake build edsl-cfg-import \
    EDSL.Stride32.Correctness EDSL.Pair32.Correctness
flock /tmp/edsl-lean-build.lock lake env lean -DwarningAsError=true tests/CFG.lean
flock /tmp/edsl-lean-build.lock lake env lean -DwarningAsError=true tests/Pair32.lean
importer=.lake/build/bin/edsl-cfg-import

import_window() {
    local directory=$1
    local span
    span=$(wc -c < "$directory/function.bin")
    # The importer locks each kernel subprocess; no outer lock here.
    lake env "$importer" "$directory/function.bin" "$directory/Raw.lean" \
        > "$directory/raw-import.txt" 2>&1
    lake env "$importer" --elf "$span" "$directory/function.elf" "$directory/ELF.lean" \
        > "$directory/elf-import.txt" 2>&1
    cat "$directory/raw-import.txt" "$directory/elf-import.txt"
    sha256sum "$directory/function.bin" "$directory/function.elf" "$directory/Raw.lean" \
        "$directory/ELF.lean" "$directory/native-results.txt" > "$directory/imported-SHA256SUMS"
}

import_window "$output/stride"
import_window "$output/pair"
import_window "$output/early"
# This program computes contiguous sums. Its finite CFG remains valid, while
# the independent stride oracle above rejects it. Static import is not proof
# of the intended task contract.
import_window "$output/wrong-stride"

functional_source() {
    local source=$1 destination=$2 container=$3
    {
        printf 'import EDSL.Stride32.Correctness\n'
        sed '/^#audit_edsl$/d' "$source"
        cat <<'EOF'
namespace EDSL.GeneratedCFG.Functional
open X86 Sequential OS.AddressSpace

-- This equality connects the actual artifact to one separately proved
-- instruction-level task instance, without assuming graph equality.
theorem sameBytes : observedBytes = Stride32.bytes := by decide

theorem exactResult {initial : State} {values : List (BitVec 32)}
    {count : Nat} {target : Word}
    (pre : Stride32.Pre observedBytes initial values count target)
    (choices : Choices) :
    ∃ result, run choices (6 * count + 4) initial = .ok result ∧
      Stride32.Post initial values count target result.state ∧
      result.instructions = 6 * count + 4 ∧ result.reads = Stride32.operandReads initial count := by
  rw [sameBytes] at pre
  exact Stride32.exact_sound pre choices

theorem resourceResult {shared : OS.Borrowing.State} {call : OS.ArrayResources.Call}
    {initial : State} {count : Nat} (code : call.bytes = observedBytes)
    (admitted : OS.ArrayResources.Admission shared call initial)
    (entry : initial.rip = call.code) (stack : initial.registers .rsp = call.stack)
    (base : initial.registers .rdi = call.base) (length : call.values.length = 2 * count)
    (counter : initial.registers .rsi = BitVec.ofNat 64 count) (choices : Choices) :
    ∃ result, run choices (6 * count + 4) initial = .ok result ∧
      Stride32.Post initial call.values count call.target result.state ∧
      result.instructions = 6 * count + 4 ∧ result.reads = Stride32.operandReads initial count ∧
      OS.ArrayResources.Admission shared call result.state ∧
      ∀ read ∈ result.reads, OS.ArrayResources.ReadPermission shared call.worker read :=
  Stride32.resource_sound (code.trans sameBytes) admitted entry stack base length counter choices
EOF
        if [[ $container == elf ]]; then
            cat <<'EOF'

def loadedState (prior : Space) (registers : Register → Word) (flags : Word) : State :=
  ⟨registers, ELF.codeAddress observedImage, flags, toMemory (loadedSpace prior)⟩

-- Loading supplies the actual function bytes. The current input and complete
-- return slot are separate caller premises; entry is a callable function.
theorem loadedResult (prior : Space) (registers : Register → Word) (flags : Word)
    {values : List (BitVec 32)} {count : Nat} {target : Word}
    (free : ELF.fresh observedImage prior = true)
    (array : ArrayAt (toMemory (loadedSpace prior)) (registers .rdi) values)
    (bound : ArrayBound (registers .rdi) values) (length : values.length = 2 * count)
    (counter : registers .rsi = BitVec.ofNat 64 count)
    (stack : readWord (toMemory (loadedSpace prior)) (registers .rsp) = .ok target)
    (returnCanonical : canonical target = true)
    (stackAfterCanonical : canonical (registers .rsp + 8) = true) (choices : Choices) :
    ELF.load observedELF prior = .ok ⟨observedImage, loadedSpace prior⟩ ∧
    ∃ result, run choices (6 * count + 4) (loadedState prior registers flags) = .ok result ∧
      Stride32.Post (loadedState prior registers flags) values count target result.state ∧
      result.instructions = 6 * count + 4 ∧
      result.reads = Stride32.operandReads (loadedState prior registers flags) count := by
  refine ⟨loaded prior free, exactResult ?_ choices⟩
  exact ⟨loadedCode prior, array, bound, length, counter, stack,
    returnCanonical, stackAfterCanonical⟩
EOF
        fi
        printf '\nend EDSL.GeneratedCFG.Functional\n\n#audit_edsl\n'
    } > "$destination"
}

pair_functional_source() {
    local source=$1 destination=$2 container=$3
    {
        printf 'import EDSL.Pair32.Correctness\n'
        sed '/^#audit_edsl$/d' "$source"
        cat <<'EOF'
namespace EDSL.GeneratedCFG.Functional
open X86 Sequential OS.AddressSpace

-- Bind the literal freshly extracted artifact, independently of its graph.
theorem sameBytes : observedBytes = Pair32.bytes := by decide

theorem exactResult {initial : State} {valuesA valuesB : List (BitVec 32)} {target : Word}
    (pre : Pair32.Pre observedBytes initial valuesA valuesB target) (choices : Choices) :
    ∃ result, run choices (6 * (valuesA.length + valuesB.length) + 6) initial = .ok result ∧
      Pair32.Post initial valuesA valuesB target result.state ∧
      result.state.registers .rax = (sum32 (valuesA ++ valuesB)).setWidth 64 ∧
      result.instructions = 6 * (valuesA.length + valuesB.length) + 6 ∧
      result.reads = Pair32.operandReads initial valuesA valuesB := by
  rw [sameBytes] at pre
  obtain ⟨result, success, post, cost, reads⟩ := Pair32.exact_sound pre choices
  exact ⟨result, success, post, post.value, cost, reads⟩

theorem resourceResult {shared : OS.Borrowing.State} {callA callB : OS.ArrayResources.Call}
    {initial : State} (code : callA.bytes = observedBytes)
    (admitted : Pair32.PairAdmission shared callA callB initial)
    (entry : initial.rip = callA.code) (stack : initial.registers .rsp = callA.stack)
    (baseA : initial.registers .rdi = callA.base)
    (counterA : initial.registers .rsi = BitVec.ofNat 64 callA.values.length)
    (baseB : initial.registers .rdx = callB.base)
    (counterB : initial.registers .rcx = BitVec.ofNat 64 callB.values.length) (choices : Choices) :
    ∃ result,
      run choices (6 * (callA.values.length + callB.values.length) + 6) initial = .ok result ∧
      Pair32.Post initial callA.values callB.values callA.target result.state ∧
      result.state.registers .rax = (sum32 (callA.values ++ callB.values)).setWidth 64 ∧
      result.instructions = 6 * (callA.values.length + callB.values.length) + 6 ∧
      result.reads = Pair32.operandReads initial callA.values callB.values ∧
      Pair32.PairAdmission shared callA callB result.state ∧
      ∀ read ∈ result.reads, OS.ArrayResources.ReadPermission shared callA.worker read := by
  have pre := Pair32.pre_of_admission admitted entry stack baseA counterA baseB counterB
  rw [code] at pre
  obtain ⟨result, success, post, value, cost, reads⟩ := exactResult pre choices
  refine ⟨result, success, post, value, cost, reads, admitted.unchangedMemory post.memory, ?_⟩
  intro read member
  exact Pair32.operandReads_permission admitted baseA baseB stack (reads ▸ member)
EOF
        if [[ $container == elf ]]; then
            cat <<'EOF'

def loadedState (prior : Space) (registers : Register → Word) (flags : Word) : State :=
  ⟨registers, ELF.codeAddress observedImage, flags, toMemory (loadedSpace prior)⟩

-- This full-ELF callable theorem has no assumed process startup. The loader
-- supplies code; current arrays and the complete return slot are caller facts.
theorem loadedResult (prior : Space) (registers : Register → Word) (flags : Word)
    {valuesA valuesB : List (BitVec 32)} {target : Word}
    (free : ELF.fresh observedImage prior = true)
    (arrayA : ArrayAt (toMemory (loadedSpace prior)) (registers .rdi) valuesA)
    (arrayB : ArrayAt (toMemory (loadedSpace prior)) (registers .rdx) valuesB)
    (boundA : ArrayBound (registers .rdi) valuesA)
    (boundB : ArrayBound (registers .rdx) valuesB)
    (counterA : registers .rsi = BitVec.ofNat 64 valuesA.length)
    (counterB : registers .rcx = BitVec.ofNat 64 valuesB.length)
    (stack : readWord (toMemory (loadedSpace prior)) (registers .rsp) = .ok target)
    (returnCanonical : canonical target = true)
    (stackAfterCanonical : canonical (registers .rsp + 8) = true) (choices : Choices) :
    ELF.load observedELF prior = .ok ⟨observedImage, loadedSpace prior⟩ ∧
    ∃ result,
      run choices (6 * (valuesA.length + valuesB.length) + 6)
        (loadedState prior registers flags) = .ok result ∧
      Pair32.Post (loadedState prior registers flags) valuesA valuesB target result.state ∧
      result.state.registers .rax = (sum32 (valuesA ++ valuesB)).setWidth 64 ∧
      result.instructions = 6 * (valuesA.length + valuesB.length) + 6 ∧
      result.reads = Pair32.operandReads (loadedState prior registers flags) valuesA valuesB := by
  refine ⟨loaded prior free, exactResult ?_ choices⟩
  exact ⟨loadedCode prior, arrayA, arrayB, boundA, boundB, counterA, counterB,
    stack, returnCanonical, stackAfterCanonical⟩
EOF
        fi
        printf '\nend EDSL.GeneratedCFG.Functional\n\n#audit_edsl\n'
    } > "$destination"
}

for container in Raw ELF; do
    functional_source "$output/stride/$container.lean" "$output/stride/${container}Functional.lean" \
        "${container,,}"
    flock /tmp/edsl-lean-build.lock lake env lean -DwarningAsError=true \
        "$output/stride/${container}Functional.lean" > "$output/stride/${container}-functional.txt" 2>&1
    cat "$output/stride/${container}-functional.txt"
done
sha256sum "$output/stride/RawFunctional.lean" "$output/stride/ELFFunctional.lean" \
    "$output/stride/Raw-functional.txt" "$output/stride/ELF-functional.txt" \
    "$output/stride/function.bin" "$output/stride/function.elf" > "$output/stride/functional-SHA256SUMS"

for container in Raw ELF; do
    pair_functional_source "$output/pair/$container.lean" "$output/pair/${container}Functional.lean" \
        "${container,,}"
    flock /tmp/edsl-lean-build.lock lake env lean -DwarningAsError=true \
        "$output/pair/${container}Functional.lean" > "$output/pair/${container}-functional.txt" 2>&1
    cat "$output/pair/${container}-functional.txt"
done
sha256sum "$output/pair/RawFunctional.lean" "$output/pair/ELFFunctional.lean" \
    "$output/pair/Raw-functional.txt" "$output/pair/ELF-functional.txt" \
    "$output/pair/function.bin" "$output/pair/function.elf" > "$output/pair/functional-SHA256SUMS"

negative="$output/rejections"
mkdir -p "$negative"
reject() {
    local name=$1 expected=$2
    shift 2
    local status=0 generated="$negative/$name.lean"
    rm -f "$generated"
    lake env "$importer" "$@" "$generated" > "$negative/$name.log.txt" 2>&1 || status=$?
    if [[ $status -ne $expected || -e $generated ]]; then
        cat "$negative/$name.log.txt"
        echo "Expected CFG admission status $expected and no obligations: $name (got $status)" >&2
        exit 1
    fi
}

# These bytes are synthetic fixtures owned by the project. No native execution
# is attempted for unsupported instructions or deliberately incomplete windows.
printf '\x89\x37\xc3' > "$negative/store.bin"
printf '\x87\x07\xc3' > "$negative/atomic.bin"
printf '\x0f\x05' > "$negative/syscall.bin"
printf '\x48\x85' > "$negative/incomplete-instruction.bin"
printf '\xeb\x01\xc3' > "$negative/outside-target.bin"
: > "$negative/empty.bin"
head -c 13 "$output/early/function.bin" > "$negative/first-ret-cutoff.bin"
head -c 64 "$output/pair/function.elf" > "$negative/truncated.elf"
pair_size=$(wc -c < "$output/pair/function.bin")
head -c "$((pair_size - 1))" "$output/pair/function.bin" > "$negative/missing-ret.bin"
reject store 3 "$negative/store.bin"
reject atomic 3 "$negative/atomic.bin"
reject syscall 3 "$negative/syscall.bin"
reject outside-target 3 "$negative/outside-target.bin"
reject incomplete-instruction 4 "$negative/incomplete-instruction.bin"
reject empty 4 "$negative/empty.bin"
reject first-ret-cutoff 3 "$negative/first-ret-cutoff.bin"
reject missing-ret 3 "$negative/missing-ret.bin"
reject first-ret-elf-cutoff 3 --elf 13 "$output/early/function.elf"
reject truncated-elf 4 --elf 35 "$negative/truncated.elf"
reject zero-span 3 --elf 0 "$output/pair/function.elf"
reject excessive-span 3 --elf 65 "$output/pair/function.elf"
reject invalid-span 2 --elf invalid "$output/pair/function.elf"
rm -f "$negative/absent-file.bin"
reject absent-file 5 "$negative/absent-file.bin"
{
    printf 'import EDSL.Stride32.Correctness\n'
    sed '/^#audit_edsl$/d' "$output/wrong-stride/Raw.lean"
    cat <<'EOF'
namespace EDSL.GeneratedCFG
-- Owned wrong-stride bytes cannot reuse this exact fixed-byte proof. This
-- failure is not a general impossibility proof for another task or contract.
theorem wrongStrideBinding : observedBytes = Stride32.bytes := by decide
end EDSL.GeneratedCFG
EOF
} > "$negative/wrong-stride-binding.lean"
binding_status=0
flock /tmp/edsl-lean-build.lock lake env lean -DwarningAsError=true \
    "$negative/wrong-stride-binding.lean" > "$negative/wrong-stride-binding.log.txt" 2>&1 || binding_status=$?
if [[ $binding_status -ne 1 ]] || ! grep -q "decide" "$negative/wrong-stride-binding.log.txt"; then
    cat "$negative/wrong-stride-binding.log.txt"
    echo 'Expected owned wrong-stride fixed-byte binding proof to fail' >&2
    exit 1
fi
sha256sum "$negative"/*.bin "$negative"/*.elf "$negative"/*.log.txt \
    "$negative/wrong-stride-binding.lean" > "$negative/SHA256SUMS"
sha256sum fixtures/cfg/* scripts/verify-cfg.sh "$output/native-check" \
    "$output/harness-arguments.txt" "$output/scope.txt" > "$output/SHA256SUMS"
printf 'Imported complete raw/ELF CFGs and observed final GCC stride/pair and early-return windows.\n'
printf 'Proved the independent stride task for literal raw/ELF bytes, with exact cost/read footprint and current OS-resource contracts.\n'
printf 'Proved the independent pair task for literal raw/ELF bytes, including exact cost/ordered reads, compatible current OS admissions and full-ELF callable loading.\n'
printf 'Static accepted wrong-stride code remains rejected by the independent native task oracle.\n'
printf 'Owned unsupported/truncated windows, omitted second RET, malformed spans and I/O failures returned their expected statuses.\n'
