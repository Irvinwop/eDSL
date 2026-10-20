#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
output=artifacts/sequential-logical64/imports
mkdir -p "$output"
# These independently selected register windows exercise typed rendering of
# all six opcodes, both register banks and ignored X through the public CLI.
# Static import certifies the finite CFG, not this function's return behavior.
cat > "$output/window.S" <<'ASM'
.text
.globl edsl_logical_import
.type edsl_logical_import,@function
edsl_logical_import:
.byte 0x48,0x21,0xc8,0x4f,0x23,0xd8
.byte 0x49,0x09,0xd8,0x4e,0x0b,0xd8
.byte 0x4a,0x31,0xd8,0x4d,0x33,0xd8,0xc3
.size edsl_logical_import,.-edsl_logical_import
.section .note.GNU-stack,"",@progbits
ASM
as --64 "$output/window.S" -o "$output/window.o"
ld -m elf_x86_64 --build-id=none -z noexecstack -e edsl_logical_import \
    -Ttext=0x401000 "$output/window.o" -o "$output/window.elf"
objcopy --dump-section ".text=$output/window.bin" "$output/window.elf"
objdump -d "$output/window.elf" > "$output/disassembly.txt"
flock /tmp/edsl-lean-build.lock lake build edsl-cfg-import
# The importer owns its kernel lock; never put an outer lock around these calls.
lake env edsl-cfg-import "$output/window.bin" "$output/Raw.lean" > "$output/raw-check.txt" 2>&1
lake env edsl-cfg-import --elf 19 "$output/window.elf" "$output/ELF.lean" > "$output/elf-check.txt" 2>&1
cat "$output/raw-check.txt" "$output/elf-check.txt"
cat > "$output/scope.txt" <<'SCOPE'
The public CLI imports an independently selected window of 19 bytes window in raw and full
ELF form. Both generated typed Lean artifacts are kernel-checked, including
exact literal bytes, six decoded logical instructions, RET, graph closure and
ELF entry binding. Both directions of AND/OR/XOR, extended banks and ignored X
appear. These are static finite-code certificates; functional correctness,
termination, caller resources and native CPU conformance remain separate.
The selected ELF is an owned callable window with no process startup. It is
never natively executed by this import check.
SCOPE
sha256sum scripts/verify-sequential-logical64-imports.sh \
    EDSL/X86/Sequential/{Model,Decode,Literals,CFGArtifact}.lean \
    lean-toolchain "$output/window.S" "$output/window.o" "$output/window.elf" \
    "$output/window.bin" "$output/disassembly.txt" "$output/Raw.lean" "$output/ELF.lean" \
    "$output/raw-check.txt" "$output/elf-check.txt" "$output/scope.txt" > "$output/SHA256SUMS"
echo 'Logical64 public raw/full-ELF typed CFG imports passed'
