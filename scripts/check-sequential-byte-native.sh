#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
export PATH="$HOME/.elan/bin:$PATH"
export LEAN_NUM_THREADS=1

if [[ $(uname -m) != x86_64 || $(uname -s) != Linux ]]; then
    echo 'The native CMP8 conformance check requires Linux x86-64.' >&2
    exit 2
fi
native_work=$(mktemp -d /tmp/edsl-byte-native.XXXXXXXX)
trap 'rm -rf -- "$native_work"' EXIT
"${CC:-cc}" -std=gnu2x -O2 -Wall -Wextra -Werror -mno-red-zone \
    fixtures/sequential-cmp8-native.c -o "$native_work/probe"
"$native_work/probe" "$native_work/flags.bin"
flock /tmp/edsl-lean-build.lock lake build BoundedScanTests
flock /tmp/edsl-lean-build.lock lake env lean -DwarningAsError=true \
    --run tests/SequentialByteNative.lean "$native_work/flags.bin"
