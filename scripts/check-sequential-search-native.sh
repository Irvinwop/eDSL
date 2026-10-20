#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
export PATH="$HOME/.elan/bin:$PATH"
export LEAN_NUM_THREADS=1

if [[ $(uname -m) != x86_64 || $(uname -s) != Linux ]]; then
    echo 'The native search-instruction conformance check requires Linux x86-64.' >&2
    exit 2
fi
native_work=$(mktemp -d /tmp/edsl-search-native.XXXXXXXX)
trap 'rm -rf -- "$native_work"' EXIT
"${CC:-gcc-13}" -std=gnu2x -O2 -Wall -Wextra -Werror -Wpedantic -mno-red-zone \
    fixtures/sequential-search-native.c -o "$native_work/probe"
"$native_work/probe" "$native_work/capture.bin"
# The validator imports only the production machine, not the search test library.
flock /tmp/edsl-lean-build.lock lake build EDSL.X86.Sequential.Machine
flock /tmp/edsl-lean-build.lock lake env lean -j1 -DwarningAsError=true \
    -DautoImplicit=false --run tests/SequentialSearchNative.lean "$native_work/capture.bin"
