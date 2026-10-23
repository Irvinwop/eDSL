#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail
if [[ $# -ne 0 ]]; then
    echo 'usage: verify-multiply-packets.sh' >&2
    exit 2
fi
cd "$(dirname "${BASH_SOURCE[0]}")/.."
export EDSL_REGISTERED_PACKET_OUTPUT=${EDSL_MULTIPLY_OUTPUT:-artifacts/multiply-packets}
exec bash scripts/verify-registered-packets.sh multiplyModulo64 tests.GradingMultiply \
    EDSL.Tests.GradingMultiply 11696 12 4912 8
