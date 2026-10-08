#!/bin/bash
# Copyright 2026 Google LLC
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     https://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

set -e

CHERIOT_DIR="/Users/muralivi/work/Cherified/cheriot"
TEST_DIR="/Users/muralivi/work/Cherified/basic-riscv-tests-cheriot/binaries"
TEST_SUITE="/Users/muralivi/work/Cheriot/cheriot-rtos/tests/build/cheriot/cheriot/release/test-suite"
LLVM_DIR="${LLVM_DIR:-$HOME/work/Cheriot/llvm-project/builds/cheriot-llvm}"
SIM="${SIM:-./Simulate}"

cd "$CHERIOT_DIR"

TMP_BIN=$(mktemp)
TMP_HEX=$(mktemp)
trap 'rm -f "$TMP_BIN" "$TMP_HEX"' EXIT

passed=0
total=0
failed_list=()

for elf in "$TEST_DIR"/*.elf "$TEST_SUITE"; do
    total=$((total + 1))
    name=$(basename "$elf")
    echo "========================================"
    echo "Running test: $name"
    echo "========================================"
    TOHOST=$("$LLVM_DIR/bin/llvm-objdump" -t "$elf" | awk '$NF == "tohost" {print $1}')
    "$LLVM_DIR/bin/llvm-objcopy" -O binary "$elf" "$TMP_BIN"
    hexdump -v -e '1/8 "%016x\n"' "$TMP_BIN" > "$TMP_HEX"
    if "$SIM" "+bin=$TMP_HEX" "+tohost=$TOHOST"; then
        echo "[PASS] $name"
        passed=$((passed + 1))
    else
        echo "[FAIL] $name"
        failed_list+=("$name")
    fi
done

echo ""
echo "Summary: $passed/$total tests passed."
if [ ${#failed_list[@]} -gt 0 ]; then
    echo "Failed tests: ${failed_list[*]}"
    exit 1
fi
