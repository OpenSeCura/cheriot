#!/bin/zsh
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

cd "$CHERIOT_DIR"

passed=0
total=0
failed_list=()

for elf in "$TEST_DIR"/*.elf; do
    total=$((total + 1))
    name=$(basename "$elf")
    echo "========================================"
    echo "Running test: $name"
    echo "========================================"
    if make -j BINARY="$elf" sim && ./Simulate; then
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
