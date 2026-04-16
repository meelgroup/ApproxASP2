#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(pwd)"

echo "Building ApproxASP..."
mkdir -p build && cd build
cmake -DCLINGO_BUILD_SHARED=ON ..
make -j10

cd $ROOT_DIR
echo "Done. Copied binaries to:"
cp build/approxasp "$ROOT_DIR"

echo "  $ROOT_DIR/approxasp"