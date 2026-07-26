#!/usr/bin/env bash
set -euo pipefail

adapter_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
worker="$adapter_dir/worker"

if [[ ! -x "$worker" ]]; then
  echo "CoStar adapter is not built; run $adapter_dir/build.sh first" >&2
  exit 127
fi

# Deep successful derivations can exceed the common 8 MiB native OCaml stack.
# Let the benchmark runner's explicit per-input timeout be the limiting guard.
if ! ulimit -s unlimited 2>/dev/null; then
  echo "warning: could not raise CoStar worker stack limit" >&2
fi

exec "$worker"
