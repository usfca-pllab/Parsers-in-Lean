#!/usr/bin/env bash

set -euo pipefail

benchmark_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
isabelle_bin="${ISABELLE_BIN:-isabelle}"
benchmark_tmp="$(mktemp -d /tmp/earley-benchmark.XXXXXX)"
trap 'rm -rf -- "$benchmark_tmp"' EXIT

"$isabelle_bin" build -c -d "$benchmark_dir" Earley_Benchmark
"$isabelle_bin" export \
  -d "$benchmark_dir" \
  -n \
  -O "$benchmark_tmp" \
  -x 'Earley_Benchmark.Benchmark:PIDE/messages' \
  Earley_Benchmark >/dev/null

LC_ALL=C strings \
  "$benchmark_tmp/Earley_Benchmark.Benchmark/PIDE/messages" |
  grep '^BENCHMARK '
