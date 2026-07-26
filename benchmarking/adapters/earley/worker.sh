#!/usr/bin/env bash
set -euo pipefail

adapter_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_dir="$(cd -- "${adapter_dir}/../../.." && pwd)"

temporary_dir="$(mktemp -d "${TMPDIR:-/tmp}/earley-worker.XXXXXX")"
input_fifo="${temporary_dir}/input"
mkfifo "${input_fifo}"

forwarder_pid=""
cleanup() {
  if [[ -n "${forwarder_pid}" ]]; then
    kill "${forwarder_pid}" 2>/dev/null || true
    wait "${forwarder_pid}" 2>/dev/null || true
  fi
  rm -f -- "${input_fifo}"
  rmdir -- "${temporary_dir}" 2>/dev/null || true
}
trap cleanup EXIT INT TERM

# Bash gives asynchronous commands /dev/null as standard input when job
# control is disabled. Preserve the caller's stdin explicitly for the
# background FIFO forwarder.
exec 3<&0
cat <&3 >"${input_fifo}" &
forwarder_pid=$!

set +e
EARLEY_BENCHMARK_INPUT="${input_fifo}" isabelle ML_process \
  -d "${repo_dir}/related-work/Earley_Parser" \
  -d "${adapter_dir}" \
  -o threads=1 \
  -l Earley_Benchmark_Adapter \
  -e 'val _ = Earley_Benchmark_Worker.main ()'
status=$?
set -e

exit "${status}"
