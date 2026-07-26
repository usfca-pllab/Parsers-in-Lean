#!/usr/bin/env bash
set -euo pipefail

adapter_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_dir="$(cd -- "${adapter_dir}/../../.." && pwd)"

exec isabelle build \
  -b \
  -j 1 \
  -d "${repo_dir}/related-work/Earley_Parser" \
  -D "${adapter_dir}"
