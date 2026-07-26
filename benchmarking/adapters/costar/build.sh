#!/usr/bin/env bash
set -euo pipefail

adapter_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_dir="$(cd -- "${adapter_dir}/../../.." && pwd)"

opam exec --switch=4.14.4+flambda --set-switch -- \
  make -C "$repo_dir/related-work/CoStar" parser

exec opam exec --switch=4.14.4+flambda --set-switch -- \
  make -C "$adapter_dir" all
