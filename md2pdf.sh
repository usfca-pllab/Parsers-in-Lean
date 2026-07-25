#!/bin/sh
set -eu

if [ "$#" -ne 1 ]; then
  echo "Usage: $0 MARKDOWN_FILE" >&2
  exit 2
fi

input=$1
output=${input%.*}.pdf
script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)

pandoc \
  --pdf-engine=xelatex \
  -f markdown \
  -t pdf \
  --include-in-header="$script_dir/docs/preamble.tex" \
  "$input" \
  -o "$output"
