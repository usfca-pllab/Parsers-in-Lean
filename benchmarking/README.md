# Joint parser benchmarks

This directory benchmarks the generated Lean memoized parser, the Isabelle
Earley parser, and CoStar from one grammar/input manifest. The runner makes
exactly one timed parser call for each input: it does not warm up a worker,
repeat a measurement, or compute timing aggregates.

The adapter-specific implementation and tool setup are documented in
[`related-work/earley.md`](../related-work/earley.md) and
[`related-work/costar.md`](../related-work/costar.md). CoStar commands load the
configured `4.14.4+flambda` opam switch themselves.

## Initial experiment

From the repository root, run:

```sh
python3 benchmarking/run.py \
  --suite earley \
  --suite classical \
  --timeout 60 \
  --jobs 6
```

The timeout applies separately to each input. Inputs are ordered by size within
each `(parser, grammar)` lane. A lane stops at its first timeout and records
larger inputs as `skipped_after_timeout`; other lanes continue. Parser-level
answers such as rejection, CoStar ambiguity, and CoStar left-recursion errors
are data rather than harness failures, so they do not trigger early stopping.
A crashed or malformed worker stops only its lane.

`--jobs` limits concurrent lanes, not the number of samples per input. Use
`--jobs 1` for an uncontended timing run or a larger value to finish an
exploratory run sooner. Run `python3 benchmarking/run.py --help` for all
options and `--list` to inspect the input grid. The default suites are
`earley` and `classical`; the `smoke` suite contains the two earlier Lean-only
examples.

Use a repeatable `--grammar ID` after selecting suites to run or debug only
particular grammars, for example:

```sh
python3 benchmarking/run.py \
  --suite classical \
  --grammar P1 \
  --parser lean \
  --timeout 60
```

Grammar IDs are matched exactly within the selected suites. Unknown IDs and IDs
that are ambiguous across selected suites are rejected before adapters build.

Adapters are built serially before any timing begins. Pass `--no-build` to use
existing executables. Commands and build hooks live in
[`adapters.toml`](adapters.toml).

## Suites

The canonical definitions are in [`manifest.py`](manifest.py):

- `earley`: `cfg1`–`cfg5` on every odd length `a^n`, for
  `n = 1, 3, ..., 65`. Odd lengths keep every `cfg3` input in its language.
- `classical`: `R1`, `R2`, `P1`, `P2`, `C1`, and `A1` at the small, medium,
  and large points specified in `related-work/grammars/classical.md`.
- `smoke`: Lean-only `S → a S S | b S S | ε` and
  `S → S S | a | b`, both on `(ab)^3`.

Every grammar records terminal and nonterminal names, ordered productions, a
start symbol, supported adapters, and explicit token sequences. Workers receive
numeric IDs generated from these declarations, keeping the three ports in
sync. The two joint suites are epsilon-free, matching the verified envelope of
the Earley implementation. Nullable smoke cases remain Lean-only. Earley
constructs one representative tree and therefore reports ambiguity as
`unknown`; CoStar reports its explicit ambiguity and left-recursion outcomes.

## Recorded data

Each run creates `benchmarking/results/<UTC-run-id>/`, or the directory passed
with `--output`. Rows are flushed after every result so an interrupted
experiment remains inspectable.

- `measurements.csv` has one row per planned parser/input pair. It records the
  input tokens and SHA-256 digest, execution status, semantic outcome, nullable
  acceptance/ambiguity/tree fields, adapter-measured `elapsed_ns`, parent
  `wall_elapsed_ns`, and diagnostics.
- `metrics.csv` is long-form parser-specific data. For example, Earley reports
  `chart_items` and `pointers`, while Lean can report memo-table statistics.
- `metadata.json` contains non-tabular run configuration, commands, repository
  state, host information, and tool versions.
- `build-<parser>.log` preserves each selected adapter's build output.

The execution `status` is one of `ok`, `timeout`, `process_error`,
`skipped_after_timeout`, or `skipped_after_failure`. The independent semantic
`outcome` is normally `accept`, `reject`, `ambiguous`, or `parser_error`.
Unknown Boolean-like facts use the literal `unknown`; this accommodates
Earley's single-tree interface and parser-specific limitations without
inventing agreement.

The worker's adapter-local high-resolution timer covers parsing and forcing its
reported result. Grammar initialization, input transmission, and result
serialization are outside `elapsed_ns`. The parent measures `wall_elapsed_ns`
with a monotonic clock to diagnose protocol and runtime overhead.

## Analysis and plots

Keep data processing separate from measurement:

```sh
python3 benchmarking/analyze.py benchmarking/results/<run-id>
python3 benchmarking/plot.py benchmarking/results/<run-id>
```

Analysis uses Polars and adds:

- `summary.csv` and `summary.parquet`, which preserve every single observation
  and add millisecond/status convenience columns;
- `ratios.csv`, containing direct per-input timing ratios wherever two parsers
  completed the same point; and
- `report.md`, covering outcomes, acceptance disagreements, parser errors,
  timeout frontiers, largest completed sizes, and ratios at the largest shared
  input.

Plotting uses `summary.csv` and creates one consolidated PNG and PDF per suite
under `plots/`. Each grammar is a subplot with input token count on the x-axis
and the one observed elapsed time on a logarithmic y-axis. Parser colors are
stable; ambiguity, rejection, parser error, and timeout use distinct markers.
There are no error bars because inputs are not repeated.

Both stages accept `--help`. Use repeated `--suite` or `--format` options to
select plot outputs.

## Adapter protocol

The runner starts one persistent worker per lane. All messages are UTF-8 TSV,
one line at a time. Fields cannot contain tabs or newlines.

Initialization is:

```text
INIT	<grammar>	<start-nt-id>	<nt-count>	<term-count>	<rule-count>
RULE	<lhs-id>	<T:id,N:id,... or ->
...
END
```

The worker replies `READY	<grammar>`. For each input the runner sends:

```text
RUN	<case-id>	<comma-separated-terminal-ids or ->
```

The response is:

```text
RESULT	<case-id>	<elapsed-ns>	<outcome>	<accepted>	<ambiguity>	<tree-present>	<k=v;k=v or ->	<error-kind or ->	<detail or ->
```

Canonical fact values are `true`, `false`, and `unknown`; ambiguity uses
`unique`, `ambiguous`, or `unknown`. After the lane, the runner sends `STOP`.
The parent enforces the timeout, terminates the worker's entire process group,
and is the only process that writes result files.

## Adding a grammar or input family

Add a `Grammar` entry in `manifest.py`, preserving production order where it is
semantically relevant. Declare a point for every input to be measured and use
`supported_parsers` if an experiment is implementation-specific. Manifest
validation rejects duplicate IDs, undeclared symbols/tokens, invalid starts,
and accidental empty inputs for epsilon-free grammars. Because adapters consume
the generic numeric protocol, a new grammar normally requires no adapter
changes.
