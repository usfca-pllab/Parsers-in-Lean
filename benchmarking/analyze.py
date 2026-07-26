#!/usr/bin/env python3
"""Create tabular summaries and a compact Markdown report for one run."""

from __future__ import annotations

import argparse
import csv
import itertools
import sys
from collections import Counter, defaultdict
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import polars as pl  # noqa: E402


def _markdown(value: object) -> str:
    return str(value).replace("|", "\\|").replace("\n", " ")


def _table(headers: list[str], rows: list[list[object]]) -> list[str]:
    lines = [
        "| " + " | ".join(headers) + " |",
        "|" + "|".join("---" for _ in headers) + "|",
    ]
    lines.extend(
        "| " + " | ".join(_markdown(value) for value in row) + " |"
        for row in rows
    )
    return lines


def read_measurements(path: Path) -> pl.DataFrame:
    return pl.read_csv(
        path,
        null_values=[""],
        schema_overrides={
            "schema_version": pl.Int64,
            "run_id": pl.String,
            "suite": pl.String,
            "grammar_id": pl.String,
            "grammar_description": pl.String,
            "parser": pl.String,
            "case_id": pl.String,
            "size_label": pl.String,
            "parameter_name": pl.String,
            "parameter_value": pl.Int64,
            "token_count": pl.Int64,
            "input_tokens": pl.String,
            "input_sha256": pl.String,
            "timeout_seconds": pl.Float64,
            "status": pl.String,
            "outcome": pl.String,
            "accepted": pl.String,
            "ambiguity": pl.String,
            "tree_present": pl.String,
            "elapsed_ns": pl.Int64,
            "wall_elapsed_ns": pl.Int64,
            "exit_code": pl.Int64,
            "error_kind": pl.String,
            "detail": pl.String,
        },
    )


def enrich(frame: pl.DataFrame) -> pl.DataFrame:
    return (
        frame.with_columns(
            (pl.col("elapsed_ns").cast(pl.Float64) / 1_000_000).alias(
                "elapsed_ms"
            ),
            (pl.col("wall_elapsed_ns").cast(pl.Float64) / 1_000_000).alias(
                "wall_elapsed_ms"
            ),
            (pl.col("status") == "ok").alias("completed"),
            (pl.col("status") == "timeout").alias("timed_out"),
        )
        .sort(["suite", "grammar_id", "parser", "token_count", "case_id"])
    )


def pairwise_ratios(rows: list[dict]) -> list[dict]:
    grouped: dict[tuple[str, str, str], list[dict]] = defaultdict(list)
    for row in rows:
        if (
            row["status"] == "ok"
            and row["outcome"] in {"accept", "ambiguous"}
            and row["elapsed_ns"] is not None
            and row["elapsed_ns"] > 0
        ):
            grouped[
                (row["suite"], row["grammar_id"], row["case_id"])
            ].append(row)

    preference = {"lean": 0, "earley": 1, "costar": 2}
    ratios: list[dict] = []
    for (suite, grammar, case_id), measurements in sorted(grouped.items()):
        measurements.sort(key=lambda row: preference.get(row["parser"], 99))
        for baseline, compared in itertools.combinations(measurements, 2):
            ratios.append(
                {
                    "suite": suite,
                    "grammar_id": grammar,
                    "case_id": case_id,
                    "token_count": baseline["token_count"],
                    "baseline_parser": baseline["parser"],
                    "compared_parser": compared["parser"],
                    "baseline_elapsed_ns": baseline["elapsed_ns"],
                    "compared_elapsed_ns": compared["elapsed_ns"],
                    "compared_over_baseline": (
                        compared["elapsed_ns"] / baseline["elapsed_ns"]
                    ),
                }
            )
    return ratios


def write_ratio_csv(path: Path, ratios: list[dict]) -> None:
    fields = (
        "suite",
        "grammar_id",
        "case_id",
        "token_count",
        "baseline_parser",
        "compared_parser",
        "baseline_elapsed_ns",
        "compared_elapsed_ns",
        "compared_over_baseline",
    )
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        writer.writerows(ratios)


def make_report(rows: list[dict], ratios: list[dict]) -> str:
    run_ids = {row["run_id"] for row in rows}
    run_id = next(iter(run_ids)) if len(run_ids) == 1 else "multiple"
    status_counts = Counter(
        (row["suite"], row["parser"], row["status"], row["outcome"])
        for row in rows
    )
    lines = [
        f"# Benchmark analysis: `{run_id}`",
        "",
        (
            f"The dataset contains {len(rows)} planned parser/input rows. "
            "Each non-skipped row represents one parser invocation; there are "
            "no repetitions or warm-up samples."
        ),
        "",
        "## Execution and semantic outcomes",
        "",
    ]
    lines.extend(
        _table(
            ["Suite", "Parser", "Execution status", "Parse outcome", "Rows"],
            [
                [suite, parser, status, outcome, count]
                for (suite, parser, status, outcome), count in sorted(
                    status_counts.items()
                )
            ],
        )
    )

    lane_rows: list[list[object]] = []
    by_lane: dict[tuple[str, str, str], list[dict]] = defaultdict(list)
    for row in rows:
        by_lane[(row["suite"], row["grammar_id"], row["parser"])].append(row)
    for (suite, grammar, parser), lane in sorted(by_lane.items()):
        completed_sizes = [
            row["token_count"] for row in lane if row["status"] == "ok"
        ]
        timeout_sizes = [
            row["token_count"] for row in lane if row["status"] == "timeout"
        ]
        skipped = sum(row["status"].startswith("skipped_") for row in lane)
        lane_rows.append(
            [
                suite,
                grammar,
                parser,
                max(completed_sizes) if completed_sizes else "—",
                min(timeout_sizes) if timeout_sizes else "—",
                skipped,
            ]
        )
    lines.extend(["", "## Completion and timeout frontiers", ""])
    lines.extend(
        _table(
            [
                "Suite",
                "Grammar",
                "Parser",
                "Largest completed input",
                "First timeout input",
                "Skipped later inputs",
            ],
            lane_rows,
        )
    )

    known_acceptance: dict[tuple[str, str, str], list[tuple[str, str]]] = (
        defaultdict(list)
    )
    for row in rows:
        if row["status"] == "ok" and row["accepted"] in {"true", "false"}:
            known_acceptance[
                (row["suite"], row["grammar_id"], row["case_id"])
            ].append((row["parser"], row["accepted"]))
    disagreements = [
        [suite, grammar, case_id, ", ".join(f"{p}={v}" for p, v in values)]
        for (suite, grammar, case_id), values in sorted(known_acceptance.items())
        if len({value for _, value in values}) > 1
    ]
    lines.extend(["", "## Cross-parser acceptance checks", ""])
    if disagreements:
        lines.extend(
            _table(
                ["Suite", "Grammar", "Input", "Reported acceptance"],
                disagreements,
            )
        )
    else:
        lines.append(
            "No disagreement was found among parsers that reported a known "
            "Boolean acceptance result for the same input."
        )

    diagnostic_groups: dict[
        tuple[str, str, str, str, str, str], list[dict]
    ] = defaultdict(list)
    for row in rows:
        if (
            row["outcome"] == "parser_error"
            or row["status"] in {"process_error", "timeout"}
        ):
            diagnostic_groups[
                (
                    row["suite"],
                    row["grammar_id"],
                    row["parser"],
                    row["status"],
                    row["error_kind"] or row["outcome"],
                    row["detail"] or "—",
                )
            ].append(row)
    error_rows: list[list[object]] = []
    for (
        suite,
        grammar,
        parser,
        status,
        kind,
        detail,
    ), group in sorted(diagnostic_groups.items()):
        ordered = sorted(group, key=lambda row: (row["token_count"], row["case_id"]))
        error_rows.append(
            [
                suite,
                grammar,
                parser,
                status,
                kind,
                len(ordered),
                ordered[0]["case_id"],
                ordered[-1]["case_id"],
                detail,
            ]
        )
    lines.extend(["", "## Parser, process, and timeout diagnostics", ""])
    if error_rows:
        lines.extend(
            _table(
                [
                    "Suite",
                    "Grammar",
                    "Parser",
                    "Status",
                    "Kind",
                    "Rows",
                    "First input",
                    "Last input",
                    "Detail",
                ],
                error_rows,
            )
        )
    else:
        lines.append("No parser errors, process errors, or timeouts were recorded.")

    ratio_groups: dict[tuple[str, str, str, str], list[dict]] = defaultdict(list)
    for ratio in ratios:
        ratio_groups[
            (
                ratio["suite"],
                ratio["grammar_id"],
                ratio["baseline_parser"],
                ratio["compared_parser"],
            )
        ].append(ratio)
    ratio_rows = [
        [
            suite,
            grammar,
            f"{compared}/{baseline}",
            max(values, key=lambda row: row["token_count"])["token_count"],
            f"{max(values, key=lambda row: row['token_count'])['compared_over_baseline']:.3g}",
        ]
        for (suite, grammar, baseline, compared), values in sorted(
            ratio_groups.items()
        )
    ]
    lines.extend(["", "## Direct timing ratios", ""])
    if ratio_rows:
        lines.extend(
            _table(
                [
                    "Suite",
                    "Grammar",
                    "Ratio",
                    "Largest shared input",
                    "Ratio at that input",
                ],
                ratio_rows,
            )
        )
        lines.extend(
            [
                "",
                (
                    "Each displayed ratio uses the single observations at the "
                    "largest input completed by both parsers. `ratios.csv` "
                    "contains every direct per-input ratio."
                ),
            ]
        )
    else:
        lines.append("No input had usable timings from two parsers.")
    lines.append("")
    return "\n".join(lines)


def parse_arguments(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Analyze measurements.csv from one benchmark result directory."
    )
    parser.add_argument("run_directory", type=Path)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    arguments = parse_arguments(argv)
    run_directory = arguments.run_directory.resolve()
    measurements = run_directory / "measurements.csv"
    if not measurements.is_file():
        raise FileNotFoundError(measurements)
    summary = enrich(read_measurements(measurements))
    summary.write_csv(run_directory / "summary.csv")
    summary.write_parquet(run_directory / "summary.parquet")
    rows = summary.to_dicts()
    ratios = pairwise_ratios(rows)
    write_ratio_csv(run_directory / "ratios.csv", ratios)
    (run_directory / "report.md").write_text(
        make_report(rows, ratios), encoding="utf-8"
    )
    print(f"analysis: {run_directory / 'report.md'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
