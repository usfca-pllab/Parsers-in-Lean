#!/usr/bin/env python3
"""Generate consolidated scaling plots from an analyzed benchmark run."""

from __future__ import annotations

import argparse
import math
import os
import sys
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from benchmarking.manifest import DEFAULT_SUITES, PARSERS  # noqa: E402


def parse_arguments(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Plot summary.csv from one benchmark result directory."
    )
    parser.add_argument("run_directory", type=Path)
    parser.add_argument(
        "--suite",
        action="append",
        help="suite to plot; repeatable (default: earley and classical if present)",
    )
    parser.add_argument(
        "--format",
        dest="formats",
        action="append",
        choices=("png", "pdf"),
        help="output format; repeatable (default: png and pdf)",
    )
    parser.add_argument(
        "--output-directory",
        type=Path,
        help="plot destination (default: RUN_DIRECTORY/plots)",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    arguments = parse_arguments(argv)
    run_directory = arguments.run_directory.resolve()
    summary_path = run_directory / "summary.csv"
    if not summary_path.is_file():
        raise FileNotFoundError(
            f"{summary_path} is missing; run benchmarking/analyze.py first"
        )
    output_directory = (
        arguments.output_directory.resolve()
        if arguments.output_directory
        else run_directory / "plots"
    )
    output_directory.mkdir(parents=True, exist_ok=True)
    os.environ.setdefault(
        "MPLCONFIGDIR",
        str((Path(__file__).with_name(".cache") / "matplotlib").resolve()),
    )

    import matplotlib.pyplot as plt
    import polars as pl
    from matplotlib.lines import Line2D

    data = pl.read_csv(
        summary_path,
        null_values=[""],
        schema_overrides={
            "token_count": pl.Int64,
            "timeout_seconds": pl.Float64,
            "elapsed_ms": pl.Float64,
        },
    )
    available_suites = data.get_column("suite").unique().to_list()
    selected_suites = arguments.suite or [
        suite for suite in DEFAULT_SUITES if suite in available_suites
    ]
    formats = tuple(dict.fromkeys(arguments.formats or ("png", "pdf")))
    palette = {
        "lean": "#1f77b4",
        "earley": "#ff7f0e",
        "costar": "#2ca02c",
    }
    outcome_markers = {
        "ambiguous": ("D", "ambiguous"),
        "reject": ("X", "reject"),
        "parser_error": ("v", "parser error"),
        "timeout": ("^", "timeout"),
    }

    for suite in selected_suites:
        suite_data = data.filter(pl.col("suite") == suite)
        if suite_data.is_empty():
            print(f"warning: suite {suite!r} has no rows", file=sys.stderr)
            continue
        grammars = suite_data.get_column("grammar_id").unique(
            maintain_order=True
        ).to_list()
        columns = min(3, len(grammars))
        rows = math.ceil(len(grammars) / columns)
        figure, axes = plt.subplots(
            rows,
            columns,
            figsize=(5.2 * columns, 3.8 * rows),
            squeeze=False,
            constrained_layout=True,
        )
        for axis, grammar in zip(axes.flat, grammars):
            grammar_data = suite_data.filter(
                pl.col("grammar_id") == grammar
            )
            annotation_count = 0
            for parser_name in PARSERS:
                parser_data = grammar_data.filter(
                    pl.col("parser") == parser_name
                ).sort("token_count")
                if parser_data.is_empty():
                    continue
                color = palette[parser_name]
                successful = parser_data.filter(
                    (pl.col("status") == "ok")
                    & pl.col("elapsed_ms").is_not_null()
                    & pl.col("outcome").is_in(["accept", "ambiguous"])
                )
                if not successful.is_empty():
                    axis.plot(
                        successful.get_column("token_count").to_list(),
                        [
                            max(value, 1e-6)
                            for value in successful.get_column(
                                "elapsed_ms"
                            ).to_list()
                        ],
                        color=color,
                        marker="o",
                        linewidth=1.5,
                        markersize=4,
                        label=parser_name,
                    )
                for outcome, (marker, _) in outcome_markers.items():
                    if outcome == "timeout":
                        marked = parser_data.filter(
                            pl.col("status") == "timeout"
                        )
                        y_values = (
                            marked.get_column("timeout_seconds") * 1000
                        ).to_list()
                    else:
                        marked = parser_data.filter(
                            (pl.col("status") == "ok")
                            & (pl.col("outcome") == outcome)
                            & pl.col("elapsed_ms").is_not_null()
                        )
                        y_values = (
                            marked.get_column("elapsed_ms").to_list()
                            if not marked.is_empty()
                            else []
                        )
                    if not marked.is_empty():
                        axis.scatter(
                            marked.get_column("token_count").to_list(),
                            [max(value, 1e-6) for value in y_values],
                            color=color,
                            marker=marker,
                            s=45,
                            zorder=4,
                        )
                unplaced = parser_data.filter(
                    pl.col("status").is_in(
                        ["process_error", "skipped_after_failure"]
                    )
                ).height
                if unplaced:
                    annotation_count += unplaced
            if annotation_count:
                axis.text(
                    0.02,
                    0.98,
                    f"{annotation_count} process-error/skipped rows",
                    transform=axis.transAxes,
                    va="top",
                    fontsize=8,
                )
            axis.set_title(grammar)
            axis.set_xlabel("Input size (tokens)")
            axis.set_ylabel("Elapsed time (ms)")
            axis.set_yscale("log")
            axis.grid(True, which="both", alpha=0.25)
        for axis in list(axes.flat)[len(grammars) :]:
            axis.set_visible(False)

        parser_handles = [
            Line2D([0], [0], color=palette[name], marker="o", label=name)
            for name in PARSERS
            if not suite_data.filter(pl.col("parser") == name).is_empty()
        ]
        semantic_handles = [
            Line2D(
                [0],
                [0],
                color="#555555",
                marker=marker,
                linestyle="None",
                label=label,
            )
            for marker, label in outcome_markers.values()
        ]
        figure.legend(
            handles=parser_handles + semantic_handles,
            loc="outside lower center",
            ncols=min(4, len(parser_handles) + len(semantic_handles)),
        )
        figure.suptitle(
            f"{suite} suite: one observation per parser and input",
            fontsize=14,
        )
        for output_format in formats:
            path = output_directory / f"{suite}.{output_format}"
            figure.savefig(path, dpi=180 if output_format == "png" else None)
            print(f"plot: {path}")
        plt.close(figure)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
