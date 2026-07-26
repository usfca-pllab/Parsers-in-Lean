from __future__ import annotations

import csv
import sys
import tempfile
import unittest
from pathlib import Path

from benchmarking.manifest import Grammar, InputPoint, Rule, T
from benchmarking.run import AdapterConfig, CsvRecorder, run_lane

REPO_ROOT = Path(__file__).resolve().parents[2]
FAKE_WORKER = REPO_ROOT / "benchmarking" / "tests" / "fake_worker.py"


def test_grammar() -> Grammar:
    return Grammar(
        suite="test",
        grammar_id="timeout-grammar",
        description="runner timeout test",
        terminals=("a",),
        nonterminals=("S",),
        start="S",
        rules=(Rule("S", (T("a"),)),),
        points=(
            InputPoint("fast", "n", 1, ("a",)),
            InputPoint("timeout", "n", 2, ("a", "a")),
            InputPoint("not-run", "n", 3, ("a", "a", "a")),
        ),
        supported_parsers=("lean",),
    )


class RunnerTests(unittest.IsolatedAsyncioTestCase):
    async def test_timeout_is_recorded_and_later_points_are_skipped(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            recorder = CsvRecorder(output, "test-run")
            await run_lane(
                adapter=AdapterConfig(
                    name="lean",
                    command=(sys.executable, str(FAKE_WORKER)),
                    build=(),
                ),
                grammar=test_grammar(),
                timeout=0.05,
                startup_timeout=2.0,
                recorder=recorder,
            )
            recorder.close()
            with (output / "measurements.csv").open(
                encoding="utf-8", newline=""
            ) as handle:
                rows = list(csv.DictReader(handle))
            self.assertEqual(
                [row["status"] for row in rows],
                ["ok", "timeout", "skipped_after_timeout"],
            )
            self.assertEqual(rows[0]["elapsed_ns"], "1000")
            self.assertEqual(rows[0]["accepted"], "true")
            with (output / "metrics.csv").open(
                encoding="utf-8", newline=""
            ) as handle:
                metrics = list(csv.DictReader(handle))
            self.assertEqual(metrics[0]["metric"], "cells")
            self.assertEqual(metrics[0]["value"], "7")


if __name__ == "__main__":
    unittest.main()
