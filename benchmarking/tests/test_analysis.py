from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from benchmarking.analyze import main as analyze
from benchmarking.manifest import Grammar, InputPoint, Rule, T
from benchmarking.plot import main as plot
from benchmarking.run import CsvRecorder


class AnalysisTests(unittest.TestCase):
    def test_analysis_and_plot_outputs_from_single_observations(self) -> None:
        grammar = Grammar(
            suite="test",
            grammar_id="G",
            description="analysis fixture",
            terminals=("a",),
            nonterminals=("S",),
            start="S",
            rules=(Rule("S", (T("a"),)),),
            points=(
                InputPoint("one", "n", 1, ("a",)),
                InputPoint("two", "n", 2, ("a", "a")),
            ),
        )
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            recorder = CsvRecorder(output, "analysis-test")
            for parser, elapsed in (("lean", 1_000_000), ("earley", 2_000_000)):
                recorder.record(
                    parser=parser,
                    grammar=grammar,
                    point=grammar.points[0],
                    timeout_seconds=60,
                    status="ok",
                    outcome="accept",
                    accepted="true",
                    ambiguity="unknown",
                    tree_present="true",
                    elapsed_ns=elapsed,
                    wall_elapsed_ns=elapsed + 100,
                )
            recorder.record(
                parser="lean",
                grammar=grammar,
                point=grammar.points[1],
                timeout_seconds=60,
                status="timeout",
                wall_elapsed_ns=60_000_000_000,
                error_kind="timeout",
            )
            recorder.record(
                parser="costar",
                grammar=grammar,
                point=grammar.points[1],
                timeout_seconds=60,
                status="ok",
                outcome="parser_error",
                accepted="unknown",
                ambiguity="unknown",
                tree_present="false",
                elapsed_ns=1_000,
                wall_elapsed_ns=1_100,
                error_kind="left_recursion",
            )
            recorder.close()

            self.assertEqual(analyze([str(output)]), 0)
            self.assertTrue((output / "summary.csv").is_file())
            self.assertTrue((output / "summary.parquet").is_file())
            self.assertIn(
                "largest input completed",
                (output / "report.md").read_text(encoding="utf-8").lower(),
            )
            self.assertEqual(
                plot(
                    [
                        str(output),
                        "--suite",
                        "test",
                        "--format",
                        "png",
                    ]
                ),
                0,
            )
            self.assertTrue((output / "plots" / "test.png").is_file())


if __name__ == "__main__":
    unittest.main()
