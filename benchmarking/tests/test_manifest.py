from __future__ import annotations

import unittest

from benchmarking.manifest import GRAMMARS, select_grammars, validate_manifest
from benchmarking.protocol import ProtocolError, init_lines, parse_result, run_line
from benchmarking.run import filter_grammars


class ManifestTests(unittest.TestCase):
    def test_manifest_is_valid_and_has_expected_grid(self) -> None:
        validate_manifest()
        earley = select_grammars(("earley",))
        classical = select_grammars(("classical",))
        smoke = select_grammars(("smoke",))
        self.assertEqual(len(earley), 5)
        self.assertTrue(all(len(grammar.points) == 33 for grammar in earley))
        self.assertEqual(
            [len(point.tokens) for point in earley[0].points],
            list(range(1, 66, 2)),
        )
        self.assertEqual(len(classical), 6)
        self.assertTrue(all(len(grammar.points) == 3 for grammar in classical))
        self.assertEqual(len(smoke), 2)
        self.assertTrue(
            all(grammar.supported_parsers == ("lean",) for grammar in smoke)
        )

    def test_documented_classical_token_counts(self) -> None:
        counts = {
            grammar.grammar_id: [len(point.tokens) for point in grammar.points]
            for grammar in select_grammars(("classical",))
        }
        self.assertEqual(counts["R1"], [5, 33, 257])
        self.assertEqual(counts["R2"], [7, 65, 513])
        self.assertEqual(counts["P1"], [8, 64, 512])
        self.assertEqual(counts["P2"], [8, 64, 512])
        self.assertEqual(counts["C1"], [7, 63, 511])
        self.assertEqual(counts["A1"], [11, 41, 161])

    def test_protocol_encoding_uses_numeric_symbols_and_epsilon(self) -> None:
        binary = next(
            grammar
            for grammar in GRAMMARS
            if grammar.grammar_id == "binary-epsilon"
        )
        lines = init_lines(binary)
        self.assertEqual(lines[0], "INIT\tbinary-epsilon\t0\t1\t2\t3")
        self.assertIn("RULE\t0\t-", lines)
        self.assertEqual(
            run_line(binary, binary.points[0]),
            "RUN\tsmoke.binary-epsilon.ab3\t0,1,0,1,0,1",
        )

    def test_result_protocol_rejects_unknown_enum_values(self) -> None:
        with self.assertRaises(ProtocolError):
            parse_result(
                "RESULT\tcase\t1\tmaybe\ttrue\tunique\ttrue\t-\t-\t-",
                "case",
            )

    def test_grammar_filter_is_exact_and_reports_unknown_ids(self) -> None:
        classical = select_grammars(("classical",))
        self.assertEqual(
            [grammar.grammar_id for grammar in filter_grammars(classical, ["P1"])],
            ["P1"],
        )
        with self.assertRaisesRegex(ValueError, "unknown grammar"):
            filter_grammars(classical, ["p1"])


if __name__ == "__main__":
    unittest.main()
