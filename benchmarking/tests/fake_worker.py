#!/usr/bin/env python3
"""Small protocol worker used only by orchestration tests."""

from __future__ import annotations

import sys
import time


def emit(line: str) -> None:
    print(line, flush=True)


def main() -> int:
    grammar = None
    for raw in sys.stdin:
        line = raw.rstrip("\r\n")
        fields = line.split("\t")
        if fields[0] == "INIT":
            grammar = fields[1]
        elif fields[0] == "END":
            emit(f"READY\t{grammar}")
        elif fields[0] == "RUN":
            case_id = fields[1]
            if case_id.endswith(".timeout"):
                time.sleep(5)
                continue
            if case_id.endswith(".parser-error"):
                emit(
                    f"RESULT\t{case_id}\t2000\tparser_error\tunknown\t"
                    "unknown\tunknown\t-\ttest_error\texpected-test-error"
                )
            else:
                emit(
                    f"RESULT\t{case_id}\t1000\taccept\ttrue\tunique\ttrue\t"
                    "cells=7\t-\t-"
                )
        elif fields[0] == "STOP":
            return 0
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

