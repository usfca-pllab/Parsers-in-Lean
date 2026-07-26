#!/usr/bin/env python3
"""Run the same grammar/input manifest against the three parser adapters."""

from __future__ import annotations

import argparse
import asyncio
import csv
import hashlib
import json
import os
import platform
import shlex
import signal
import subprocess
import sys
import time
import tomllib
from collections import deque
from dataclasses import asdict, dataclass
from datetime import UTC, datetime
from pathlib import Path
from typing import Iterable, TextIO

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from benchmarking.manifest import (  # noqa: E402
    DEFAULT_SUITES,
    GRAMMARS,
    PARSERS,
    Grammar,
    InputPoint,
    select_grammars,
    suites,
)
from benchmarking.protocol import (  # noqa: E402
    AdapterResult,
    ProtocolError,
    init_lines,
    parse_ready,
    parse_result,
    run_line,
)

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_CONFIG = Path(__file__).with_name("adapters.toml")
SCHEMA_VERSION = 1

MEASUREMENT_FIELDS = (
    "schema_version",
    "run_id",
    "suite",
    "grammar_id",
    "grammar_description",
    "parser",
    "case_id",
    "size_label",
    "parameter_name",
    "parameter_value",
    "token_count",
    "input_tokens",
    "input_sha256",
    "timeout_seconds",
    "status",
    "outcome",
    "accepted",
    "ambiguity",
    "tree_present",
    "elapsed_ns",
    "wall_elapsed_ns",
    "exit_code",
    "error_kind",
    "detail",
)

METRIC_FIELDS = (
    "schema_version",
    "run_id",
    "suite",
    "grammar_id",
    "parser",
    "case_id",
    "metric",
    "value",
)


@dataclass(frozen=True)
class AdapterConfig:
    name: str
    command: tuple[str, ...]
    build: tuple[str, ...]


def load_adapter_config(path: Path) -> dict[str, AdapterConfig]:
    with path.open("rb") as handle:
        document = tomllib.load(handle)
    raw_adapters = document.get("adapters")
    if not isinstance(raw_adapters, dict):
        raise ValueError(f"{path}: missing [adapters] table")
    adapters: dict[str, AdapterConfig] = {}
    for name, raw in raw_adapters.items():
        if not isinstance(raw, dict):
            raise ValueError(f"{path}: adapters.{name} must be a table")
        command = raw.get("command")
        build = raw.get("build", [])
        if (
            not isinstance(command, list)
            or not command
            or not all(isinstance(part, str) and part for part in command)
        ):
            raise ValueError(f"{path}: adapters.{name}.command must be nonempty")
        if not isinstance(build, list) or not all(
            isinstance(part, str) and part for part in build
        ):
            raise ValueError(f"{path}: adapters.{name}.build must be an array")
        adapters[name] = AdapterConfig(name, tuple(command), tuple(build))
    missing = set(PARSERS) - set(adapters)
    if missing:
        raise ValueError(f"{path}: missing adapter definitions {sorted(missing)}")
    return adapters


def _display_command(command: Iterable[str]) -> str:
    return shlex.join(command)


def _run_capture(command: list[str], timeout: float = 10.0) -> str:
    try:
        process = subprocess.run(
            command,
            cwd=REPO_ROOT,
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            timeout=timeout,
        )
    except (FileNotFoundError, subprocess.TimeoutExpired) as exception:
        return f"unavailable: {exception}"
    output = process.stdout.strip().replace("\n", " | ")
    if process.returncode != 0:
        return f"exit {process.returncode}: {output}"
    return output


def collect_metadata(
    *,
    run_id: str,
    arguments: argparse.Namespace,
    adapters: dict[str, AdapterConfig],
    selected_parsers: tuple[str, ...],
    selected_suites: tuple[str, ...],
    grammars: tuple[Grammar, ...],
) -> dict:
    revision = _run_capture(["git", "rev-parse", "HEAD"])
    try:
        dirty_process = subprocess.run(
            ["git", "status", "--porcelain"],
            cwd=REPO_ROOT,
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            timeout=20.0,
        )
        dirty_lines = dirty_process.stdout.splitlines()
    except (FileNotFoundError, subprocess.TimeoutExpired) as exception:
        dirty_lines = [f"unavailable: {exception}"]
    manifest_payload = json.dumps(
        [asdict(grammar) for grammar in grammars],
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return {
        "schema_version": SCHEMA_VERSION,
        "run_id": run_id,
        "started_at_utc": datetime.now(UTC).isoformat(),
        "finished_at_utc": None,
        "state": "starting",
        "command_line": sys.argv,
        "configuration": {
            "timeout_seconds_per_input": arguments.timeout,
            "jobs": arguments.jobs,
            "suites": list(selected_suites),
            "parsers": list(selected_parsers),
            "grammars": [
                f"{grammar.suite}/{grammar.grammar_id}" for grammar in grammars
            ],
            "manifest_sha256": hashlib.sha256(manifest_payload).hexdigest(),
            "adapter_config": str(arguments.config),
            "build_enabled": not arguments.no_build,
        },
        "adapters": {
            name: {
                "command": list(adapters[name].command),
                "build": list(adapters[name].build),
            }
            for name in selected_parsers
        },
        "repository": {
            "root": str(REPO_ROOT),
            "revision": revision,
            "dirty": bool(dirty_lines),
            "status_porcelain": dirty_lines,
        },
        "host": {
            "platform": platform.platform(),
            "machine": platform.machine(),
            "processor": platform.processor(),
            "logical_cpus": os.cpu_count(),
            "python": sys.version,
        },
        "tools": {
            "lake": _run_capture(["lake", "--version"]),
            "isabelle": _run_capture(["isabelle", "version"]),
            "rocq": _run_capture(
                [
                    "opam",
                    "exec",
                    "--switch=4.14.4+flambda",
                    "--set-switch",
                    "--",
                    "rocq",
                    "--version",
                ]
            ),
            "ocamlopt": _run_capture(
                [
                    "opam",
                    "exec",
                    "--switch=4.14.4+flambda",
                    "--set-switch",
                    "--",
                    "ocamlopt",
                    "-version",
                ]
            ),
        },
    }


def write_metadata(path: Path, metadata: dict) -> None:
    temporary = path.with_suffix(".json.tmp")
    with temporary.open("w", encoding="utf-8") as handle:
        json.dump(metadata, handle, indent=2, sort_keys=True)
        handle.write("\n")
    temporary.replace(path)


def run_build(
    adapter: AdapterConfig, output_directory: Path
) -> None:
    if not adapter.build:
        return
    print(f"[build:{adapter.name}] {_display_command(adapter.build)}", flush=True)
    process = subprocess.run(
        adapter.build,
        cwd=REPO_ROOT,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
    )
    log_path = output_directory / f"build-{adapter.name}.log"
    log_path.write_text(process.stdout, encoding="utf-8")
    if process.returncode != 0:
        tail = "\n".join(process.stdout.splitlines()[-20:])
        raise RuntimeError(
            f"{adapter.name} build failed with exit {process.returncode}; "
            f"see {log_path}\n{tail}"
        )


class CsvRecorder:
    def __init__(self, output_directory: Path, run_id: str):
        self.run_id = run_id
        self.measurement_handle: TextIO = (
            output_directory / "measurements.csv"
        ).open("w", encoding="utf-8", newline="")
        self.metric_handle: TextIO = (output_directory / "metrics.csv").open(
            "w", encoding="utf-8", newline=""
        )
        self.measurement_writer = csv.DictWriter(
            self.measurement_handle, fieldnames=MEASUREMENT_FIELDS
        )
        self.metric_writer = csv.DictWriter(
            self.metric_handle, fieldnames=METRIC_FIELDS
        )
        self.measurement_writer.writeheader()
        self.metric_writer.writeheader()
        self.flush()

    def record(
        self,
        *,
        parser: str,
        grammar: Grammar,
        point: InputPoint,
        timeout_seconds: float,
        status: str,
        outcome: str = "unknown",
        accepted: str = "unknown",
        ambiguity: str = "unknown",
        tree_present: str = "unknown",
        elapsed_ns: int | None = None,
        wall_elapsed_ns: int | None = None,
        exit_code: int | None = None,
        error_kind: str = "",
        detail: str = "",
        metrics: dict[str, str] | None = None,
    ) -> None:
        case_id = grammar.case_id(point)
        self.measurement_writer.writerow(
            {
                "schema_version": SCHEMA_VERSION,
                "run_id": self.run_id,
                "suite": grammar.suite,
                "grammar_id": grammar.grammar_id,
                "grammar_description": grammar.description,
                "parser": parser,
                "case_id": case_id,
                "size_label": point.label,
                "parameter_name": point.parameter_name,
                "parameter_value": point.parameter_value,
                "token_count": len(point.tokens),
                "input_tokens": " ".join(point.tokens),
                "input_sha256": grammar.input_hash(point),
                "timeout_seconds": timeout_seconds,
                "status": status,
                "outcome": outcome,
                "accepted": accepted,
                "ambiguity": ambiguity,
                "tree_present": tree_present,
                "elapsed_ns": "" if elapsed_ns is None else elapsed_ns,
                "wall_elapsed_ns": (
                    "" if wall_elapsed_ns is None else wall_elapsed_ns
                ),
                "exit_code": "" if exit_code is None else exit_code,
                "error_kind": error_kind,
                "detail": detail,
            }
        )
        for key, value in sorted((metrics or {}).items()):
            self.metric_writer.writerow(
                {
                    "schema_version": SCHEMA_VERSION,
                    "run_id": self.run_id,
                    "suite": grammar.suite,
                    "grammar_id": grammar.grammar_id,
                    "parser": parser,
                    "case_id": case_id,
                    "metric": key,
                    "value": value,
                }
            )
        self.flush()

    def flush(self) -> None:
        self.measurement_handle.flush()
        self.metric_handle.flush()

    def close(self) -> None:
        self.flush()
        self.measurement_handle.close()
        self.metric_handle.close()


class Worker:
    def __init__(self, adapter: AdapterConfig):
        self.adapter = adapter
        self.process: asyncio.subprocess.Process | None = None
        self.stderr_tail: deque[str] = deque(maxlen=100)
        self.stderr_task: asyncio.Task | None = None

    async def start(self, grammar: Grammar, timeout: float) -> None:
        self.process = await asyncio.create_subprocess_exec(
            *self.adapter.command,
            cwd=REPO_ROOT,
            stdin=asyncio.subprocess.PIPE,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE,
            start_new_session=True,
            limit=1024 * 1024,
        )
        self.stderr_task = asyncio.create_task(self._drain_stderr())
        await self._write_lines(init_lines(grammar))
        line = await asyncio.wait_for(self._read_line(), timeout=timeout)
        parse_ready(line, grammar.grammar_id)

    async def run(
        self, grammar: Grammar, point: InputPoint
    ) -> AdapterResult:
        case_id = grammar.case_id(point)
        await self._write_lines((run_line(grammar, point),))
        return parse_result(await self._read_line(), case_id)

    async def _write_lines(self, lines: Iterable[str]) -> None:
        process = self._require_process()
        if process.stdin is None:
            raise RuntimeError("worker stdin is unavailable")
        for line in lines:
            process.stdin.write(line.encode("utf-8") + b"\n")
        await process.stdin.drain()

    async def _read_line(self) -> str:
        process = self._require_process()
        if process.stdout is None:
            raise RuntimeError("worker stdout is unavailable")
        raw = await process.stdout.readline()
        if not raw:
            code = await process.wait()
            stderr = " | ".join(self.stderr_tail)
            raise RuntimeError(
                f"worker exited with {code} before responding"
                + (f": {stderr}" if stderr else "")
            )
        return raw.decode("utf-8", errors="replace").rstrip("\r\n")

    async def _drain_stderr(self) -> None:
        process = self._require_process()
        if process.stderr is None:
            return
        while line := await process.stderr.readline():
            self.stderr_tail.append(
                line.decode("utf-8", errors="replace").rstrip("\r\n")
            )

    def stderr_detail(self) -> str:
        return " | ".join(self.stderr_tail)

    def returncode(self) -> int | None:
        return None if self.process is None else self.process.returncode

    def _require_process(self) -> asyncio.subprocess.Process:
        if self.process is None:
            raise RuntimeError("worker has not started")
        return self.process

    async def close(self) -> None:
        if self.process is None:
            return
        if self.process.returncode is None:
            try:
                await self._write_lines(("STOP",))
                await asyncio.wait_for(self.process.wait(), timeout=5.0)
            except (BrokenPipeError, ConnectionResetError, asyncio.TimeoutError):
                await self.kill()
        await self._finish_stderr()

    async def kill(self) -> None:
        if self.process is None:
            return
        if self.process.returncode is None:
            try:
                os.killpg(self.process.pid, signal.SIGTERM)
            except (ProcessLookupError, PermissionError):
                self.process.terminate()
            try:
                await asyncio.wait_for(self.process.wait(), timeout=2.0)
            except asyncio.TimeoutError:
                try:
                    os.killpg(self.process.pid, signal.SIGKILL)
                except (ProcessLookupError, PermissionError):
                    self.process.kill()
                await self.process.wait()
        await self._finish_stderr()

    async def _finish_stderr(self) -> None:
        if self.stderr_task is not None:
            try:
                await asyncio.wait_for(self.stderr_task, timeout=1.0)
            except asyncio.TimeoutError:
                self.stderr_task.cancel()
            except asyncio.CancelledError:
                pass
            self.stderr_task = None


def _skip_remaining(
    *,
    recorder: CsvRecorder,
    parser: str,
    grammar: Grammar,
    points: Iterable[InputPoint],
    timeout: float,
    status: str,
    detail: str,
) -> None:
    for point in points:
        recorder.record(
            parser=parser,
            grammar=grammar,
            point=point,
            timeout_seconds=timeout,
            status=status,
            error_kind="early_stop",
            detail=detail,
        )


async def run_lane(
    *,
    adapter: AdapterConfig,
    grammar: Grammar,
    timeout: float,
    recorder: CsvRecorder,
    startup_timeout: float | None = None,
) -> None:
    """Run points sequentially; stop this lane after timeout/infrastructure loss."""

    parser = adapter.name
    worker = Worker(adapter)
    points = grammar.points
    try:
        await worker.start(grammar, startup_timeout or timeout)
    except Exception as exception:
        await worker.kill()
        first, *remaining = points
        recorder.record(
            parser=parser,
            grammar=grammar,
            point=first,
            timeout_seconds=timeout,
            status="process_error",
            exit_code=worker.returncode(),
            error_kind=type(exception).__name__,
            detail=str(exception),
        )
        _skip_remaining(
            recorder=recorder,
            parser=parser,
            grammar=grammar,
            points=remaining,
            timeout=timeout,
            status="skipped_after_failure",
            detail="worker failed during grammar initialization",
        )
        print(
            f"[{parser}:{grammar.grammar_id}] initialization failed: {exception}",
            file=sys.stderr,
            flush=True,
        )
        return

    try:
        for index, point in enumerate(points):
            case_id = grammar.case_id(point)
            started = time.monotonic_ns()
            try:
                result = await asyncio.wait_for(
                    worker.run(grammar, point), timeout=timeout
                )
                wall_elapsed_ns = time.monotonic_ns() - started
            except asyncio.TimeoutError:
                wall_elapsed_ns = time.monotonic_ns() - started
                await worker.kill()
                recorder.record(
                    parser=parser,
                    grammar=grammar,
                    point=point,
                    timeout_seconds=timeout,
                    status="timeout",
                    wall_elapsed_ns=wall_elapsed_ns,
                    error_kind="timeout",
                    detail=f"no RESULT within {timeout:g} seconds",
                )
                _skip_remaining(
                    recorder=recorder,
                    parser=parser,
                    grammar=grammar,
                    points=points[index + 1 :],
                    timeout=timeout,
                    status="skipped_after_timeout",
                    detail=f"earlier input {case_id} timed out",
                )
                print(f"[{parser}:{grammar.grammar_id}] timeout at {case_id}")
                return
            except Exception as exception:
                wall_elapsed_ns = time.monotonic_ns() - started
                await worker.kill()
                detail = str(exception)
                stderr = worker.stderr_detail()
                if stderr:
                    detail = f"{detail}; stderr: {stderr}"
                recorder.record(
                    parser=parser,
                    grammar=grammar,
                    point=point,
                    timeout_seconds=timeout,
                    status="process_error",
                    wall_elapsed_ns=wall_elapsed_ns,
                    exit_code=worker.returncode(),
                    error_kind=type(exception).__name__,
                    detail=detail,
                )
                _skip_remaining(
                    recorder=recorder,
                    parser=parser,
                    grammar=grammar,
                    points=points[index + 1 :],
                    timeout=timeout,
                    status="skipped_after_failure",
                    detail=f"worker failed at {case_id}",
                )
                print(
                    f"[{parser}:{grammar.grammar_id}] failed at {case_id}: "
                    f"{exception}",
                    file=sys.stderr,
                    flush=True,
                )
                return
            recorder.record(
                parser=parser,
                grammar=grammar,
                point=point,
                timeout_seconds=timeout,
                status="ok",
                outcome=result.outcome,
                accepted=result.accepted,
                ambiguity=result.ambiguity,
                tree_present=result.tree_present,
                elapsed_ns=result.elapsed_ns,
                wall_elapsed_ns=wall_elapsed_ns,
                exit_code=worker.returncode(),
                error_kind=result.error_kind,
                detail=result.detail,
                metrics=result.metrics,
            )
            print(
                f"[{parser}:{grammar.grammar_id}] {case_id}: "
                f"{result.outcome}, {result.elapsed_ns / 1_000_000:.3f} ms",
                flush=True,
            )
    finally:
        await worker.close()


async def run_all_lanes(
    *,
    adapters: dict[str, AdapterConfig],
    grammars: tuple[Grammar, ...],
    parsers: tuple[str, ...],
    timeout: float,
    jobs: int,
    recorder: CsvRecorder,
) -> None:
    semaphore = asyncio.Semaphore(jobs)

    async def limited(adapter: AdapterConfig, grammar: Grammar) -> None:
        async with semaphore:
            await run_lane(
                adapter=adapter,
                grammar=grammar,
                timeout=timeout,
                recorder=recorder,
            )

    lanes = [
        limited(adapters[parser], grammar)
        for grammar in grammars
        for parser in parsers
        if parser in grammar.supported_parsers
    ]
    if not lanes:
        raise ValueError("the selected suites and parsers produce no lanes")
    await asyncio.gather(*lanes)


def resolve_suites(requested: list[str] | None) -> tuple[str, ...]:
    if not requested:
        return DEFAULT_SUITES
    if "all" in requested:
        return suites()
    return tuple(dict.fromkeys(requested))


def resolve_parsers(requested: list[str] | None) -> tuple[str, ...]:
    return tuple(dict.fromkeys(requested or PARSERS))


def filter_grammars(
    grammars: tuple[Grammar, ...], requested: list[str] | None
) -> tuple[Grammar, ...]:
    if not requested:
        return grammars
    selected: list[Grammar] = []
    for grammar_id in dict.fromkeys(requested):
        matches = [
            grammar for grammar in grammars if grammar.grammar_id == grammar_id
        ]
        if not matches:
            available = ", ".join(grammar.grammar_id for grammar in grammars)
            raise ValueError(
                f"unknown grammar {grammar_id!r} in selected suites; "
                f"available: {available}"
            )
        if len(matches) > 1:
            suites_with_id = ", ".join(grammar.suite for grammar in matches)
            raise ValueError(
                f"grammar ID {grammar_id!r} is ambiguous across selected "
                f"suites: {suites_with_id}"
            )
        selected.append(matches[0])
    return tuple(selected)


def default_output_directory() -> Path:
    run_id = datetime.now(UTC).strftime("%Y%m%dT%H%M%S.%fZ")
    return Path(__file__).with_name("results") / run_id


def parse_arguments(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Run each selected parser/input exactly once. Inputs are sequential "
            "within a parser/grammar lane and lanes may run concurrently."
        )
    )
    parser.add_argument(
        "--suite",
        action="append",
        choices=(*suites(), "all"),
        help="suite to run; repeatable (default: earley and classical)",
    )
    parser.add_argument(
        "--parser",
        dest="parsers",
        action="append",
        choices=PARSERS,
        help="parser adapter to run; repeatable (default: all)",
    )
    parser.add_argument(
        "--grammar",
        action="append",
        help="grammar ID within the selected suites; repeatable",
    )
    parser.add_argument(
        "--timeout",
        type=float,
        default=60.0,
        help="seconds allowed for each input (default: 60)",
    )
    parser.add_argument(
        "--jobs",
        type=int,
        default=1,
        help="maximum concurrent parser/grammar lanes (default: 1)",
    )
    parser.add_argument(
        "--output",
        type=Path,
        help="new result directory (default: timestamp under benchmarking/results)",
    )
    parser.add_argument(
        "--config",
        type=Path,
        default=DEFAULT_CONFIG,
        help="adapter command configuration",
    )
    parser.add_argument(
        "--no-build",
        action="store_true",
        help="use already-built adapters",
    )
    parser.add_argument(
        "--list",
        action="store_true",
        help="list manifest entries and exit",
    )
    arguments = parser.parse_args(argv)
    if arguments.timeout <= 0:
        parser.error("--timeout must be positive")
    if arguments.jobs <= 0:
        parser.error("--jobs must be positive")
    return arguments


def list_manifest() -> None:
    for grammar in GRAMMARS:
        sizes = ", ".join(
            f"{point.label}:{len(point.tokens)}" for point in grammar.points
        )
        print(
            f"{grammar.suite}/{grammar.grammar_id}\t"
            f"parsers={','.join(grammar.supported_parsers)}\t"
            f"inputs={sizes}"
        )


def main(argv: list[str] | None = None) -> int:
    arguments = parse_arguments(argv)
    if arguments.list:
        list_manifest()
        return 0

    selected_suites = resolve_suites(arguments.suite)
    selected_parsers = resolve_parsers(arguments.parsers)
    grammars = filter_grammars(
        select_grammars(selected_suites), arguments.grammar
    )
    adapters = load_adapter_config(arguments.config.resolve())

    output_directory = (
        arguments.output.resolve()
        if arguments.output is not None
        else default_output_directory().resolve()
    )
    if output_directory.exists() and any(output_directory.iterdir()):
        raise FileExistsError(
            f"refusing to overwrite nonempty result directory: {output_directory}"
        )
    output_directory.mkdir(parents=True, exist_ok=True)
    run_id = output_directory.name
    metadata = collect_metadata(
        run_id=run_id,
        arguments=arguments,
        adapters=adapters,
        selected_parsers=selected_parsers,
        selected_suites=selected_suites,
        grammars=grammars,
    )
    metadata_path = output_directory / "metadata.json"
    write_metadata(metadata_path, metadata)

    recorder: CsvRecorder | None = None
    try:
        if not arguments.no_build:
            for parser_name in selected_parsers:
                run_build(adapters[parser_name], output_directory)
        recorder = CsvRecorder(output_directory, run_id)
        metadata["state"] = "running"
        write_metadata(metadata_path, metadata)
        asyncio.run(
            run_all_lanes(
                adapters=adapters,
                grammars=grammars,
                parsers=selected_parsers,
                timeout=arguments.timeout,
                jobs=arguments.jobs,
                recorder=recorder,
            )
        )
    except KeyboardInterrupt:
        metadata["state"] = "interrupted"
        metadata["error"] = "KeyboardInterrupt"
        return_code = 130
    except Exception as exception:
        metadata["state"] = "failed"
        metadata["error"] = f"{type(exception).__name__}: {exception}"
        print(metadata["error"], file=sys.stderr)
        return_code = 1
    else:
        metadata["state"] = "complete"
        return_code = 0
    finally:
        if recorder is not None:
            recorder.close()
        metadata["finished_at_utc"] = datetime.now(UTC).isoformat()
        write_metadata(metadata_path, metadata)

    print(f"results: {output_directory}", flush=True)
    return return_code


if __name__ == "__main__":
    raise SystemExit(main())
