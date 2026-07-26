"""Persistent TSV protocol shared by the benchmark runner and adapters."""

from __future__ import annotations

from dataclasses import dataclass

from benchmarking.manifest import Grammar, InputPoint


class ProtocolError(RuntimeError):
    pass


@dataclass(frozen=True)
class AdapterResult:
    case_id: str
    elapsed_ns: int
    outcome: str
    accepted: str
    ambiguity: str
    tree_present: str
    metrics: dict[str, str]
    error_kind: str
    detail: str


def _require_field(value: str, name: str) -> str:
    if not value or any(character in value for character in "\t\r\n"):
        raise ProtocolError(f"{name} is not a valid TSV protocol field")
    return value


def init_lines(grammar: Grammar) -> tuple[str, ...]:
    _require_field(grammar.grammar_id, "grammar id")
    lines = [
        "\t".join(
            (
                "INIT",
                grammar.grammar_id,
                str(grammar.start_id),
                str(len(grammar.nonterminals)),
                str(len(grammar.terminals)),
                str(len(grammar.rules)),
            )
        )
    ]
    for rule in grammar.rules:
        encoded_symbols: list[str] = []
        for symbol in rule.rhs:
            if symbol.kind == "terminal":
                encoded_symbols.append(f"T:{grammar.terminal_id(symbol.name)}")
            else:
                encoded_symbols.append(f"N:{grammar.nonterminal_id(symbol.name)}")
        rhs = ",".join(encoded_symbols) if encoded_symbols else "-"
        lines.append(
            f"RULE\t{grammar.nonterminal_id(rule.lhs)}\t{rhs}"
        )
    lines.append("END")
    return tuple(lines)


def run_line(grammar: Grammar, point: InputPoint) -> str:
    case_id = _require_field(grammar.case_id(point), "case id")
    encoded = ",".join(str(grammar.terminal_id(token)) for token in point.tokens)
    return f"RUN\t{case_id}\t{encoded or '-'}"


def parse_ready(line: str, grammar_id: str) -> None:
    expected = f"READY\t{grammar_id}"
    if line != expected:
        raise ProtocolError(f"expected {expected!r}, received {line!r}")


def parse_metrics(field: str) -> dict[str, str]:
    if field == "-":
        return {}
    result: dict[str, str] = {}
    for item in field.split(";"):
        if "=" not in item:
            raise ProtocolError(f"invalid metric entry: {item!r}")
        key, value = item.split("=", 1)
        if (
            not key
            or not value
            or any(c in key for c in "=;\t\r\n")
            or any(c in value for c in ";\t\r\n")
        ):
            raise ProtocolError(f"invalid metric entry: {item!r}")
        if key in result:
            raise ProtocolError(f"duplicate metric: {key!r}")
        result[key] = value
    return result


def parse_result(line: str, expected_case_id: str) -> AdapterResult:
    fields = line.split("\t", 9)
    if len(fields) != 10 or fields[0] != "RESULT":
        raise ProtocolError(f"invalid result line: {line!r}")
    _, case_id, elapsed, outcome, accepted, ambiguity, tree, metrics, error, detail = (
        fields
    )
    if case_id != expected_case_id:
        raise ProtocolError(
            f"expected result for {expected_case_id!r}, received {case_id!r}"
        )
    try:
        elapsed_ns = int(elapsed)
    except ValueError as exception:
        raise ProtocolError(f"invalid elapsed_ns: {elapsed!r}") from exception
    if elapsed_ns < 0:
        raise ProtocolError("elapsed_ns must be nonnegative")
    for name, value in (
        ("outcome", outcome),
        ("accepted", accepted),
        ("ambiguity", ambiguity),
        ("tree_present", tree),
    ):
        _require_field(value, name)
    allowed = {
        "outcome": {"accept", "reject", "ambiguous", "parser_error"},
        "accepted": {"true", "false", "unknown"},
        "ambiguity": {"unique", "ambiguous", "unknown"},
        "tree_present": {"true", "false", "unknown"},
    }
    for name, value in (
        ("outcome", outcome),
        ("accepted", accepted),
        ("ambiguity", ambiguity),
        ("tree_present", tree),
    ):
        if value not in allowed[name]:
            raise ProtocolError(
                f"invalid {name} {value!r}; expected one of "
                f"{sorted(allowed[name])}"
            )
    if error != "-":
        _require_field(error, "error_kind")
    if detail != "-":
        _require_field(detail, "detail")
    return AdapterResult(
        case_id=case_id,
        elapsed_ns=elapsed_ns,
        outcome=outcome,
        accepted=accepted,
        ambiguity=ambiguity,
        tree_present=tree,
        metrics=parse_metrics(metrics),
        error_kind="" if error == "-" else error,
        detail="" if detail == "-" else detail,
    )
