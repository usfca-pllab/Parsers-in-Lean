"""Canonical grammars and input families used by all benchmark adapters.

The adapters receive numeric symbol identifiers over the line protocol.  Human
readable names live here so that grammar and input definitions have one source
of truth.
"""

from __future__ import annotations

from dataclasses import dataclass
from hashlib import sha256
from typing import Iterable, Literal

PARSERS = ("lean", "earley", "costar")
DEFAULT_SUITES = ("earley", "classical")


@dataclass(frozen=True)
class Symbol:
    kind: Literal["terminal", "nonterminal"]
    name: str


def T(name: str) -> Symbol:
    return Symbol("terminal", name)


def N(name: str) -> Symbol:
    return Symbol("nonterminal", name)


@dataclass(frozen=True)
class Rule:
    lhs: str
    rhs: tuple[Symbol, ...]


@dataclass(frozen=True)
class InputPoint:
    label: str
    parameter_name: str
    parameter_value: int
    tokens: tuple[str, ...]


@dataclass(frozen=True)
class Grammar:
    suite: str
    grammar_id: str
    description: str
    terminals: tuple[str, ...]
    nonterminals: tuple[str, ...]
    start: str
    rules: tuple[Rule, ...]
    points: tuple[InputPoint, ...]
    supported_parsers: tuple[str, ...] = PARSERS

    @property
    def start_id(self) -> int:
        return self.nonterminals.index(self.start)

    def terminal_id(self, terminal: str) -> int:
        return self.terminals.index(terminal)

    def nonterminal_id(self, nonterminal: str) -> int:
        return self.nonterminals.index(nonterminal)

    def case_id(self, point: InputPoint) -> str:
        return f"{self.suite}.{self.grammar_id}.{point.label}"

    def input_hash(self, point: InputPoint) -> str:
        encoded = "\0".join(point.tokens).encode("utf-8")
        return sha256(encoded).hexdigest()


def _earley_points() -> tuple[InputPoint, ...]:
    return tuple(
        InputPoint(f"n{n:03d}", "n", n, ("a",) * n)
        for n in range(1, 66, 2)
    )


def _sizes(
    parameter_name: str,
    values: Iterable[tuple[str, int]],
    make_tokens,
) -> tuple[InputPoint, ...]:
    return tuple(
        InputPoint(label, parameter_name, value, tuple(make_tokens(value)))
        for label, value in values
    )


EARLEY_POINTS = _earley_points()

GRAMMARS: tuple[Grammar, ...] = (
    Grammar(
        suite="earley",
        grammar_id="cfg1",
        description="Ambiguous binary concatenation: S → S S | a",
        terminals=("a",),
        nonterminals=("S",),
        start="S",
        rules=(
            Rule("S", (N("S"), N("S"))),
            Rule("S", (T("a"),)),
        ),
        points=EARLEY_POINTS,
    ),
    Grammar(
        suite="earley",
        grammar_id="cfg2",
        description="Right-recursive: S → a S | a",
        terminals=("a",),
        nonterminals=("S",),
        start="S",
        rules=(
            Rule("S", (T("a"), N("S"))),
            Rule("S", (T("a"),)),
        ),
        points=EARLEY_POINTS,
    ),
    Grammar(
        suite="earley",
        grammar_id="cfg3",
        description="Odd nested language: S → a S a | a",
        terminals=("a",),
        nonterminals=("S",),
        start="S",
        rules=(
            Rule("S", (T("a"), N("S"), T("a"))),
            Rule("S", (T("a"),)),
        ),
        points=EARLEY_POINTS,
    ),
    Grammar(
        suite="earley",
        grammar_id="cfg4",
        description="Left-recursive linear: S → S a | a",
        terminals=("a",),
        nonterminals=("S",),
        start="S",
        rules=(
            Rule("S", (N("S"), T("a"))),
            Rule("S", (T("a"),)),
        ),
        points=EARLEY_POINTS,
    ),
    Grammar(
        suite="earley",
        grammar_id="cfg5",
        description="Left-recursive ambiguity through X → Y | Z",
        terminals=("a",),
        nonterminals=("S", "X", "Y", "Z"),
        start="S",
        rules=(
            Rule("S", (N("S"), N("X"))),
            Rule("S", (T("a"),)),
            Rule("X", (N("Y"),)),
            Rule("X", (N("Z"),)),
            Rule("Y", (T("a"),)),
            Rule("Z", (T("a"),)),
        ),
        points=EARLEY_POINTS,
    ),
    Grammar(
        suite="classical",
        grammar_id="R1",
        description="Regular a* b",
        terminals=("a", "b"),
        nonterminals=("S",),
        start="S",
        rules=(
            Rule("S", (T("a"), N("S"))),
            Rule("S", (T("b"),)),
        ),
        points=_sizes(
            "n",
            (("small", 4), ("medium", 32), ("large", 256)),
            lambda n: ("a",) * n + ("b",),
        ),
    ),
    Grammar(
        suite="classical",
        grammar_id="R2",
        description="Regular (a b)* c",
        terminals=("a", "b", "c"),
        nonterminals=("S", "A"),
        start="S",
        rules=(
            Rule("S", (T("a"), N("A"))),
            Rule("S", (T("c"),)),
            Rule("A", (T("b"), N("S"))),
        ),
        points=_sizes(
            "n",
            (("small", 3), ("medium", 32), ("large", 256)),
            lambda n: ("a", "b") * n + ("c",),
        ),
    ),
    Grammar(
        suite="classical",
        grammar_id="P1",
        description="Context-free a^n b^n",
        terminals=("a", "b"),
        nonterminals=("S", "T"),
        start="S",
        rules=(
            Rule("S", (T("a"), N("T"))),
            Rule("T", (N("S"), T("b"))),
            Rule("T", (T("b"),)),
        ),
        points=_sizes(
            "n",
            (("small", 4), ("medium", 32), ("large", 256)),
            lambda n: ("a",) * n + ("b",) * n,
        ),
    ),
    Grammar(
        suite="classical",
        grammar_id="P2",
        description="Predictive, semicolon-terminated identifier list",
        terminals=("ID", "COMMA", "SEMI"),
        nonterminals=("List", "Rest"),
        start="List",
        rules=(
            Rule("List", (T("ID"), N("Rest"))),
            Rule("Rest", (T("COMMA"), T("ID"), N("Rest"))),
            Rule("Rest", (T("SEMI"),)),
        ),
        points=_sizes(
            "items",
            (("small", 4), ("medium", 32), ("large", 256)),
            lambda n: ("ID",) + ("COMMA", "ID") * (n - 1) + ("SEMI",),
        ),
    ),
    Grammar(
        suite="classical",
        grammar_id="C1",
        description="Odd palindromes; selected family a^n b a^n",
        terminals=("a", "b"),
        nonterminals=("P",),
        start="P",
        rules=(
            Rule("P", (T("a"), N("P"), T("a"))),
            Rule("P", (T("b"), N("P"), T("b"))),
            Rule("P", (T("a"),)),
            Rule("P", (T("b"),)),
        ),
        points=_sizes(
            "n",
            (("small", 3), ("medium", 31), ("large", 255)),
            lambda n: ("a",) * n + ("b",) + ("a",) * n,
        ),
    ),
    Grammar(
        suite="classical",
        grammar_id="A1",
        description="Dangling-else grammar on fully matched inputs",
        terminals=("IF", "COND", "THEN", "ELSE", "OTHER"),
        nonterminals=("Stmt",),
        start="Stmt",
        rules=(
            Rule("Stmt", (T("IF"), T("COND"), T("THEN"), N("Stmt"))),
            Rule(
                "Stmt",
                (
                    T("IF"),
                    T("COND"),
                    T("THEN"),
                    N("Stmt"),
                    T("ELSE"),
                    N("Stmt"),
                ),
            ),
            Rule("Stmt", (T("OTHER"),)),
        ),
        points=_sizes(
            "nesting",
            (("small", 2), ("medium", 8), ("large", 32)),
            lambda n: ("IF", "COND", "THEN") * n
            + ("OTHER",)
            + ("ELSE", "OTHER") * n,
        ),
    ),
    Grammar(
        suite="smoke",
        grammar_id="binary-epsilon",
        description="Nullable binary grammar: S → a S S | b S S | ε",
        terminals=("a", "b"),
        nonterminals=("S",),
        start="S",
        rules=(
            Rule("S", (T("a"), N("S"), N("S"))),
            Rule("S", (T("b"), N("S"), N("S"))),
            Rule("S", ()),
        ),
        points=(
            InputPoint("ab3", "pairs", 3, tuple("ababab")),
        ),
        supported_parsers=("lean",),
    ),
    Grammar(
        suite="smoke",
        grammar_id="ambiguous-concat",
        description="Classic ambiguous grammar: S → S S | a | b",
        terminals=("a", "b"),
        nonterminals=("S",),
        start="S",
        rules=(
            Rule("S", (N("S"), N("S"))),
            Rule("S", (T("a"),)),
            Rule("S", (T("b"),)),
        ),
        points=(
            InputPoint("ab3", "pairs", 3, tuple("ababab")),
        ),
        supported_parsers=("lean",),
    ),
)


def suites() -> tuple[str, ...]:
    return tuple(dict.fromkeys(grammar.suite for grammar in GRAMMARS))


def select_grammars(selected_suites: Iterable[str]) -> tuple[Grammar, ...]:
    wanted = set(selected_suites)
    return tuple(grammar for grammar in GRAMMARS if grammar.suite in wanted)


def validate_manifest(grammars: Iterable[Grammar] = GRAMMARS) -> None:
    grammar_keys: set[tuple[str, str]] = set()
    case_ids: set[str] = set()
    for grammar in grammars:
        key = (grammar.suite, grammar.grammar_id)
        if key in grammar_keys:
            raise ValueError(f"duplicate grammar key: {key}")
        grammar_keys.add(key)
        for field_name, value in (
            ("suite", grammar.suite),
            ("grammar_id", grammar.grammar_id),
        ):
            if not value or any(c in value for c in "\t\r\n"):
                raise ValueError(f"invalid {field_name}: {value!r}")
        if len(set(grammar.terminals)) != len(grammar.terminals):
            raise ValueError(f"{key}: duplicate terminal")
        if len(set(grammar.nonterminals)) != len(grammar.nonterminals):
            raise ValueError(f"{key}: duplicate nonterminal")
        if not grammar.nonterminals or grammar.start not in grammar.nonterminals:
            raise ValueError(f"{key}: invalid start nonterminal")
        if not grammar.rules:
            raise ValueError(f"{key}: grammar has no rules")
        if not grammar.points:
            raise ValueError(f"{key}: grammar has no input points")
        unknown_parsers = set(grammar.supported_parsers) - set(PARSERS)
        if unknown_parsers:
            raise ValueError(f"{key}: unknown parsers {sorted(unknown_parsers)}")
        for rule in grammar.rules:
            if rule.lhs not in grammar.nonterminals:
                raise ValueError(f"{key}: undeclared lhs {rule.lhs!r}")
            for symbol in rule.rhs:
                declared = (
                    symbol.name in grammar.terminals
                    if symbol.kind == "terminal"
                    else symbol.name in grammar.nonterminals
                )
                if not declared:
                    raise ValueError(f"{key}: undeclared symbol {symbol}")
        point_labels: set[str] = set()
        for point in grammar.points:
            if point.label in point_labels:
                raise ValueError(f"{key}: duplicate point {point.label!r}")
            point_labels.add(point.label)
            if not point.tokens and not any(not rule.rhs for rule in grammar.rules):
                raise ValueError(f"{key}: empty input for epsilon-free grammar")
            undeclared = set(point.tokens) - set(grammar.terminals)
            if undeclared:
                raise ValueError(f"{key}: input uses {sorted(undeclared)}")
            case_id = grammar.case_id(point)
            if case_id in case_ids:
                raise ValueError(f"duplicate case id: {case_id}")
            case_ids.add(case_id)


validate_manifest()
