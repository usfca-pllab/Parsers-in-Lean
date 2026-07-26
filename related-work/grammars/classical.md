# Classical grammar benchmark suite

This suite contains small, diagnostic context-free grammars. Every grammar is
epsilon-free and has neither direct nor indirect left recursion. The selected
benchmark inputs have exactly one parse, including those selected for a grammar
that is ambiguous on other inputs.

Terminals are written in lowercase or as uppercase token names. Nonterminals
start with an uppercase letter. `x^n` means `n` repetitions of token `x`;
it is input-generation notation, not grammar notation.

## Summary

| ID | Class | Grammar property | Selected-input property |
|---|---|---|---|
| R1 | Regular | Right-linear, LL(1) | Unique |
| R2 | Regular | Right-linear, LL(1), two-state cycle | Unique |
| P1 | Context-free | LL(1), non-regular language | Unique |
| P2 | Regular | Predictive terminated list | Unique |
| C1 | Context-free | Palindromes, not LL(1) as written | Unique |
| A1 | Context-free | Ambiguous dangling-else grammar | Unique for fully matched inputs |

## R1: `a* b`

```text
S -> a S
S -> b
```

This is a right-linear LL(1) grammar. The alternatives have disjoint FIRST
sets `{a}` and `{b}`.

Input family:

```text
R1(n) = a^n b
```

| Size | `n` | Token count | Concrete input |
|---|---:|---:|---|
| Small | 4 | 5 | `a a a a b` |
| Medium | 32 | 33 | `a^32 b` |
| Large | 256 | 257 | `a^256 b` |

## R2: `(a b)* c`

```text
S -> a A
S -> c
A -> b S
```

This is another right-linear LL(1) grammar, presented as a two-state
right-recursive cycle. Every recursive step consumes `a b`, so it is not left
recursive.

Input family:

```text
R2(n) = (a b)^n c
```

| Size | `n` | Token count | Concrete input |
|---|---:|---:|---|
| Small | 3 | 7 | `a b a b a b c` |
| Medium | 32 | 65 | `(a b)^32 c` |
| Large | 256 | 513 | `(a b)^256 c` |

## P1: `a^n b^n`

```text
S -> a T
T -> S b
T -> b
```

This is an epsilon-free, left-factored grammar for equal positive runs of
`a` and `b`. It is LL(1): after the initial `a`, `T` selects `S b` on lookahead
`a` and selects `b` on lookahead `b`.

Input family:

```text
P1(n) = a^n b^n, n >= 1
```

| Size | `n` | Token count | Concrete input |
|---|---:|---:|---|
| Small | 4 | 8 | `a a a a b b b b` |
| Medium | 32 | 64 | `a^32 b^32` |
| Large | 256 | 512 | `a^256 b^256` |

## P2: terminated identifier lists

```text
List -> ID Rest
Rest -> COMMA ID Rest
Rest -> SEMI
```

This is an epsilon-free LL(1) list grammar. The explicit `SEMI` terminator
replaces the epsilon production normally used for an optional tail.

Input family:

```text
P2(n) = ID (COMMA ID)^(n-1) SEMI, n >= 1
```

| Size | Items | Token count | Concrete input |
|---|---:|---:|---|
| Small | 4 | 8 | `ID COMMA ID COMMA ID COMMA ID SEMI` |
| Medium | 32 | 64 | `ID (COMMA ID)^31 SEMI` |
| Large | 256 | 512 | `ID (COMMA ID)^255 SEMI` |

## C1: odd palindromes

```text
P -> a P a
P -> b P b
P -> a
P -> b
```

This grammar is epsilon-free and consumes a terminal before every recursive
call. It is not LL(1) as written because two alternatives can begin with `a`
and two can begin with `b`, but every generated string has a unique parse:
the matching outer tokens determine each recursive production and the middle
token determines the base production.

The benchmark family deliberately uses a simple uniquely parsed subset:

```text
C1(n) = a^n b a^n
```

| Size | `n` | Token count | Concrete input |
|---|---:|---:|---|
| Small | 3 | 7 | `a a a b a a a` |
| Medium | 31 | 63 | `a^31 b a^31` |
| Large | 255 | 511 | `a^255 b a^255` |

## A1: dangling `else`

```text
Stmt -> IF COND THEN Stmt
Stmt -> IF COND THEN Stmt ELSE Stmt
Stmt -> OTHER
```

This epsilon-free grammar has no left recursion: each recursive production
consumes `IF COND THEN` before reaching another `Stmt`. The grammar is globally
ambiguous. For example,

```text
IF COND THEN IF COND THEN OTHER ELSE OTHER
```

allows the `ELSE` to attach to either `IF`.

For benchmarks, use fully matched nesting. These inputs have exactly one parse
because every open `IF` has a corresponding `ELSE`, including the outermost
one:

```text
A1(n) = (IF COND THEN)^n OTHER (ELSE OTHER)^n
```

| Size | Nesting | Token count | Concrete input |
|---|---:|---:|---|
| Small | 2 | 11 | `IF COND THEN IF COND THEN OTHER ELSE OTHER ELSE OTHER` |
| Medium | 8 | 41 | `(IF COND THEN)^8 OTHER (ELSE OTHER)^8` |
| Large | 32 | 161 | `(IF COND THEN)^32 OTHER (ELSE OTHER)^32` |

## Benchmarking guidance

- Treat every space-separated terminal name as one token.
- Verify acceptance and parse-tree construction in addition to recording time.
- Record chart-item and pointer counts where the parser exposes them.
- Run rejected inputs separately: failure paths can be substantially cheaper.
- For scaling plots, vary only the repetition parameter within one family.
- A1 tests an ambiguous grammar without making the selected input ambiguous;
  use its shorter unmatched example separately when testing ambiguity handling.

