# Grammars from the Isabelle Earley parser

Source: `related-work/Earley_Parser/Examples.thy`.

The first five grammars are active Isabelle definitions. They share the symbol
datatype `a | S | X | Y | Z`, use `S` as the start symbol, and are formally
proved epsilon-free in the source. Isabelle infers nonterminals as symbols
that occur on the left-hand side of a rule.

## `cfg1`: cubic ambiguous grammar

The source labels this as an \(O(n^3)\) ambiguous grammar.

```text
S -> S S
S -> a
```

- Isabelle definitions: `rules1`, `cfg1`
- Nonterminal: `S`
- Terminal: `a`
- Language: one or more `a` tokens
- Ambiguity: a string of \(n\) tokens has the different binary
  parenthesizations of `a^n`.

## `cfg2`: right-recursive grammar

This occurs under the source heading “\(O(n^2)\) unambiguous or bounded
ambiguity.”

```text
S -> a S
S -> a
```

- Isabelle definitions: `rules2`, `cfg2`
- Nonterminal: `S`
- Terminal: `a`
- Language: one or more `a` tokens

## `cfg3`: odd-length nested grammar

This also occurs under “\(O(n^2)\) unambiguous or bounded ambiguity.”

```text
S -> a S a
S -> a
```

- Isabelle definitions: `rules3`, `cfg3`
- Nonterminal: `S`
- Terminal: `a`
- Language: an odd, positive number of `a` tokens

## `cfg4`: left-recursive linear grammar

The source labels this as an \(O(n)\), bounded-state, non-right-recursive
LR(k) grammar.

```text
S -> S a
S -> a
```

- Isabelle definitions: `rules4`, `cfg4`
- Nonterminal: `S`
- Terminal: `a`
- Language: one or more `a` tokens

## `cfg5`: ambiguity through equivalent nonterminals

```text
S -> S X
S -> a
X -> Y
X -> Z
Y -> a
Z -> a
```

- Isabelle definitions: `rules5`, `cfg5`
- Nonterminals: `S`, `X`, `Y`, `Z`
- Terminal: `a`
- Language: one or more `a` tokens
- Ambiguity: every derived `X` can produce `a` through either `Y` or `Z`.

## Shared active benchmark input

All five active grammars are evaluated on the same definition, `inp`:

```text
a^65
```

That is an Isabelle list containing 65 copies of terminal `a`.

For testing these grammars, use repetitions of the symbol `a` up to this limit.
