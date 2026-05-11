# Proof Refinements

This file records places where an initial helper statement was too broad or
misaligned with the proof, and the replacement direction used in the
implementation.

## `Gen.runParser_mem_bounds`

Original statement:

```lean
lemma runParser_mem_bounds
  {cfg : @CFG α ν}
  {p : ParserM (tag := tag cfg) α List (ParseTree cfg)}
  {input : Array α} {start end_ : ℕ}
  (h : end_ ∈ (runParser (tag := tag cfg) p input start).1)
  : start ≤ end_ ∧ end_ ≤ input.size
```

Why this is not sound:

The statement quantifies over arbitrary `ParserM` values.  A lifted primitive
parser can produce a result map with any key chosen by the primitive parser,
independent of the input bounds.  Even `pure`-like behavior returns at `start`;
if `start > input.size`, the conclusion `end_ ≤ input.size` is false for
`end_ = start`.  So the bounds property is not a semantic invariant of all
parsers.

Potential replacements:

- Use a parser-specific invariant:

```lean
abbrev result_bounded (cfg : @CFG α ν)
  (p : ParserM (tag := tag cfg) α List (ParseTree cfg)) (input : Array α)
  :=
  ∀ start end_ : ℕ,
  start ≤ input.size →
  ∀ tree, tree ∈ (runParser p input start).1.getD end_ [] →
    start ≤ end_ ∧ end_ ≤ input.size
```

- Prove `result_bounded` for the parser constructors used by `gen_sound`:
  terminal parsers, failure, joins, and `List.traverse` over bounded child
  parsers.

- Strengthen the memoization induction predicate used by `gen_sound` so every
  recursive parser supplies both `sound` and `result_bounded`.

Final replacement:

The original `runParser_mem_bounds` helper was removed.  The proof now uses
`result_bounded` as the parser-specific invariant:

- `terminal'_bounded` proves boundedness for generated terminal parsers.
- `failure_bounded` proves boundedness for failure.
- `bounded_of_sup_bounded` proves boundedness is preserved by parser joins.
- `runParser_traverse_origin_bounded` refines traversal origins with the
  bounds of the child parser that produced each subtree.
- `runParser_traverse_result_bounds` proves the final end position of a
  traversal result is bounded when each child parser is bounded.

`gen_sound` now strengthens its memoization induction predicate from only
`sound` to:

```lean
∀ n input, sound cfg n (parser n) input ∧
  result_bounded cfg (parser n) input
```

The soundness proof uses the boundedness half of recursive calls when checking
recursive nonterminal children, so it no longer depends on a global
all-parsers bounds theorem.
