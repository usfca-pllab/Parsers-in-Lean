# ParserCombinators

Verified parser combinator experiments in Lean 4, focused on memoizing parser
families generated from context-free grammars.

The current core lives in three modules:

- `ParserCombinators/Memoized.lean` defines the deep parser representation
  `ParserM`, result maps keyed by end positions, parser combinators, runners,
  and a terminating `memoize` operator.  Termination is controlled by a finite
  per-tag recursion `Counter` with a well-founded order.
- `ParserCombinators/Gen.lean` translates a `CFG` into a family of memoized
  parsers that produce `ParseTree`s.  It also states and partially proves
  soundness and completeness-style properties for generated parsers.
- `ParserCombinators/Lemmas.lean` collects supporting facts about `runParser`
  and parser combinators.  Some central facts are still axiomatized while the
  proof infrastructure is being developed.

Supporting modules define context-free grammars and parse trees (`CFG.lean`),
state and utility infrastructure (`MState.lean`, `Util.lean`, `Order.lean`,
`Range.lean`), plus older/simple parser experiments and examples.

## Development

This project uses Lake with Lean `leanprover/lean4:v4.22.0-rc4`, mathlib, and
aesop.  Build the library with:

```sh
lake build
```

The repository is proof-in-progress: `sorry`, `axiom`, and commented tests in
the core files mark the main unfinished verification work.
