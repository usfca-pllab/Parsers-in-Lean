# ParserCombinators

Verified parser combinator experiments in Lean 4, focused on memoizing parser
families generated from context-free grammars.

The current core lives in three modules:

- `ParserCombinators/Memoized.lean` defines the deep parser representation
  `ParserM`, result maps keyed by end positions, parser combinators, runners,
  and a terminating `memoize` operator.  Termination is controlled by a finite
  per-tag recursion `Counter` with a well-founded order.
- `ParserCombinators/Gen.lean` translates a `CFG` into a family of memoized
  parsers that produce `ParseTree`s and proves soundness and completeness for
  the executable exact-counter memoizer.
- `ParserCombinators/Lemmas.lean` collects supporting facts about `runParser`
  and the state-aware parser combinators used by the generated-parser proofs.

Supporting modules define context-free grammars and parse trees (`CFG.lean`),
state and utility infrastructure (`MState.lean`, `Util.lean`, `Order.lean`),
plus older/simple parser experiments and examples.

## Verification status

The generated parser in `ParserCombinators/Gen.lean` has checked soundness and
completeness proofs for the executable exact-counter memoizer. Cache entries
are keyed by nonterminal, serialized recursion counter, and start position;
`memo_complete` is the central cache-completeness invariant. The checked core
contains no project `axiom` declarations or `sorry` placeholders.

`ParserCombinators/Example2.lean` is a standalone memoized parser over a finite
terminal datatype whose result type carries grammar-validity and root
certificates. It deliberately does not use `Gen.gen_correct` or claim
completeness or frontier equality. `Basic.lean` and `Example.lean` remain
nonmemoized controls, while `Main.lean` is the executable memoization
comparison.

See [the correctness architecture](docs/memoized-parser-correctness.md) and
[the pruned Lean-axiom frontier](docs/axiom-proof-frontier.md). The separate
[benchmarking guide](benchmarking/README.md) describes the joint Lean, Earley,
and CoStar benchmark runner, grammar suites, CSV results, and plots.

This project uses Lake with Lean `leanprover/lean4:v4.22.0-rc4`, mathlib, and
aesop. Build the library with:

```sh
lake build
```

`Example.lean` is a non-umbrella control and can be elaborated separately:

```sh
lake env lean ParserCombinators/Example.lean
```
