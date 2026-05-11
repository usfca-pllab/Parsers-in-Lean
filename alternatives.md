# Alternatives

This file records proof-design routes that were considered but not chosen for
the current implementation path.

## Proof-Carrying Generated Parsers

Alternative route:

Instead of keeping `Gen.gen'` and `Gen.gen` as parsers that return plain
`ParseTree cfg` values, define a typed generator whose result type carries the
validity and root proofs directly.  A representative target type would be:

```lean
ParserM (tag := tag cfg) α List
  {tree : ParseTree cfg // tree.Valid ∧ tree.root = Symbol.nonterm n}
```

The implementation would then build proof-carrying leaves and nodes as parser
results, and an erasure theorem would relate the typed generator back to the
current plain parse-tree generator.

Why this was not chosen now:

- The current parser combinator stack already works over plain result values,
  and `gen_sound` now supplies validity/root information externally.
- Carrying dependent result types through `List.traverse`, `⊔`, `memoize`, and
  recursive nonterminal calls would add substantial type-level plumbing before
  improving the main proof obligations.
- The external-proof route keeps the executable parser shape simple and lets
  soundness, boundedness, and later completeness be proved as separate
  semantic theorems.

Current route:

Keep generated parsers untyped:

```lean
gen (μ := List) cfg n : ParserM (tag := tag cfg) α List (ParseTree cfg)
```

Attach correctness externally through theorems such as:

```lean
theorem gen_sound (cfg : @CFG α ν) n input :
  sound cfg n (gen (μ := List) cfg n) input
```

Future completeness work should follow the same style by proving
`gen_complete`, then optionally combining soundness and completeness in a
public `gen_correct` theorem.
