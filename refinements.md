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

## `Memoized.memoize` Completeness Fuel And Cache

Original behavior:

```lean
match positionMap[pos]? with
| some cachedResult => pure cachedResult
| none =>
  let results ← lower (g (memoize (counter.dec t ((← read).size - pos)) g) t) pos
  modifyGet ...
```

Why this is not enough for generated-parser completeness:

- The recursive budget `input.size - pos` can cut off the final nullable/base
  call.  For a grammar such as `S -> term a, nonterm S | []`, parsing `[a]`
  can reach the recursive `S` at end position with zero fuel before trying the
  epsilon rule.
- The cache was keyed only by `(tag, position)`, not by fuel.  A lower-fuel
  call could cache an incomplete result for a position, and a later higher-fuel
  call would return that stale approximation without recomputing.

Intermediate replacement:

```lean
let results ← lower (g (memoize (counter.dec t ((← read).size - pos + 1)) g) t) pos
modifyGet $ fun memo =>
  let positionMap := memo.getD t ⊥
  let results := results ⊔ positionMap.getD pos ⊥
  (results, memo.insert t $ positionMap.insert pos results)
```

The extra budget unit admits the final nullable/base invocation after consuming
the remaining input.  Removing the cache short-circuit makes cache entries
monotone approximations: each call recomputes at its current budget and unions
new results with any existing cached results.  This is the operational
precondition used by the temporary `Gen.gen_complete_exists` axiom's proof
outline.

Final replacement:

```lean
let key : MemoEntryKey τ := (Counter.toKey counter, pos)
let positionMap := (← get).getD t ⊥
match positionMap[key]? with
| some cachedResult => pure cachedResult
| none =>
    let input ← read
    let results ← lower (g (memoize (counter.dec t (input.size - pos + 1)) g) t) pos
    modifyGet $ fun memo =>
      let positionMap := memo.getD t ⊥
      (results, memo.insert t $ positionMap.insert key results)
```

The final design keeps the `+1` budget refinement and restores real cache hits.
The memo table now keys entries by the exact executable counter key together
with the input position.  A lower-counter result can no longer be reused for a
higher-counter call at the same tag and position, so cache hits are coherent
with the bounded recursive semantics while preserving memoization.
