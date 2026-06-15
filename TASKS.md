# TASKS

This file tracks only the active path to the overall goal: remove the remaining
proof assumptions from the verified memoizing parser-combinator core while
preserving exact-counter memoization.

Detailed proof history, completed helper layers, old tactical TODOs, and audit
snapshots live in `TASKS-trace.md`.  Statement refinements live in
`refinements.md`.  Broader design ideas live in `future-work.md` and
`memo-strategies.md`.

## Definition Of Done

- [ ] No active `axiom` or `sorry` remains in:
  `ParserCombinators/Gen.lean`, `ParserCombinators/Lemmas.lean`,
  `ParserCombinators/Memoized.lean`, or `ParserCombinators/CFG.lean`.
- [ ] `gen_sound`, `gen_complete`, and `gen_correct` build against the real
  exact-counter `memoize` implementation.
- [ ] `memoize` still reuses exact-counter cache entries; no proof-only
  recomputation path replaces memoization.
- [ ] `lake build` succeeds.
- [ ] The final audit commands below report no live dependencies on retired
  axiom names.

## Active Work

### 1. Remove The Bind/Traverse Axiom

Live assumption:

- `ParserCombinators/Lemmas.lean`: `mem_runParser_bind_iff_eq_bind_mem_runParser`

Live dependency:

- `ParserCombinators/Gen.lean`: `runParser_traverse_complete_cons`

Required work:

- [ ] Replace the fresh-state traversal completeness path with a lower-state or
  exact-prefix traversal theorem that threads the memo state produced by the
  head parser and earlier traversal actions.
- [ ] Refactor the remaining Gen traversal consumer to use the state-threaded
  theorem.
- [ ] Delete `mem_runParser_bind_iff_eq_bind_mem_runParser`.

### 2. Remove The Sup/Choice Axiom

Live assumption:

- `ParserCombinators/Lemmas.lean`: `runParser_sup_eq_sup_runParser`

Live dependency:

- `ParserCombinators/Gen.lean`: `complete_of_sup_right`

Required work:

- [ ] Replace the fresh-state right-choice completeness path with an after-left
  or lower-state theorem that accounts for the memo state produced by the left
  branch.
- [ ] Refactor generated-rule fold completeness to use the state-threaded
  choice theorem.
- [ ] Delete `runParser_sup_eq_sup_runParser`.

## Next Proof Step

- [x] Finish the exact-counter cache-completeness invariant for generated
  parsers:
  `positionMap_complete`, whole-memo union preservation, and the
  `memoizeStep` compute branch.
- [ ] Thread that invariant through lower-state generated-parser completeness,
  then use it to discharge the bind/traverse and sup/choice dependencies above.

## Final Audit

```sh
rg -n "\\baxiom\\b|\\bsorry\\b" ParserCombinators/Gen.lean ParserCombinators/Lemmas.lean ParserCombinators/Memoized.lean ParserCombinators/CFG.lean
rg -n "\\b(runParser_sup_eq_sup_runParser|mem_runParser_bind_iff_eq_bind_mem_runParser)\\b" ParserCombinators/Gen.lean ParserCombinators/Lemmas.lean
lake build
```

Historical notes or explicitly retired `old_*` statement records are not active
blockers, but no live proof should depend on retired axiom names.
