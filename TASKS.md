# TASKS

This file tracks only the active path to the overall goal: remove the remaining
proof assumptions from the verified memoizing parser-combinator core while
preserving exact-counter memoization.

Detailed proof history, completed helper layers, old tactical TODOs, and audit
snapshots live in `TASKS-trace.md`.  Statement refinements live in
`refinements.md`.  Broader design ideas live in `future-work.md` and
`memo-strategies.md`.

## Definition Of Done

- [x] No active `axiom` or `sorry` remains in:
  `ParserCombinators/Gen.lean`, `ParserCombinators/Lemmas.lean`,
  `ParserCombinators/Memoized.lean`, or `ParserCombinators/CFG.lean`.
- [x] `gen_sound`, `gen_complete`, and `gen_correct` build against the real
  exact-counter `memoize` implementation.
- [x] `memoize` still reuses exact-counter cache entries; no proof-only
  recomputation path replaces memoization.
- [x] `lake build` succeeds.
- [x] The final audit commands below report no live dependencies on retired
  axiom names.

## Compact Proof Path

The remaining proof work should stay compact.  Do not build a broad parser
algebra library or duplicate generic sound/bounded/complete variants unless a
live downstream proof needs them.

Goal constraint: the final proof should be a small generated-parser
completeness argument over the existing exact-counter memoization invariant,
not a large collection of near-duplicate helper families.  Prefer one named
semantic lemma at each real boundary over repeated inlining of parser
definitions inside the main theorem.

Preferred route:

- Keep the exact-counter `memo_complete` cache-coherence layer as the only
  memo-completeness invariant unless a concrete proof obligation forces a
  sharper local predicate.
- Add one lower-state generated-parser completeness theorem: from
  `memo_complete cfg input memo` and an admissible valid tree over the current
  span, running the generated parser under `memo` contains that tree.
- Instantiate that theorem at `startState` using `memo_complete_empty` in the
  public `gen_complete_exists` / `gen_complete` path.
- Delete or stop using stale fresh-state helpers instead of preserving old
  names with restated meanings.
- Use existing exact-prefix/lower-state bind and after-left/lower-state choice
  lemmas; avoid proving broad generic equivalences for all `ParserM`.

Compactness criteria:

- [x] The final replacement for the bind/traverse axiom is generated-parser
  specific or exact-prefix/lower-state specific, not a broad fresh-state bind
  equivalence.
- [x] The final replacement for the sup/choice axiom is after-left or
  lower-state specific, not a broad fresh-state choice equivalence.
- [x] The proof avoids repetitive inlining of `gen'`, `memoizeStep`, and
  parser combinator internals when a named local helper would expose the needed
  fact more directly.
- [x] New helper lemmas are merged, deleted, or kept private unless they remove
  real duplication or encode a reusable proof boundary.
- [x] The final `Gen.lean` changes read as one coherent proof path: no
  parallel theorem families, compatibility wrappers, or preserved stale helper
  routes remain unless they are still used by a live proof obligation.

## Active Work

### 1. Remove The Bind/Traverse Axiom

Status: complete.

Retired assumption:

- `ParserCombinators/Lemmas.lean`: `mem_runParser_bind_iff_eq_bind_mem_runParser`

Retired dependency:

- `ParserCombinators/Gen.lean`: `runParser_traverse_complete_cons`

Completed work:

- [x] Replace the fresh-state traversal completeness path with a lower-state or
  exact-prefix traversal theorem that threads the memo state produced by the
  head parser and earlier traversal actions.
- [x] Refactor the remaining Gen traversal consumer to use the state-threaded
  theorem.
- [x] Keep this replacement compact: factor repeated terminal/lift/failure or
  bind-state plumbing into named local helpers only where it removes duplicated
  proof logic.
- [x] Delete `mem_runParser_bind_iff_eq_bind_mem_runParser`.

### 2. Remove The Sup/Choice Axiom

Status: complete.

Retired assumption:

- `ParserCombinators/Lemmas.lean`: `runParser_sup_eq_sup_runParser`

Retired dependency:

- `ParserCombinators/Gen.lean`: `complete_of_sup_right`

Completed work:

- [x] Replace the fresh-state right-choice completeness path with an after-left
  or lower-state theorem that accounts for the memo state produced by the left
  branch.
- [x] Refactor generated-rule fold completeness to use the state-threaded
  choice theorem.
- [x] Keep this replacement compact: avoid a generic parser-choice algebra
  layer unless the generated-rule fold proof genuinely needs that exact
  abstraction.
- [x] Delete `runParser_sup_eq_sup_runParser`.

## Next Proof Step

- [x] Finish the exact-counter cache-completeness invariant for generated
  parsers:
  `positionMap_complete`, whole-memo union preservation, and the
  `memoizeStep` compute branch.
- [x] Thread that invariant through lower-state generated-parser completeness,
  then use it to discharge the bind/traverse and sup/choice dependencies above.

## Final Audit

```sh
rg -n "\\baxiom\\b|\\bsorry\\b" ParserCombinators/Gen.lean ParserCombinators/Lemmas.lean ParserCombinators/Memoized.lean ParserCombinators/CFG.lean
rg -n "\\b(runParser_sup_eq_sup_runParser|mem_runParser_bind_iff_eq_bind_mem_runParser)\\b" ParserCombinators/Gen.lean ParserCombinators/Lemmas.lean
lake build
```

Historical notes or explicitly retired `old_*` statement records are not active
blockers, but no live proof should depend on retired axiom names.
