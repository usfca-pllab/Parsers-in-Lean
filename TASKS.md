# Current Missing Work

This file tracks items that are already marked in the code as `TODO`, `sorry`,
or `axiom`.  Broader suggestions live in `future-work.md`.

## `ParserCombinators/Gen.lean`

- [ ] Define and prove the intended correctness theorem for generated parsers.
  Existing markers:
  - `TODO(maemre): correctness theorem (by injecting validity proofs above)`
  - `TODO(maemre): correctness theorem (sound/complete)`

- [ ] Fill the helper lemmas currently left as placeholders:
  - [x] `mem_zip_index`
  - [ ] `runParser_mem_bounds`
    - Current statement is too broad for arbitrary `ParserM`: a lifted primitive
      parser can put results at invalid keys.  It should be replaced by a
      generated-parser or result-membership boundedness invariant.
  - [x] `terminal'_sound`

- [x] Finish the `gen_sound` proof.
  Completed pieces:
  - Proved the local traversal-origin claim `h_mem_subtrees`.
  - Replaced the two `sorry`s ruling out impossible terminal/nonterminal subtree
    cases.
  - Completed the remaining child-parser reasoning using `h_recur`.

- [ ] Revisit the TODO about the proof shape around `rule.zip subtrees`.
  The current note suggests an induction over the rule and children may be a
  cleaner way to prove child validity.

## `ParserCombinators/Lemmas.lean`

- [ ] Replace `memoize_induction` with a theorem.

- [ ] Replace `runParser_sup_eq_sup_runParser` with a theorem.

- [ ] Replace `runParser_map` with a theorem.

- [ ] Replace `runParser_pure` with a theorem.

- [ ] Replace `mem_runParser_terminal_iff` with a theorem.
  This List-specific terminal semantics axiom was added as the narrow primitive
  fact needed to prove `terminal'_sound`.

- [ ] Replace `mem_runParser_bind_iff_eq_bind_mem_runParser` with a theorem.
  There are two declarations in the file: an older commented-out statement
  marked incorrect, and the current list-membership statement used downstream.
  The current statement should be proved or refined until it is provable.

## `ParserCombinators/Memoized.lean`

- [ ] Prove the relevant laws for the `ParserM` monad instance.

- [ ] Add the constrained-monad/lower-lift theorems noted in the comments:
  - `lower_preserves_identity`
  - `lower_preserves_composition`
  - `isomorphism_lower_lift`

- [ ] Prove that `ParserM` has the intended `SemilatticeSup` and `OrderBot`
  structure, or replace the TODO with the exact weaker laws actually needed.

- [ ] Replace the cache update TODO with an `alter`-based implementation if it
  still improves the `memoize` code.

- [ ] Prove that `runParser` commutes with the parser combinators.

- [ ] Add the extra parser example tests requested by the TODO near
  `funcParser`.

- [ ] Implement `memo`.

- [ ] Implement `memo'`.

- [ ] Prove `memo_sound`.

- [ ] Prove `memo_complete`.
