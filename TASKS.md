# Current Missing Work

This file tracks items that are already marked in the code as `TODO`, `sorry`,
or `axiom`.  Broader suggestions live in `future-work.md`.

## `ParserCombinators/Gen.lean`

- [x] Replace the two top-level correctness TODO comments with precise theorem
  references and the external-proof design choice.
  Removed markers:
  - `TODO(maemre): correctness theorem (by injecting validity proofs above)`
  - `TODO(maemre): correctness theorem (sound/complete)`
  Resolution:
  - [x] Soundness is now represented by:
    ```lean
    theorem gen_sound (cfg : @CFG α ν) n input :
      sound cfg n (gen (μ := List) cfg n) input
    ```
  - [x] Chose the external-proof route: generated parsers continue to return
    plain `ParseTree cfg` values, while validity/root information is supplied
    by theorem statements such as `gen_sound` and the planned `gen_complete`.
  - [x] Recorded the proof-carrying subtype parser route in `alternatives.md`.
  - [x] Replaced the stale TODO comments in `Gen.lean` with a short design
    comment.

- [ ] Strengthen and prove the generated-parser completeness theorem.
  Current placeholder:
  ```lean
  abbrev complete (cfg : @CFG α ν) (n : ν)
    (p : ParserM (tag := tag cfg) α List (ParseTree cfg)) (input : Array α)
    (_h : cfg.derives [Symbol.nonterm n] (input.toList.map Symbol.term))
    := ∃ tree, tree ∈ (runParser p input).1[0]?.getD ⊥
  ```
  Concrete replacement work:
  - [ ] Replace `complete` with a statement that asks for a full-span parse at
    end position `input.size`, not merely some result at key `0`.
    Candidate shape:
    ```lean
    abbrev complete (cfg : @CFG α ν) (n : ν)
      (p : ParserM (tag := tag cfg) α List (ParseTree cfg)) (input : Array α)
      :=
      cfg.derives [Symbol.nonterm n] (input.toList.map Symbol.term) →
        ∃ tree,
          tree ∈ (runParser p input 0).1.getD input.size [] ∧
          tree.Valid ∧
          tree.root = Symbol.nonterm n ∧
          tree.leaves = input.toList
    ```
  - [ ] Add the theorem:
    ```lean
    theorem gen_complete (cfg : @CFG α ν) n input :
      complete cfg n (gen (μ := List) cfg n) input
    ```
  - [ ] Prove or import the parse-tree/derivation bridge needed in the reverse
    direction from the existing `ParseTree.derives_of_Valid_tree` theorem:
    from a derivation `cfg.derives [Symbol.nonterm n] terminals`, construct a
    valid parse tree rooted at `n` with those leaves.
  - [ ] Prove parser completeness constructor lemmas for the generated parser
    cases: terminal, empty rule/traversal, sequencing through `List.traverse`,
    rule choice through `foldl`/`⊔`, and recursive nonterminal calls through
    `memoize_induction`.
  - [ ] Combine `gen_sound` and `gen_complete` into the intended public
    correctness theorem if a single theorem is desired, for example:
    ```lean
    theorem gen_correct (cfg : @CFG α ν) n input :
      sound cfg n (gen (μ := List) cfg n) input ∧
      complete cfg n (gen (μ := List) cfg n) input
    ```

- [x] Fill the helper lemmas currently left as placeholders:
  - [x] `mem_zip_index`
  - [x] Replace unsound `runParser_mem_bounds` with `result_bounded`
    invariants.
    - The original arbitrary-`ParserM` statement was removed.
    - Added boundedness lemmas for terminals, failure, joins, and traversal.
    - Strengthened `gen_sound`'s memoization induction predicate to carry both
      `sound` and `result_bounded`.
  - [x] `terminal'_sound`

- [x] Finish the `gen_sound` proof.
  Completed pieces:
  - Proved the local traversal-origin claim `h_mem_subtrees`.
  - Replaced the two `sorry`s ruling out impossible terminal/nonterminal subtree
    cases.
  - Completed the remaining child-parser reasoning using `h_recur`.

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
