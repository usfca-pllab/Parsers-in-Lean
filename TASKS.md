# Current Missing Work

This file tracks items that are already marked in the code as `TODO`, `sorry`,
or `axiom`.  Broader suggestions live in `future-work.md`.

## `ParserCombinators/Gen.lean`

- [ ] Replace the two top-level correctness TODO comments with precise theorem
  declarations and/or references to the completed theorem.
  Existing markers:
  - `TODO(maemre): correctness theorem (by injecting validity proofs above)`
  - `TODO(maemre): correctness theorem (sound/complete)`
  Concrete shape:
  - [x] Soundness is now represented by:
    ```lean
    theorem gen_sound (cfg : @CFG α ν) n input :
      sound cfg n (gen (μ := List) cfg n) input
    ```
  - [ ] Decide whether the "injecting validity proofs" TODO should become an
    actual typed generator, for example a parser returning a subtype like
    `{tree : ParseTree cfg // tree.Valid ∧ tree.root = Symbol.nonterm n}`, or
    whether the external `gen_sound` theorem is the intended replacement.
  - [ ] If the subtype route is chosen, define the subtype specification,
    implement the typed wrapper around `gen'` or `gen`, and prove that erasing
    proofs gives the existing generated parser behavior.
  - [ ] If the external-proof route is chosen, remove the stale TODO comment
    and add a short comment near `gen_sound` explaining that generated parsers
    stay untyped while validity/root information is supplied by the theorem.

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

- [ ] Remove or update the stale helper-lemma TODO comment.
  Current marker:
  - `TODO: helper lemmas (placeholders; proofs to be filled later)`
  Concrete status:
  - `mem_zip_index`, `runParser_traverse_origin`,
    `runParser_traverse_origin_bounded`, `runParser_traverse_result_bounds`,
    `terminal'_sound`, `terminal'_bounded`, `failure_sound`,
    `failure_bounded`, `sound_of_sup_sound`, and `bounded_of_sup_bounded` are
    now proved.
  - The remaining action is documentation cleanup in `Gen.lean`: replace the
    placeholder comment with a neutral section comment such as "Traversal and
    parser-constructor lemmas used by generated-parser soundness."

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
