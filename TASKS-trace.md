# TASKS Trace

This file preserves the older detailed checklist for traceability.  The active
backlog now lives in `TASKS.md`.

## Active-List Cleanup

`TASKS.md` was narrowed to the overall proof goal and now tracks only the live
axiom-removal backlog.  The detailed completed work below is retained here so
the proof process remains auditable without cluttering the working queue.

Latest cleanup: `TASKS.md` now intentionally avoids naming every intermediate
helper, old TODO, and completed proof layer as an active task.  It is a
goal-oriented checklist that tracks only:

- the final definition of done,
- the two remaining assumptions and their live Gen dependencies,
- the immediate proof route through exact-counter cache completeness and
  lower-state generated-parser completeness,
- final audit and build checks.

Detailed helper names, theorem-adjustment reviews, completed proof layers, and
older tactical TODOs stay in this trace file for context when resuming
implementation.

This keeps the working task list aligned with the overall goal: eliminate the
remaining proof assumptions in the core while preserving exact-counter
memoization.  The long-form record below remains the traceability source for
why particular helper layers were added, replaced, or retired.

Current audit snapshot for the active file:

```text
No matches:
rg -n "\\baxiom\\b|\\bsorry\\b" ParserCombinators/Gen.lean ParserCombinators/Lemmas.lean ParserCombinators/Memoized.lean ParserCombinators/CFG.lean
rg -n "\\b(runParser_sup_eq_sup_runParser|mem_runParser_bind_iff_eq_bind_mem_runParser)\\b" ParserCombinators/Gen.lean ParserCombinators/Lemmas.lean
```

`lake build` succeeds after the axiom declarations and stale helper paths were
removed.

Latest verified replacement-layer progress:

- Added `generatedListSymbolParser` to name the List-specialized parser
  generated for a single grammar symbol.  This avoids repeated unfolding of a
  large match in generated traversal proofs.
- Added `lower_memo_wellFormed_generated_traverse_memoize`, proving that
  generated child traversal preserves memo well-formedness under the actual
  exact-counter `memoize` implementation.
- Added `mem_lower_traverse_cons_terminal_exists_tail_wf`, the terminal-head
  traversal decomposition that also exposes a well-formed memo state for the
  tail.
- Added `lower_result_bounded_generated_traverse_memoize`, proving direct
  lower-state bounds for generated child traversal results.
- Added `lower_valid_pairs_generated_traverse_memoize`, proving generated
  traversal results align with the rule symbols as `validChildPair`s.
- Added `lower_generated_rule_branch_result_sound_bounded_memoize`, assembling
  the lower-state result soundness, boundedness, and memo well-formedness
  invariant for one generated rule branch.
- Added the whole-memo exact-counter completeness preservation layer:
  `positionMap_complete`, `positionMap_complete_sup`,
  `positionMap_complete_of_memo_complete_sup`, `memo_complete_sup`,
  `memo_complete_memoizeStep_compute`, and `memo_complete_memoizeStep`.
  This proves that `memoizeStep` preserves the generated-parser
  cache-completeness invariant through both cache-hit and compute branches.
- Added the lower-state exact-counter cache-completeness bridge:
  `lower_memo_complete`, `lower_map_memo_complete`,
  `lower_memo_complete_memoizeStep_lift`, `lower_failure_memo_complete`, and
  `lower_memo_complete_memoize`.  This threads `memo_complete` through
  `ParserM.lower` for result maps and the implemented `memoize` wrapper
  without unfolding the generated parser or replacing memoization with
  recomputation.
- Added the lower-state generated-rule insertion bridge:
  `generatedSymbolParser`, `generatedRuleParser`,
  `lower_rule_branch_complete`, `lower_complete_of_foldl_sup_mem_split`, and
  `lower_gen'_rule_complete_after_split`, plus the small split adapters
  `list_split_of_mem` and `generatedRuleParser_split_of_rule_mem`.  These
  expose the facts needed to replace the stale fresh-state `gen'_rule_complete`
  path: prove one rule branch under the memo state produced by earlier rule
  branches, then insert it into the generated `foldl` using the existing
  after-left choice semantics.
- Added the `memo_complete` state-preservation fold layer:
  `joinUnderCache_memo_complete`,
  `traversable_foldl_joinUnderCache_memo_complete`,
  `list_foldl_traversable_joinUnderCache_memo_complete`, and
  `lower_return_bind_cons_memo_complete`.  These provide the missing invariant
  for constructive traversal completeness: earlier result actions can run
  before the selected parse result without destroying exact-counter cache
  completeness.
- Extended that state-preservation layer through bind:
  `bindContinue_memo_complete`, `parser_bind_memo_complete`,
  `lower_bind_constructor_memo_complete`, and `lower_lift_memo_complete`.
  These are the cache-completeness analogs of the existing memo-well-formedness
  bind lemmas and give corrected traversal proofs a compact way to thread
  `memo_complete` through `Parser.bind` and lifted parser primitives.
- Extended exact-counter cache-completeness preservation through choice and
  generated-rule folds with `parser_pure_memo_complete`,
  `parser_orElse_memo_complete`, `lower_sup_memo_complete`, and
  `lower_memo_complete_of_foldl_sup`.  These are the prefix-state invariants
  needed to use `lower_gen'_rule_complete_after_split` after earlier generated
  rule branches have executed.
- Added generated-rule and `gen'` fold cache-completeness bridges:
  `lower_rule_branch_memo_complete_of_traverse` and
  `lower_gen'_memo_complete_of_rules`.  These isolate the remaining missing
  obligation for the lower-state completeness proof to generated child
  traversal, rather than the whole generated parser fold.
- Added generated child traversal cache-completeness preservation:
  `lower_memo_complete_traverse_cons_terminal`,
  `lower_memo_complete_traverse_cons_lift`,
  `lower_memo_complete_traverse_cons_failure`,
  `lower_memo_complete_traverse_cons_memoize`, and
  `lower_memo_complete_generated_traverse_memoize`.  This closes the
  state-preservation side for generated child traversal; the remaining
  generated-traversal work is direct membership/completeness under
  `memo_complete`.
- Added bind-prefix cache-completeness helpers:
  `bind_action_prefix_memo_complete` and
  `mem_lower_bind_exists_action_split_complete`.  These are the
  `memo_complete` analogs of the existing well-formedness prefix/decomposition
  lemmas and expose the exact threaded memo state needed by lower-state
  traversal completeness without using the stale fresh-state bind axiom.
- Added direct generated child traversal membership under exact-counter cache
  completeness:
  `lower_traverse_complete_cons_lift_of_head_tail_complete` and
  `lower_generated_traverse_complete_of_admissible_valid_pairs`.  This proves
  admissible generated child forests are produced by the generated traversal
  under any `memo_complete` memo state, using terminal construction and the
  actual memoized nonterminal head path instead of the stale fresh-state
  `GeneratedChildWitness` route.
- Added the lower-state generated-rule fold bridge
  `lower_gen'_complete_of_admissible_rule`.  It selects the concrete CFG rule
  inside the generated `gen'` fold, proves its child traversal under the memo
  state produced by earlier rule branches, and inserts the branch with
  `lower_gen'_rule_complete_after_split`.
- Added exact-counter key lookup facts:
  `counter_getElem?_eq_of_toKey_eq` and `counter_getD_eq_of_toKey_eq`.  These
  turn equality of executable counter keys into usable lookup/default lookup
  equalities, which is needed by the recursive completeness rewrite when
  discharging `resultMap_complete` obligations for cached body results.
- Extended the exact-counter key-transfer layer with
  `counter_dec_getElem?_eq_of_getElem?_eq`,
  `admissibleTreeWith_congr_counter_getElem?`, and
  `admissibleForestWith_congr_counter_getElem?`.  These transfer admissibility
  across counters with identical executable lookups and through one `dec`,
  which is the core coherence fact needed when a cached `Counter.toKey` is
  re-instantiated by `resultMap_complete`.
- Added `resultMap_complete_lower_gen'_memoized_body`, a generated-parser
  specific compute-body bridge.  It converts an admissible nonterminal tree at
  the parent exact-counter key into membership in the `gen'` body run under the
  decremented counter, using the lower-state rule-fold completeness theorem.
  This names the key semantic boundary needed by the recursive completeness
  induction instead of inlining rule selection and counter-key transfer at each
  cache insertion site.
- Ran the theorem-adjustment review for the `memo_complete` generated
  traversal/rule-fold helpers and refined their `memoizeStep` preservation
  premise from unguarded to guarded by `counter[n]? ≠ some 0`.  The review
  confirmed this matches executable `memoize`, which runs `memoizeStep` only in
  the nonzero counter branch, and avoids a proof obligation for zero-counter
  `memoizeStep` runs that the implementation never performs.  Updated
  `lower_memo_complete_traverse_cons_memoize`,
  `lower_memo_complete_generated_traverse_memoize`,
  `lower_generated_traverse_complete_of_admissible_valid_pairs`,
  `lower_gen'_complete_of_admissible_rule`, and
  `resultMap_complete_lower_gen'_memoized_body` in place rather than adding a
  duplicate guarded theorem family.
- Added `memoized_gen_complete_invariant`, the recursive exact-counter
  completeness invariant for generated parsers.  It carries lower-state
  `memo_complete` preservation, guarded compute-branch `resultMap_complete`,
  and admissible-tree membership for the current memoized parser.
- Rewired `gen_complete_exists_of_admissible_valid_tree` to instantiate that
  invariant at `startState` with `memo_complete_empty`, so public
  `gen_complete` and `gen_correct` build through the real exact-counter
  `memoize` implementation.
- Deleted the stale fresh-state runParser completeness route:
  `runParser_map_complete`, `runParser_traverse_complete_cons`,
  `TraverseCompleteWitness`, `GeneratedChildWitness`, the witness conversion
  helpers, the old `complete_of_sup_right` / fold helpers, and the old
  arbitrary-counter `gen_complete_of_admissible_tree_span` route.
- Removed the now-unused axiom declarations
  `runParser_sup_eq_sup_runParser` and
  `mem_runParser_bind_iff_eq_bind_mem_runParser` from `Lemmas.lean`.
- `lake build` succeeds after these additions.

Latest theorem-contract review and cleanup:

- Ran the repo-local theorem-adjustment review for replacing the old
  `gen'_sound_bounded` path.  The sub-agent agreed with the lower-state fold
  direction but rejected an unguarded body-step theorem because zero-counter
  nonterminals execute as failure and should not require compute-body facts.
- Added guarded lower-state variants:
  `lower_memo_wellFormed_generated_traverse_memoize_guarded`,
  `lower_result_bounded_generated_traverse_memoize_guarded`,
  `lower_valid_pairs_generated_traverse_memoize_guarded`,
  `lower_generated_rule_branch_result_sound_bounded_memoize_guarded`, and
  `lower_gen'_result_sound_bounded_memoize`.
- Strengthened the internal induction predicate in `gen_sound` so it carries
  lower-state result soundness, bounds, memo well-formedness, and the guarded
  compute-body invariant needed by `memoizeStep`.
- Deleted the obsolete `gen'_sound_bounded` theorem after `gen_sound` no longer
  used it.  This retires the stale arbitrary-`recur` fresh-state contract.
- `lake build` succeeds after this rewrite.
- Deleted the unused fresh-state sup contracts `sound_of_sup_sound` and
  `bounded_of_sup_bounded`, which the earlier theorem review had identified as
  invalid for arbitrary memo-sensitive parsers.  The only remaining direct sup
  axiom use is now `complete_of_sup_right`, through the older
  `complete_of_foldl_sup_mem` completeness path.
- `lake build` succeeds after this cleanup.
- Deleted the unused generic fresh-state traversal helpers
  `runParser_traverse_origin_bounded` and `runParser_traverse_result_bounds`
  after theorem-adjustment review.  The review confirmed they had no Lean call
  sites and depended on the stale state-insensitive bind view.  Generated
  traversal boundedness now lives in the lower-state generated-parser-specific
  layer.
- Added small terminal-primitive facts in `Gen.lean` for the future
  state-threaded traversal-completeness replacement:
  `terminalPrimitive_getElem?_eq_some_of_match`,
  `terminalPrimitive_toList_eq_singleton_of_match`,
  `memoState_pure_snd_val_eq`, `memoState_pure_snd_eq`, and
  `terminalPrimitive_snd_eq`.  These expose the successful terminal result map
  and unchanged memo state without unfolding the primitive at each downstream
  proof site.
- Added `lower_return_bind_cons_complete`,
  `lower_traverse_complete_cons_return`, and
  `lower_traverse_complete_cons_terminal`.  These prove the pure-head and
  terminal-head traversal completeness constructors under an arbitrary memo
  state, avoiding the stale fresh-state bind axiom for those cases.
- Added the first exact-counter cache-completeness layer:
  `memo_complete`, `memo_complete_empty`,
  `mem_lower_memoize_of_cache_complete`,
  `mem_lower_memoize_of_body_mem`, and
  `mem_lower_memoize_of_body_or_cache_complete`.  This isolates the two
  executable branches of `memoize`: a cache hit is complete if the exact-key
  cache entry is complete, and a miss reduces to body completeness under the
  same memo state.
- Extended that cache-completeness layer with key-level insertion and result
  map transfer facts:
  `memoWithCachedResult_getElem?_self`,
  `memoWithCachedResult_getElem?_ne`, `resultMap_complete`,
  `resultMap_complete_of_memo_complete_getElem?`,
  `resultMap_complete_of_quot_eq`,
  `resultMap_complete_unionSup_left`,
  `resultMap_complete_unionSup_right`,
  `memo_complete_memoWithCachedResult`, and
  `memo_complete_memoizeStep_cache`.  These avoid relying on full
  `Counter.toKey` injectivity by making exact-key equality an explicit
  premise for inserted entries.
- `lake build` succeeds after these additions.

The theorem-adjustment review for replacing `Gen.gen'_sound_bounded` found
that the lower-state direction is right, but the span-guarded `lower_sound`
predicate is too weak for memoized cache insertion.  The reviewed replacement
invariant is:

- `lower_result_sound cfg n p input`
- `lower_result_bounded cfg p input`
- `lower_memo_wellFormed cfg p input`

The direct result-sound layer has been added and verified by `lake build`.
New supporting facts include:

- `lower_result_sound`
- `lower_sound_of_lower_result_sound`
- `sound_of_lower_result_sound`
- `resultMap_sound_of_lower_result_sound`
- `resultMap_bounded_of_lower_result_bounded`
- `lower_map_result_sound_of_forall`
- `lower_bind_constructor_result_sound`
- `lower_result_sound_memoizeStep_lift`
- `lower_result_sound_memoize`
- `lower_result_bounded_memoize`
- `lower_memo_wellFormed_memoize`
- `lower_failure_result_sound`
- `lower_result_sound_of_sup_sound_after_left`
- `lower_result_sound_bounded_memo_of_foldl_sup`
- `lower_rule_branch_result_sound_of_traverse_pairs`
- `lower_rule_branch_memo_wellFormed_of_traverse`

Recent generated-traversal decomposition work:

- `mem_lower_traverse_cons_memoize_exists_head_tail` was added and verified.
  It decomposes a `List.traverse` result whose head parser is the actual
  `memoize` implementation, exposing the memoized head result and the tail
  result under the threaded memo state.
- `mem_lower_traverse_cons_memoize_exists_head_tail_wf` was added and
  verified.  It strengthens the memoized-head decomposition with a proof that
  the memo state threaded into the tail traversal is `memo_wellFormed`, assuming
  the `memoizeStep` primitive and tail traversal preserve well-formedness.
- `mem_lower_traverse_cons_terminal_exists_tail` was strengthened and verified.
  It now also exposes the terminal head membership and the `start + 1 <=
  input.size` bound needed by lower-state traversal bounds.
- A fully generic arbitrary-head theorem
  `mem_lower_traverse_cons_exists_head_tail` was tried and removed: even after
  inlining the bind reconstruction it timed out in `Lemmas.lean`.  The current
  proof route should stay generated-parser-specific, using the terminal and
  memoized-head decomposition lemmas rather than a broad parser-algebra theorem.

A theorem-adjustment review for the old sup helper contracts confirmed:

- `sound_of_sup_sound`, `bounded_of_sup_bounded`, and
  `complete_of_sup_right` are not provable for arbitrary memo-sensitive
  parsers.
- The old names should be deleted once unused rather than reused with
  state-aware statements, because the names suggest the invalid fresh-state
  abstraction.
- The replacement route is to use `*_after_left` / `lower_*` state-aware
  helpers and the lower-state `gen'` theorem; completeness should use
  `complete_of_foldl_sup_mem_after_prefix` where branch membership is known
  after the prefix state.
- A later review reaffirmed that deleting the old fresh-state sup contracts is
  theorem-contract sound, but call sites cannot be swapped locally while
  `gen'_sound_bounded` only assumes fresh `sound`/`result_bounded`.  The
  downstream route must strengthen that path to `lower_result_sound`,
  `lower_result_bounded`, and `lower_memo_wellFormed`, then recover fresh
  `sound` and `result_bounded` at the outer boundary.

The active file was then tightened again to remove checked-off scaffolding from
the working queue.  Those completed state-parametric, state-preservation, and
constructor-specific proof layers remain recorded below under the corresponding
old bind/sup sections.  The live file now contains only:

- the two remaining axiom targets,
- the current downstream uses that force them,
- the next proof replacements to attempt,
- the final audit command.

Current active proof debt after the cleanup:

- `Lemmas.runParser_sup_eq_sup_runParser`
- `Lemmas.mem_runParser_bind_iff_eq_bind_mem_runParser`

The removed `Lemmas.memoize_induction` work is complete and recorded below.

### Snapshot Moved Out Of `TASKS.md`

The short active file intentionally omits the detailed replacement inventory.
The most relevant current names are:

- Bind replacement layer:
  `mem_lower_bind_exists_action_split_mem`,
  `mem_runParser_bind_exists_action_split_mem`,
  `mem_lower_bind_iff_exists_action_split_mem`,
  `mem_runParser_bind_iff_exists_action_split_mem`,
  `mem_lower_traverse_complete_cons_of_bind_getElem_action_mem`,
  `mem_runParser_traverse_complete_cons_of_bind_getElem_action_mem`,
  `mem_lower_traverse_cons_lift_exists_head_tail`,
  `mem_lower_traverse_cons_bind_return_exists_head_tail`, and
  `Gen.bind_action_prefix_memo_wellFormed`,
  `Gen.mem_lower_bind_exists_action_split_wf`,
  `Gen.lower_bind_constructor_result_bounded`,
  `Gen.lower_bind_constructor_sound`.
- Memoized lower-state bridge layer:
  `lower_sound_memoizeStep_lift`,
  `lower_result_bounded_memoizeStep_lift`, and
  `lower_memo_wellFormed_memoizeStep_lift`.
- Map lower-state transfer layer:
  `lower_map_sound_of_forall` and
  `lower_map_result_bounded_of_forall`.
- Rule-branch lower-state bridge layer:
  `valid_node_of_validChildPairs`,
  `lower_rule_branch_sound_of_traverse_pairs`, and
  `lower_rule_branch_result_bounded_of_traverse`.
- Generated traversal decomposition layer:
  `mem_lower_traverse_cons_terminal_exists_tail`.
- Remaining bind-axiom user:
  `Gen.runParser_traverse_complete_cons`.
- Sup replacement layer:
  `mem_lower_sup_iff_after_left`,
  `sound_of_sup_sound_after_left`,
  `bounded_of_sup_bounded_after_left`,
  `complete_of_sup_right_after_left`,
  `lower_complete_of_sup_left`,
  `lower_complete_of_sup_right_after_left`,
  `lower_complete_of_foldl_sup_acc`,
  `lower_complete_of_foldl_sup_head_after_left`,
  `lower_complete_of_foldl_sup_mem_after_prefix`,
  `complete_of_foldl_sup_mem_after_prefix`,
  `lower_sound_of_sup_sound_after_left`, and
  `lower_bounded_of_sup_bounded_after_left`.
- Remaining sup-axiom user:
  `Gen.complete_of_sup_right`.

## Original Current Missing Work

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

- [x] Strengthen and prove the generated-parser completeness theorem.
  Current placeholder:
  ```lean
  abbrev complete (cfg : @CFG α ν) (n : ν)
    (p : ParserM (tag := tag cfg) α List (ParseTree cfg)) (input : Array α)
    (_h : cfg.derives [Symbol.nonterm n] (input.toList.map Symbol.term))
    := ∃ tree, tree ∈ (runParser p input).1[0]?.getD ⊥
  ```
  Concrete replacement work:
  - [x] Replace `complete` with a statement that asks for a full-span parse at
    end position `input.size`, not merely some result at key `0`.
    Final shape:
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
  - [x] Add the theorem:
    ```lean
    theorem gen_complete (cfg : @CFG α ν) n input :
      complete cfg n (gen (μ := List) cfg n) input
    ```
  - [x] Add the public combined theorem:
    ```lean
    theorem gen_correct (cfg : @CFG α ν) n input :
      sound cfg n (gen (μ := List) cfg n) input ∧
      complete cfg n (gen (μ := List) cfg n) input
    ```
  - [x] Add the narrow parser-side completeness bridge `gen_complete_exists`.
    It was initially introduced as an axiom while the minimal-tree/fuel/cache
    argument was developed, and is now proved.

- [x] Replace `gen_complete_exists` with a theorem.
  Planned route:
  - Prove a minimal-tree theorem excluding same-nonterminal same-span cycles.
  - Prove parser completeness for those minimal valid trees, using the
    `remaining input + 1` memoization budget and exact-counter cache
    coherence.
  - [x] Add parser-constructor completeness helpers for generated child
    traversal:
    - `runParser_map_complete`
    - `runParser_traverse_complete_cons`
    - `TraverseCompleteWitness`
    - `runParser_traverse_complete_of_witness`
  - [x] Add parser-constructor completeness helpers for generated rule
    branches and rule choice:
    - `runParser_rule_branch_complete`
    - `complete_of_sup_left`
    - `complete_of_sup_right`
    - `complete_of_foldl_sup_acc`
    - `complete_of_foldl_sup_mem`
    - `gen'_rule_complete`
  - [x] Add parse-tree validity extraction helpers for generated children:
    - `valid_node_terminal_child`
    - `valid_node_nonterminal_child`
  - [x] Add generated-child witness helpers connecting parser-side child
    completeness to generated rule completeness:
    - `GeneratedChildWitness`
    - `generatedChildWitness_to_traverse`
    - `gen'_rule_complete_of_child_witness`
  - [x] Add span-based helpers that turn valid generated children plus
    recursive child memberships into generated-child witnesses:
    - `forestLeaves`
    - `array_getElem?_of_toList_eq_append_singleton`
    - `validChildPair`
    - `generatedChildWitness_of_valid_pairs`
    - `generatedChildWitness_of_valid_node_span`
  - [x] Retire the old direct valid-node/tree/derivation wrappers for the
    generated one-step parser after theorem-adjustment review.  The deleted
    names were `gen'_complete_of_valid_node_span`,
    `gen'_complete_of_valid_node_full_span`,
    `gen'_complete_of_valid_tree_full_span`, and
    `gen'_complete_exists_of_derives`.  They were unused by the active
    public completeness route and encoded the stale fresh-state abstraction for
    arbitrary `recur`.
  - [x] Prove a memoized-recursion exposure lemma for an empty `runParser`
    state:
    when the exact counter is not zero and no cache entry exists, membership in
    `runParser (g (memoize (counter.dec ...)) n)` is preserved by
    `runParser (memoize counter g n)`.
    This is the bridge from the proved `gen'` completeness lemmas to `gen`.
    Completed pieces:
    - [x] Factor `memoizeStep` out of `memoize` so the cache miss body can be
      unfolded without normalizing the recursive definition.
    - [x] Prove `mem_memoizeStep_of_compute_mem`.
    - [x] Prove the cache-miss result-map equalities:
      - `memoizeStep_compute_fst_eq`
      - `memoizeStep_empty_fst_eq_compute`
    - [x] Prove the cache-hit branch lemmas:
      - `memoizeStep_cache_fst_eq`
      - `mem_memoizeStep_of_cache_mem`
    - [x] Prove the generalized initial-state exposure lemma
      `mem_memoize_startState_of_body_mem` for arbitrary non-exhausted
      counters.
    - [x] Prove `mem_memoize_empty_of_body_mem`.
    - [x] Retire the unused Gen-side bridges `gen_complete_exists_of_body` and
      `gen_complete_exists_of_decremented_recur` after theorem-adjustment
      review.  They supported the old one-step `gen'` wrapper route; the
      active proof now goes through the admissible/minimal-tree route.
  - [x] Prove or reuse the required lower/lift membership law for `ParserM`:
    `memoize` is implemented as `ParserM.lift`, and `runParser` lowers lifted
    parsers through `Parser.bind`, so the exposure lemma depends on showing
    that lowering a lifted primitive parser reconstructs its result map
    membership.
    - [x] Prove the inner/outer fold preservation helpers needed for the
      `Parser.bind` lowering proof:
      - `mem_traversable_foldl_joinUnderCache_of_head`
      - `mem_traversable_foldl_joinUnderCache_of_split`
      - `mem_list_foldl_traversable_joinUnderCache_of_acc`
      - `mem_list_foldl_traversable_joinUnderCache_of_split`
      - `mem_traversable_foldl_lower_return_of_mem`
      - `mem_list_foldl_lower_returns_of_resultMap`
      - `mem_bindContinue_return_of_mem`
      - `parser_bind_fst_eq_bindContinue`
      - `mem_parser_bind_return_of_mem`
      - `mem_lower_lift_of_mem`
    - [x] Expose the `Parser.bind` implementation as an explicit state/reader
      body in `Memoized.lean` rather than relying on generic `MStateT` do-bind
      normalization.
    - [x] Factor the continuation part into `Parser.bindActions` and
      `Parser.bindContinue`, and prove the membership theorem for the
      bind-return continuation core.
    - [x] Extract a smaller named bind-core theorem/projection so the final
      `ParserM.lift` membership theorem does not force Lean to normalize the
      whole `ParserM.lower` expression.
  - [x] Define the finite-counter admissibility/minimality invariant for parse
    trees in an input span.  Added `SpanVisit`, `nodeSpanVisit`,
    `AdmissibleTreeWith`, `AdmissibleForestWith`, `AdmissibleTree`, and the
    node/forest inversion lemmas.  The invariant rules out ancestor
    same-nonterminal/same-span repeats and threads the exact `Counter`
    budget through child spans.
  - [x] Prove generated-parser completeness for admissible valid nodes by
    structural/minimal-tree induction, using the memoized-recursion exposure
    lemma to recursive nonterminal children.
    Completed pieces:
    - [x] Add `generatedChildWitness_of_admissible_valid_pairs`, which turns
      admissible valid child forests into generated child witnesses for the
      decremented memoized recursive parser.
    - [x] Add `gen_complete_of_admissible_tree_span`, the size-based induction
      theorem showing that `memoize counter gen'` parses an admissible valid
      nonterminal tree over its input span.
    - [x] Add `gen_complete_of_admissible_node_span`, the node-specialized
      wrapper.
    - [x] Add `gen_complete_exists_of_admissible_valid_tree`, the full-span
      bridge from an admissible valid tree to `gen`.
  - [x] Combine the admissible-tree theorem with
    `ParseTree.exists_Valid_tree_of_derives` (or its future theorem
    replacement) to replace `gen_complete_exists`.
    - [x] Add `exists_minimal_valid_tree_of_derives`, selecting a
      size-minimal valid tree with the requested root and leaves from any CFG
      derivation.
    - [x] Prove that a size-minimal valid tree satisfies the
      `AdmissibleTree` finite-counter invariant.
      - [x] Add child-span decomposition/bounds helpers:
        `input_eq_child_span_of_mem` and `child_span_bounds_of_mem`.
      - [x] Add the direct child validity projection
        `valid_node_child_node_valid_of_mem`.
      - [x] Add direct minimality contradiction helper
        `minimal_valid_tree_no_child_same_root_leaves`.
      - [x] Add counter decrement helpers:
        `counter_dec_self_getD`, `counter_dec_other_getElem?`, and
        `counter_dec_other_getElem?_ne_zero`.
      - [x] Prove the immediate subtree-replacement lemma: replacing a valid
        node child by a smaller valid node with the same root and leaves
        preserves parent validity/root/leaves and decreases size.
        Added `validChildPair_replace_same_root`,
        `list_sizeOf_replace_lt`, `node_sizeOf_replace_child_lt`,
        `valid_node_replace_child_split`, and
        `minimal_valid_node_no_smaller_child_replacement_split`.
      - [x] Lift replacement through ancestors so global minimality implies
        every node subtree is minimal for its own root/leaves.
        Added `ReplaceSubtree`, `TreeSubtree`,
        `replaceSubtree_preserves_valid_root_leaves_size`,
        `replaceSubtree_of_subtree`, and
        `minimal_valid_tree_no_smaller_subtree_replacement`.
      - [x] Use subtree minimality to rule out same-nonterminal same-span
        repeats in `seen`.
        Added `ProperTreeSubtree`, `treeSubtree_valid_of_valid`,
        `treeSubtree_size_le`, `properTreeSubtree_size_lt`,
        `properTreeSubtree_valid_of_valid`,
        `minimal_valid_tree_no_proper_descendant_same_root_leaves`,
        `list_middle_eq_drop_take`, `list_middle_eq_of_same_span`,
        `minimal_valid_tree_no_proper_descendant_same_span`, and
        `minimal_valid_tree_no_proper_descendant_same_nodeSpan`.
      - [x] Prove the counter budget obligation from the strictly decreasing
        span lengths of repeated same-nonterminal ancestors.
        - [x] Add `counterForSeen`, mirroring the recursive counter produced
          from the `seen` path.
        - [x] Add `CounterMatchesSeen` and cons/node-span preservation lemmas
          for threading the equality invariant through admissibility
          constructors.
        - [x] Add `spanVisitCount` plus the count-based lower-bound theorem
          `counterForSeen_getD_lower_bound`.
        - [x] Add nonzero-budget wrappers
          `counterForSeen_getElem?_ne_zero_of_count_lt` and
          `counterMatchesSeen_getElem?_ne_zero_of_count_lt`.
        - [x] Add `spanVisitInitialFuel` plus the exact counter
          characterization
          `counterForSeen_getElem?_eq_initialFuel_sub_count`.
        - [x] Add initial-fuel nonzero wrappers for the no-prior-visit and
          count-below-initial-fuel cases.
        - [x] Add `SeenPath`, subtree transitivity helpers, and
          `seenPath_visit_mem_ancestor` to relate `seen` entries to concrete
          ancestor nodes and spans.
        - [x] Prove `seenPath_nodeSpan_not_mem_of_minimal`, separating the
          no-cycle part of admissibility from the remaining budget argument.
        - [x] Add direct-child span arithmetic helpers for contained spans and
          strict same-tag span shrinkage.
        - [x] Instantiate the count/default hypotheses from the
          same-span-repeat exclusion and nested-span facts along a valid tree
          path.
          Added `SubtreeSpan`,
          `minimal_valid_tree_same_tag_proper_subtreeSpan_leaves_length_lt`,
          `seenPath_subtreeSpan_count_add_leaves_lt_initialFuel`, and
          `seenPath_count_lt_initialFuel`.
      - [x] Prove `minimal_valid_tree_admissible_with` and the full-span
        wrapper `minimal_valid_tree_admissible`.
    - [x] Use `exists_minimal_valid_tree_of_derives`,
      `minimal_valid_tree_admissible`, and
      `gen_complete_exists_of_admissible_valid_tree` to prove
      `gen_complete_exists`.

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

## `ParserCombinators/CFG.lean`

- [x] Replace `ParseTree.exists_Valid_tree_of_derives` with a theorem.
  This axiom is the reverse direction of `ParseTree.derives_of_Valid_tree`:
  from a derivation `cfg.derives [Symbol.nonterm n] terminals`, construct a
  valid parse tree rooted at `n` with those leaves.  The planned proof uses a
  stronger forest theorem over arbitrary sentential forms.
  - [x] Add the forest representation layer needed for the stronger theorem:
    - `ParseTree.forestLeaves`
    - `ParseTree.ForestPairValid`
    - `ParseTree.ForestValid`
    - `ParseTree.exists_forest_of_terminals`
    - `ParseTree.exists_Valid_tree_of_singleton_forest`
  - [x] Prove a yield decomposition lemma:
    every `cfg.yields v u` replaces one `Symbol.nonterm n` in a prefix/suffix
    context by some `rhs ∈ cfg.rules n`.
  - [x] Prove the reverse-step forest constructor:
    from a valid forest for `pre ++ rhs ++ post`, build a valid forest for
    `pre ++ [Symbol.nonterm n] ++ post` by wrapping the `rhs` subforest in a
    `ParseTree.Node`.
    - [x] Prove the split-form constructor
      `ParseTree.ForestValid_reverse_step_explicit`, assuming separate valid
      forests for `pre`, `rhs`, and `post`.
    - [x] Prove or reuse list/forest splitting lemmas that decompose a valid
      forest for `pre ++ rhs ++ post` into the split-form inputs.
  - [x] Induct over `cfg.derives sentential terminals` to construct a valid
    forest, then specialize to `[Symbol.nonterm n]`.

## `ParserCombinators/Lemmas.lean`

- [x] Replace `memoize_induction` with a theorem.
  - [x] Add the proved guarded well-founded counter induction skeleton
    `memoize_counter_induction`.
  - [x] Add whole-memo union preservation for the cache invariant:
    `memo_sound_sup`, `memo_bounded_sup`, and `memo_wellFormed_sup`.
  - [x] Add whole-memo preservation for the cache-miss branch of
    `memoizeStep`.
  - [x] Combine cache-hit and cache-miss preservation into one
    `memoizeStep` invariant theorem.
  - [x] Add the reverse start-state exposure lemma
    `mem_body_of_memoize_startState_mem`.
  - [x] Factor the generated one-step proof into `gen'_sound_bounded`.
  - [x] Refactor `Gen.gen_sound` to use `memoize_counter_induction`.
  - [x] Delete `Lemmas.memoize_induction`.

  The route that removed the axiom uses exact-counter induction over fresh
  `runParser` executions.  The memo-cache preservation lemmas remain useful for
  the later state-aware cleanup, but `gen_sound` no longer depends on the broad
  arbitrary-predicate memoization axiom.

- [ ] Replace `runParser_sup_eq_sup_runParser` with a theorem.
  - [x] Prove the one-sided left membership theorem `mem_runParser_sup_left`.
    This is axiom-free because `Parser.orElse` runs the left parser first and
    `joinUnderCache` preserves its results.
  - [x] Refactor `Gen.complete_of_sup_left` to use
    `mem_runParser_sup_left`, removing one dependency on the broad sup axiom.
  - [ ] Refine or replace the remaining right/full-equivalence uses.  The
    generic full statement is suspect for arbitrary embedded parsers because
    the right parser can observe memo state produced by the left parser.
    - [x] Run the repo-local axiom-adjustment review for the broad sup axiom.
      The review confirmed the state-insensitive equivalence is not generally
      provable because `Parser.orElse` runs the right branch after the left
      branch's memo state.
    - [x] Prove the raw state-aware parser-level replacement facts:
      - `parser_orElse_fst_eq_unionSup`
      - `mem_parser_orElse_iff`
    - [x] Prove the state-aware right-side preservation lemmas:
      - `mem_parser_orElse_right_after_left_of_mem`
      - `mem_runParser_sup_right_after_left_of_mem`
    - [x] Prove the runParser-level state-aware replacement iff:
      - `mem_runParser_sup_iff_after_left`
    - [x] Add Gen-side state-aware wrappers:
      - `sound_of_sup_sound_after_left`
      - `bounded_of_sup_bounded_after_left`
      - `complete_of_sup_right_after_left`
    - [x] Refactor the Gen-side state-aware wrappers to use
      `mem_runParser_sup_iff_after_left`.
    - [x] Add arbitrary-memo lower-level replacement facts:
      - `mem_lower_sup_left`
      - `mem_lower_sup_right_after_left_of_mem`
      - `mem_lower_sup_or`
      - `mem_lower_sup_iff_after_left`
    - [x] Add Gen-side lower-level sound/bounds wrappers:
      - `lower_sound_of_sup_sound_after_left`
      - `lower_bounded_of_sup_bounded_after_left`
    - [ ] Thread a generalized soundness/boundedness/completeness invariant
      over an explicit memo state, or prove a cache-coherence theorem for the
      generated parsers, before replacing `complete_of_sup_right` and the
      remaining full-sup uses.

- [x] Remove the active `runParser_map` axiom from the proof surface.
  - [x] Add the shallow `Parser` projection helper `parser_map_fst_eq`,
    showing that mapping an embedded parser maps only its result map and
    preserves the state-threading structure.
  - [x] Prove map state-preservation helpers:
    - `mstateT_reader_map_snd_eq`
    - `parser_map_snd_eq`
  - [x] Prove state-parametric embedded parser map membership helpers:
    - `mem_parser_map_of_mem`
    - `mem_parser_map_exists_of_mem`
  - [x] Prove lifted embedded parser map membership helpers without using
    the broad bind axiom:
    - `mem_runParser_lift_map_of_mem`
    - `mem_runParser_lift_map_exists_of_mem`
  - [x] Prove the List-specific forward membership theorem
    `mem_runParser_map_of_mem` without the bind axiom, via the state-aware
    lower-level theorem `mem_lower_map_of_mem`.
  - [x] Prove the List-specific reverse membership theorem
    `mem_runParser_map_exists_of_mem` without the bind axiom, via the
    state-aware lower-level theorem `mem_lower_map_exists_of_mem`.
  - [x] Refactor Gen completeness map construction (`runParser_map_complete`
    and `terminal'_complete`) to use `mem_runParser_map_of_mem` instead of
    the broad `runParser_map` equivalence axiom.
  - [x] Refactor Gen soundness/boundedness map destructors to use
    `mem_runParser_map_exists_of_mem` instead of the broad `runParser_map`
    equivalence axiom.
  - [x] Delete the unused generic `runParser_map` axiom and its
    `runParser_map_getElem?_eq` helper after sub-agent review.  The old
    generic equivalence theorem remains unproved and is no longer part of the
    active axiom surface; current downstream code only needs the narrower
    List-membership theorems above.

- [x] Replace `runParser_pure` with a theorem.
  - [x] Add `mem_runParser_pure_iff` as the List-membership form needed by
    terminal and bind semantics proofs.
  - [x] Add `runParser_pure_getD` as the direct List-result form used by
    later parser semantics proofs.

- [x] Replace `mem_runParser_terminal_iff` with a theorem.
  This List-specific terminal semantics axiom was added as the narrow primitive
  fact needed to prove `terminal'_sound`.

- [ ] Replace `mem_runParser_bind_iff_eq_bind_mem_runParser` with a theorem.
  There are two declarations in the file: an older commented-out statement
  marked incorrect, and the current list-membership statement used downstream.
  The current statement should be proved or refined until it is provable.
  - [x] Add `joinUnderCache` membership preservation helpers:
    - `joinUnderCache_snd_eq`
    - `joinUnderCache_snd_val_eq_of`
    - `traversable_foldl_joinUnderCache_snd_val_eq_of_forall`
    - `list_foldl_traversable_joinUnderCache_snd_val_eq_of_forall`
    - `mem_joinUnderCache_left`
    - `mem_joinUnderCache_right`
    - `mem_joinUnderCache_or`
    - `mem_traversable_foldl_joinUnderCache_of_acc`
    - `mem_traversable_foldl_joinUnderCache_of_head`
    - `mem_traversable_foldl_joinUnderCache_of_split`
    - `mem_traversable_foldl_joinUnderCache_or_action`
    - `mem_list_foldl_traversable_joinUnderCache_of_acc`
    - `mem_list_foldl_traversable_joinUnderCache_of_split`
    - `mem_list_foldl_traversable_joinUnderCache_or_group`
    - `mem_list_foldl_traversable_joinUnderCache_or_action`
    - `mem_lower_return_iff`
    - `mem_traversable_foldl_lower_return_of_mem`
    - `mem_list_foldl_lower_returns_of_resultMap`
    - `mem_bindContinue_return_of_mem`
    - `mem_bindContinue_of_action_mem`
    - `mem_bindContinue_exists_action`
    - `bindActions_action_origin`
    - `bindActions_action_split_origin`
    - `mem_bindContinue_exists_getElem_action_mem`
    - `bindActions_forall₂_snd_val_eq`
    - `bindContinue_snd_val_eq_of_forall`
    - `bindActionPrefix_snd_val_eq_of_forall`
    - `parser_bind_fst_eq_bindContinue`
    - `parser_bind_snd_val_eq_bindRun`
    - `bindRun_snd_eq_bindContinue`
    - `parser_bind_snd_val_eq_of_forall`
    - `lower_map_snd_val_eq`
    - `mem_lower_bind_of_action_mem`
    - `mem_lower_bind_of_action_exists_mem`
    - `mem_lower_bind_of_getElem_action_mem`
    - `mem_lower_bind_exists_getElem_action_mem`
    - `mem_lower_map_of_mem`
    - `mem_lower_map_exists_of_mem`
    - `mem_lower_cons_map_exists_of_cons`
    - `not_mem_lower_cons_map_nil`
    - `mem_lower_traverse_preserves_length`
    - `mem_lower_traverse_cons_tail_exists_of_cons`
    - `not_mem_lower_traverse_cons_nil`
    - `mem_lower_traverse_complete_cons_of_bind_getElem_action_mem`
    - `runParser_bind_fst_eq_bindContinue`
    - `mem_runParser_bind_of_action_mem`
    - `mem_runParser_bind_of_action_exists_mem`
    - `resultMap_toList_value_split_witness`
    - `mem_runParser_bind_of_getElem_action_mem`
    - `mem_runParser_bind_exists_getElem_action_mem`
    - `mem_parser_bind_return_of_mem`
    - `mem_lower_lift_of_mem`
  - [x] Remove the accidental `DecidableEq` requirement on the hidden pivot
    type from `bindActions_forall₂_snd_val_eq` and
    `bindContinue_snd_val_eq_of_forall`.  This keeps the state-preservation
    layer aligned with `Parser.bind`, whose pivot parser does not require a
    decidable result type, and is needed before these lemmas can be used in
    induction over `ParserM.Bind`.
  - [x] Remove the same accidental hidden-pivot `DecidableEq` requirement from
    the parser/lower bind action helpers, so `ParserM.Bind` induction can use
    them for arbitrary embedded pivot parsers.
  - [x] Refactor the generic map consumers away from the old bind axiom:
    `mem_runParser_map_of_mem` and `mem_runParser_map_exists_of_mem` now use
    the state-aware lower map theorems.
  - [x] Use the join helpers to prove the lower/lift membership law for
    `ParserM.lift`, then use that as a base component for the bind theorem.
  - [x] Generalize the bind membership layer from `runParser`/`startState` to
    arbitrary memo states with the `mem_lower_bind_*` theorems.  The existing
    `mem_runParser_bind_*` theorems now delegate to these implementation-shaped
    facts.
  - [x] Add split-action extractors for the real bind execution:
    - `mem_lower_bind_exists_action_split_mem`
    - `mem_runParser_bind_exists_action_split_mem`
    - `mem_lower_bind_iff_exists_action_split_mem`
    - `mem_runParser_bind_iff_exists_action_split_mem`
    These expose the concrete result-map split and continuation-prefix memo
    state used by `Parser.bind`, avoiding the state-insensitive list-bind view
    in the old axiom.
    - [x] Run theorem-adjustment review for this replacement direction.  The
      reviewer confirmed that the old `iff` is not salvageable for
      memo-sensitive parsers unless the RHS uses the exact continuation-prefix
      memo state.  The recommended low-level primitive is the exact-prefix
      split theorem above, with traversal-shaped wrappers layered on top.
  - [x] Refactor traversal length preservation away from the old bind axiom:
    `runParser_traverse_preserves_length` now delegates to the arbitrary-memo
    theorem `mem_lower_traverse_preserves_length`.
  - [x] Add the state-aware traversal cons tail/nil decomposition lemmas:
    `mem_lower_traverse_cons_tail_exists_of_cons` and
    `not_mem_lower_traverse_cons_nil`.
    These expose tail execution under the actual continuation memo state.
    A stronger theorem claiming that the head result appears in
    `head.lower` under the original memo state is not valid for arbitrary
    `ParserM.Bind`, because reassociated bind continuations can change the
    memo prefix before later head alternatives run.
      - [x] Add the exact-prefix traversal completeness constructor
    `mem_lower_traverse_complete_cons_of_bind_getElem_action_mem`.  This is
    the checked replacement shape for consing through a `ParserM.Bind` head:
    callers must prove the full continuation action under the memo prefix
    actually used by `Parser.bind`, rather than reusing a `runParser` proof
    from `startState`.
      - [x] Add a generated-parser-friendly bind-return traversal
        decomposition:
        - `mem_lower_traverse_cons_bind_return_exists_head_tail`
        - `mem_runParser_traverse_cons_bind_return_exists_head_tail`
        This exposes the primitive head result for parsers of shape
        `ParserM.Bind p (fun a => ParserM.Return (f a))` while still returning
        the tail membership under the actual continuation memo state.  A more
        generic theorem claiming head membership in `head.lower` under the
        original memo state is not valid without a memo-prefix equivalence,
        because previous continuation actions can update the cache before the
        current head alternative is observed.
      - [x] Add traversal-shaped lift-head wrappers:
        - `mem_lower_traverse_cons_lift_exists_head_tail`
        - `mem_runParser_traverse_cons_lift_exists_head_tail`
        These are the sound version of the head/tail decomposition for lifted
        primitive heads.  Recursive memoized heads still require either a
        memoize-specific bridge or the broader coherent/reachable memo-state
        invariant.
      - [x] Add the runParser-level exact-prefix traversal constructor:
        - `mem_runParser_traverse_complete_cons_of_bind_getElem_action_mem`
      - [x] Add the Gen-side continuation-prefix preservation bridge:
        - `bind_action_prefix_memo_wellFormed`
        This proves the exact memo prefix exposed by the bind split theorem is
        well-formed when the pivot parser and continuation family preserve
        well-formed memo states.  It is the preservation half needed before
        lower-state traversal bounds can replace the old `runParser`-only
        traversal theorem.
  - [x] Add the first checked Gen-side state-parametric layer needed by the
    traversal replacement:
    - `lower_sound`
    - `lower_result_bounded`
    - `sound_of_lower_sound`
    - `result_bounded_of_lower_result_bounded`
    - `lower_terminal'_result_bounded`
    - `lower_failure_empty`
    - `lower_failure_sound`
    - `lower_failure_bounded`
    The existing `terminal'_bounded`, `failure_sound`, and `failure_bounded`
    now factor through the arbitrary-memo versions.
  - [x] Add the first checked Gen-side memo-state preservation layer needed by
    state-aware sup/traversal replacement:
    - `lower_memo_wellFormed`
    - `lower_map_memo_wellFormed`
    - `lower_failure_memo_wellFormed`
    - `lower_terminal'_memo_wellFormed`
    This uses the smaller checked lift-state lemmas in `Lemmas.lean`:
    `bindContinue_return_snd_val_eq`, `lower_lift_snd_val_eq`, and
    `terminalPrimitive_snd_val_eq`.
  - [x] Add the checked state-threading stack for sequencing in `Gen.lean`:
    - `joinUnderCache_memo_wellFormed`
    - `traversable_foldl_joinUnderCache_memo_wellFormed`
    - `list_foldl_traversable_joinUnderCache_memo_wellFormed`
    - `bindContinue_memo_wellFormed`
    - `parser_bind_memo_wellFormed`
    - `lower_bind_constructor_memo_wellFormed`
    - `lower_lift_memo_wellFormed`
    A fully generic `ParserM.bind` preservation theorem would require the
    lower/composition law for arbitrary embedded parser terms, so the checked
    layer is phrased around the concrete `ParserM.Bind`/`ParserM.lift`
    constructors needed by generated terminals and memoized calls.
  - [x] Add checked state-aware alternative preservation in `Gen.lean`:
    - `parser_pure_memo_wellFormed`
    - `parser_orElse_memo_wellFormed`
    - `lower_sup_memo_wellFormed`
    This is the preservation-side counterpart of the existing state-aware
    `*_after_left` sup facts and is needed before replacing the remaining
    state-insensitive sup wrappers.
  - [ ] Refactor traversal consumers away from the old state-insensitive bind
    axiom.  This still requires a state-aware traversal invariant, because bind
    continuations run under memo states produced by the pivot parser and by
    earlier continuation actions.
    - [ ] Define the memo-state predicate needed by generated-parser
      traversal proofs.  It should characterize reachable/coherent memo states
      for the exact-counter `memoize` cache, ruling out arbitrary bad cached
      results.
      - [x] Add the initial sound/bounds cache-entry predicates and empty-cache
        lemmas in `Gen.lean`:
        `cachedResultMap`, `memoWithCachedResult`, `resultMap_sound`,
        `resultMap_bounded`, `memo_sound`, `memo_bounded`,
        `memo_wellFormed`, `resultMap_sound_empty`,
        `resultMap_bounded_empty`, `memo_sound_empty`, `memo_bounded_empty`,
        and `memo_wellFormed_empty`.
      - [x] Add cache lookup/projection/preservation lemmas for the
        sound/bounds invariant:
        `cachedResultMap_memoWithCachedResult_self`,
        `cachedResultMap_memoWithCachedResult_ne`,
        `cachedResultMap_eq_of_getElem?_eq_some`,
        `resultMap_sound_of_memo_sound`,
        `resultMap_bounded_of_memo_bounded`,
        `resultMap_sound_of_memo_sound_of_getElem?_eq_some`,
        `resultMap_bounded_of_memo_bounded_of_getElem?_eq_some`,
        `memo_sound_memoWithCachedResult`,
        `memo_bounded_memoWithCachedResult`, and
        `memo_wellFormed_memoWithCachedResult`.
      - [x] Add the inner `ResultMap.unionSup` preservation lemmas:
        `resultMap_sound_sup` and `resultMap_bounded_sup`.
      - [x] Add the per-nonterminal position-map invariant layer:
        `positionMap_sound`, `positionMap_bounded`,
        `positionMap_sound_empty`, `positionMap_bounded_empty`,
        `positionMap_sound_of_memo_sound`, and
        `positionMap_bounded_of_memo_bounded`.
      - [x] Add quotient-transport and position-map union preservation:
        `resultMap_sound_of_quot_eq`,
        `resultMap_bounded_of_quot_eq`,
        `positionMapUnion`,
        `positionMap_sound_sup`, and
        `positionMap_bounded_sup`.
      - [x] Add `memoizeStep` branch lemmas for the returned result-map
        sound/bounds invariant:
        `resultMap_sound_memoizeStep_cache`,
        `resultMap_bounded_memoizeStep_cache`,
        `resultMap_sound_memoizeStep_compute`,
        `resultMap_bounded_memoizeStep_compute`,
        `resultMap_sound_memoizeStep`, and
        `resultMap_bounded_memoizeStep`.
      - [x] Add `memoizeStep` state-shape and cache-hit whole-memo
        preservation facts:
        `memoizeStep_cache_snd_val_eq`,
        `memoizeStep_compute_snd_val_eq`,
        `memo_sound_memoizeStep_cache`,
        `memo_bounded_memoizeStep_cache`, and
        `memo_wellFormed_memoizeStep_cache`.
      - [ ] Extend the predicate with exact-counter reachability/coherence
        facts strong enough to handle cache hits and generated-parser
        completeness under continuation memo states.
    - [ ] Restate the Gen traversal origin/bounds helpers against that
      predicate rather than against fresh `runParser` executions from
      `startState`.
    - [ ] Restate traversal completeness witnesses so recursive child
      completeness is available under the actual continuation memo state, or
      under a proof that this state satisfies the coherent/reachable predicate.

## `ParserCombinators/Memoized.lean`

- [ ] Prove the relevant laws for the `ParserM` monad instance.

- [ ] Add the constrained-monad/lower-lift theorems noted in the comments:
  - [x] `lower_preserves_identity`
  - [ ] `lower_preserves_composition`
  - [ ] `isomorphism_lower_lift`

- [ ] Prove that `ParserM` has the intended `SemilatticeSup` and `OrderBot`
  structure, or replace the TODO with the exact weaker laws actually needed.

- [ ] Replace the cache update TODO with an `alter`-based implementation if it
  still improves the `memoize` code.

- [ ] Prove that `runParser` commutes with the parser combinators.

- [x] Add the extra parser example tests requested by the TODO near
  `funcParser`.
  Added guards for empty input, shifted successful starts, and shifted failed
  starts for both mapped parser examples.

- [x] Implement `memo`.
  Replaced the old arbitrary-tag sketch with a single-parser homogeneous
  wrapper around the real finite-counter `memoize`.

- [x] Implement `memo'`.
  Replaced the old arbitrary-tag sketch with a homogeneous parser-family
  wrapper around the real finite-counter `memoize`.

- [x] Remove the active placeholder theorem `memo_sound`.
  The old statement compared `memo` to `withFuel`; this is a semantic
  fuel/subsumption theorem that needs cache-coherence and counter adequacy
  invariants, not a theorem that follows from the wrapper definition.

- [x] Remove the active placeholder theorem formerly named `memo_complete`.
  That old theorem was a fuel/subsumption completeness claim for the public
  `memo` wrapper and is tracked as future proof work instead of remaining as a
  `sorry`.  The current `Gen.lean` abbreviation named `memo_complete` is a
  different exact-counter cache-entry invariant used by generated-parser
  completeness.
