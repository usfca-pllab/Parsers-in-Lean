# TASKS

This file tracks the active proof-simplification path for
`ParserCombinators/Gen.lean` and `ParserCombinators/Lemmas.lean`.

The current proof is complete, but the main files are still large.  The goal is
proof compression only: preserve the executable parser generator and the
exact-counter memoization design while reducing duplicated proof plumbing.

## Guardrails

- Do not change `gen`, `memoize`, `gen_sound`, `gen_complete`, or
  `gen_correct`.
- Keep `memo_complete` exact-keyed and central.  Cache completeness must remain
  tied to `(Counter.toKey counter, start)`.
- Do not introduce counter subsumption, dominance reuse, same-tag/start reuse,
  proof-only recomputation, chart parsing, or a worklist parser.
- Avoid building a broad parser algebra library.  Add only abstractions needed
  by live generated-parser proof obligations.
- Keep raw implementation details such as `prePairs`, `preValues`, quotient
  transport, and `DHashMap` case splits behind narrow semantic lemmas.
- Run `lake build` after each implemented phase.

## Definition Of Done

- [ ] `lake build` succeeds.
- [ ] `rg -n "\\baxiom\\b|\\bsorry\\b" ParserCombinators` returns no matches.
- [ ] `gen_sound`, `gen_complete`, and `gen_correct` theorem statements are
  unchanged.
- [ ] `gen` and `memoize` definitions are unchanged.
- [ ] `ParserCombinators/Gen.lean` and `ParserCombinators/Lemmas.lean` have a
  meaningful net line-count reduction.
- [ ] Exact-counter cache reuse remains visibly enforced in the completeness
  path.

## Plan

### 1. Add A Narrow State-Preservation Core

Introduce local abbreviations for state preservation through parser execution:

```lean
ActionPreserves Inv act :=
  ∀ memo, Inv memo → Inv ((act memo input).2.val)

ParserPreserves Inv p :=
  ∀ start, ActionPreserves Inv (p start)

LowerPreserves Inv p :=
  ∀ memo, Inv memo → ∀ start,
    Inv (((p.lower start) memo input).2.val)
```

Prove only the live structural lemmas:

- pure
- `joinUnderCache`
- traversable and list folds over `joinUnderCache`
- `Parser.bind`
- `ParserM.Bind`
- `ParserM.lift`
- map state preservation

Instantiate this core for:

- `Inv := memo_wellFormed cfg input`
- `Inv := memo_complete cfg input`

Then replace duplicated `memo_wellFormed` / `memo_complete` state-threading
families where the generic lemmas apply directly.

Do not start with generic `sup`, `orElse`, or arbitrary `foldl` theorem
families.  Add those only if a live call site still needs them after the core
is in place.

### 2. Hide Bind Prefix Plumbing

Keep the existing raw action-split lemma as an implementation detail, but add
one semantic bind-origin lemma:

```lean
mem_lower_bind_exists_split_prefix_inv :
  x ∈ (((ParserM.Bind p k).lower start) memo input).1.getD end_ [] →
  Inv memo →
  ParserPreserves Inv p →
  (∀ a, LowerPreserves Inv (k a)) →
  ∃ split a memoPrefix,
    a ∈ ((p start) memo input).1.getD split [] ∧
    Inv memoPrefix ∧
    x ∈ (((k a).lower split) memoPrefix input).1.getD end_ []
```

Use it to replace downstream uses of:

- `bind_action_prefix_memo_wellFormed`
- `bind_action_prefix_memo_complete`
- `mem_lower_bind_exists_action_split_wf`
- `mem_lower_bind_exists_action_split_complete`

The semantic lemma must keep the exact prefix memo witness needed by downstream
soundness, boundedness, well-formedness, and completeness proofs.  It must not
claim any broader parser equivalence.

### 3. Add HashMap Transport Lemmas

Constrain raw `Std.HashMap` and `Std.DHashMap` reasoning to a few semantic
transport lemmas.

Add narrow helpers for:

- result-map membership/predicate preservation through `unionSup`
- position-map completeness through `positionMapUnion`
- whole-memo completeness through `left ⊔ right`

Refactor these proofs to use the helpers:

- `positionMap_complete_sup`
- `positionMap_complete_of_memo_complete_sup`
- `memo_complete_sup`

After this phase, quotient/getD/DHashMap four-case reasoning should appear in
the transport lemmas only.

### 4. Factor Selected-Rule Completeness

Extract the repeated selected-rule prefix/suffix proof pattern into one helper.

The helper should:

- split `(cfg.rules n).attach.map ...` into `rulePrefix`, selected rule, and
  suffix
- prove the prefix fold preserves `memo_complete`
- define the exact `prefixMemo`
- run selected rule traversal under `prefixMemo`
- transport the selected branch result through the suffix fold

Use this helper in:

- `lower_gen'_complete_of_admissible_rule`
- `resultMap_complete_lower_gen'_memoized_body`, if it still repeats selected
  rule setup after the first refactor

Keep selected rule identity and exact prefix memo visible in theorem
statements.  Do not introduce a broad parser-choice fold library.

### 5. Reassess Generated-Traverse Bundling

Only after the earlier phases land, inspect whether these still duplicate
substantial induction logic:

- `lower_result_bounded_generated_traverse_memoize_guarded`
- `lower_valid_pairs_generated_traverse_memoize_guarded`
- `lower_generated_rule_branch_result_sound_bounded_memoize_guarded`

If duplication remains high, consider one bundled generated-traverse theorem
returning exactly the facts needed by generated-rule soundness:

- bounds
- valid child pairs
- memo well-formed preservation

Do not bundle completeness into this theorem.  Completeness remains on the
separate exact-counter `memo_complete` path.

### 6. Prune After References Disappear

After `Gen.lean` is simplified, use `rg` to find unused helper names and remove
stale wrappers.

Likely low-risk cleanup:

- remaining thin `runParser` mirrors whose lower-state versions are used
  directly
- duplicate local/list helpers, including `mem_bind_cons_map_exists_of_cons`
  and `not_mem_bind_cons_map_nil` if both `Gen.lean` and `Lemmas.lean` still
  define equivalent versions
- stale compatibility wrappers created only to preserve old helper names

Do not remove commented tests or TODO notes unless the underlying issue is
actually resolved.

## Audit Commands

```sh
lake build
rg -n "\\baxiom\\b|\\bsorry\\b" ParserCombinators
rg -n "theorem gen_sound|theorem gen_complete |theorem gen_correct" ParserCombinators/Gen.lean
wc -l ParserCombinators/Lemmas.lean ParserCombinators/Gen.lean
```
