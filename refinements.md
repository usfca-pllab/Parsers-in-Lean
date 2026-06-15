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
`result_bounded` and lower-state boundedness as parser-specific invariants:

- `terminal'_bounded` proves boundedness for generated terminal parsers.
- `failure_bounded` proves boundedness for failure.
- State-aware join lemmas such as `lower_bounded_of_sup_bounded_after_left`
  prove boundedness while accounting for the memo state threaded through the
  left branch before the right branch runs.
- Generated traversal uses lower-state, generated-parser-specific lemmas such
  as `lower_result_bounded_generated_traverse_memoize` and its guarded variant
  rather than generic fresh-state traversal bounds.

The older generic helpers `runParser_traverse_origin_bounded` and
`runParser_traverse_result_bounds` were retired after theorem-adjustment review.
They depended on the stale state-insensitive bind view and had no remaining
Lean call sites.

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

## `Lemmas.memoize_induction`

Original statement:

```lean
axiom memoize_induction
  (g : ((t : τ) → ParserM (tag := tag) β μ (tag t)) →
      (t : τ) → ParserM (tag := tag) β μ (tag t))
  (p : ((t : τ) → ParserM (tag := tag) β μ (tag t)) → Prop)
  (h_failure : p (fun _ => ⊥))
  (h_induction : ∀ parser, p parser → p (g parser)) :
    p (memoize Counter.empty g)
```

Why this is not sound:

The predicate `p` is arbitrary, but `memoize Counter.empty g` is not a plain
finite iterate of `g` starting from `⊥`.  It is a stateful parser wrapper around
`memoizeStep`, and `memoizeStep` can return cached results from `MemoData`
without running `g`.  A syntactic predicate such as `parser = fun _ => ⊥` can
hold for the base and be preserved by a constant-failure `g`, while failing for
`memoize` under nonempty memo states.

Final replacement:

The proved theorem `memoize_counter_induction` gives the well-founded counter
induction skeleton that follows the implementation recursion:

```lean
theorem memoize_counter_induction
  (g : ((t : τ) → ParserM (tag := tag) β μ (tag t)) →
      (t : τ) → ParserM (tag := tag) β μ (tag t))
  (P : (counter : Counter τ) →
      ((t : τ) → ParserM (tag := tag) β μ (tag t)) → Prop)
  (h_step :
    ∀ counter,
      (∀ t fuel,
        counter[t]? ≠ some 0 →
        P (counter.dec t fuel) (memoize (counter.dec t fuel) g)) →
      P counter (memoize counter g)) :
    P Counter.empty (memoize Counter.empty g)
```

`Gen.gen_sound` now uses this theorem directly.  The proof factors the
one-step generated parser argument into:

- `gen'_sound_bounded`, the existing generated-body soundness/boundedness proof
  for a fixed recursive parser family;
- `mem_body_of_memoize_startState_mem`, the reverse of the start-state
  memoization exposure lemma, showing that from an empty memo state and a
  nonzero counter, any `memoize counter g t` result came from the corresponding
  body parser with `counter.dec t (input.size - start + 1)`.

The broad `memoize_induction` axiom has been deleted.  The separate
memo-cache preservation lemmas for `memoizeStep` remain useful for later
state-aware traversal/cache-coherence work, but they are no longer needed to
justify the top-level `gen_sound` theorem.

## `Lemmas.mem_runParser_bind_iff_eq_bind_mem_runParser`

Original statement:

```lean
axiom mem_runParser_bind_iff_eq_bind_mem_runParser
  [DecidableEq α']
  (parser₁ : ParserM (tag := tag) β List α)
  (parser₂ : α → ParserM (tag := tag) β List α')
  {start end_pos : ℕ}
  {r : List α'}
  {x : α'} :
    ((runParser (parser₁ >>= parser₂) input start).1[end_pos]? = some r ∧
      x ∈ r) ↔
    ∃ split : ℕ, ∃ s : List α,
      (runParser parser₁ input start).1[split]? = some s ∧
      x ∈ s >>= fun x =>
        (runParser (parser₂ x) input split).1[end_pos]?.toList.flatten
```

Why this is not sound:

`Parser.bind` first runs the pivot parser, then folds continuation actions with
`joinUnderCache`.  Each continuation action runs under the memo state produced
by the pivot parser and by earlier continuation actions.  The original axiom
instead restarts every continuation with `runParser`, which uses `startState`.
That loses cache effects and is not faithful for memo-sensitive parsers.

Replacement direction:

Use arbitrary-memo lower-level bind facts that expose the real state threading:

- `mem_lower_bind_of_action_mem`
- `mem_lower_bind_of_action_exists_mem`
- `mem_lower_bind_of_getElem_action_mem`
- `mem_lower_bind_exists_getElem_action_mem`

These facts are proved from `parser_bind_fst_eq_bindContinue`,
`mem_bindContinue_of_action_mem`, `mem_bindContinue_exists_getElem_action_mem`,
and `resultMap_toList_value_split_witness`.  The existing
`mem_runParser_bind_*` helper theorems now delegate to this arbitrary-memo
layer.

The old iff axiom cannot be deleted yet because the generated-parser traversal
lemmas still ask for state-insensitive child memberships.  The next replacement
step is to make traversal soundness/completeness state-aware, or to prove a
cache-coherence invariant strong enough to convert reachable continuation
states back into the required generated-parser semantic facts.

Refinement update:

The generic map membership helpers have now been moved off the old bind axiom.
`Parser.bind` exposes a computational `bindRun` core, and `Lemmas.lean` proves
the state-preservation bridge through:

- `parser_bind_snd_val_eq_bindRun`
- `bindRun_snd_eq_bindContinue`
- `parser_bind_snd_val_eq_of_forall`
- `lower_map_snd_val_eq`
- `bindActions_action_split_origin`
- `bindActionPrefix_snd_val_eq_of_forall`
- `mem_lower_map_of_mem`
- `mem_lower_map_exists_of_mem`
- `mem_lower_cons_map_exists_of_cons`
- `not_mem_lower_cons_map_nil`

The public `mem_runParser_map_of_mem` and
`mem_runParser_map_exists_of_mem` now delegate to these state-aware lower
theorems rather than to `mem_runParser_bind_iff_eq_bind_mem_runParser`.
The `runParser`-level cons/map destructors used by traversal proofs now
delegate to arbitrary-memo lower-level versions, preparing the traversal
proofs for the same state-aware refactor.

Traversal length preservation has also been moved off the old bind axiom.  The
new theorem `mem_lower_traverse_preserves_length` proves the invariant directly
for explicit memo states:

```lean
theorem mem_lower_traverse_preserves_length
  (xs : List (ParserM (tag := tag) β List α))
  (memo : MemoData tag List) (input : Array β)
  (start end_pos : ℕ) (result : List α)
  (h :
    result ∈
      (((List.traverse id xs).lower start) memo input).1.getD end_pos []) :
    result.length = xs.length
```

The existing `runParser_traverse_preserves_length` theorem now follows by
specializing this lower-level statement to `startState`.  The remaining
traversal users in `Gen.lean` still require state-aware origin, bounds, and
completeness-cons replacements.

The first reusable decomposition lemmas for traversal cons are intentionally
weaker than the old bind axiom:

```lean
theorem mem_lower_traverse_cons_tail_exists_of_cons
  (head : ParserM (tag := tag) β List α)
  (tail : List (ParserM (tag := tag) β List α))
  (memo : MemoData tag List) (input : Array β)
  (start end_pos : ℕ)
  (h :
    result_head :: result_tail ∈
      (((head >>= fun a => List.cons a <$> List.traverse id tail).lower start)
        memo input).1.getD end_pos []) :
    ∃ split memo_tail,
      result_tail ∈
        (((List.traverse id tail).lower split) memo_tail input).1.getD end_pos []
```

and

```lean
theorem not_mem_lower_traverse_cons_nil
```

For the completeness direction, the checked constructor is deliberately
implementation-shaped:

```lean
theorem mem_lower_traverse_complete_cons_of_bind_getElem_action_mem
```

It applies when the caller can prove the cons result for the full continuation
action under the exact prefix state that `Parser.bind` computes.  A more
convenient theorem using only `head.lower` membership and a tail proof for all
memo states was rejected by proof search for a semantic reason: in the
`ParserM.Bind` case, reassociation changes the prefix state by running earlier
full continuations, not just earlier head continuations.

The stronger statement one might want for `Gen.lean`, namely that
`result_head` also appears in `(head.lower start) memo`, is not sound for an
arbitrary `ParserM`.  When `head = ParserM.Bind p k`, the reassociated parser
`head >>= continuation` runs previous `k >>= continuation` actions before a
later `k` action, so the memo prefix is different from the prefix used by
`head.lower` alone.  The remaining generated-parser traversal proof should
therefore use either a reachable/coherent memo invariant, or a specialized
structural predicate that is stable under these continuation states.

Initial cache invariant surface:

`Gen.lean` now defines the first sound/bounds layer of that invariant:

- `cachedResultMap`
- `memoWithCachedResult`
- `resultMap_sound`
- `resultMap_bounded`
- `memo_sound`
- `memo_bounded`
- `memo_wellFormed`
- `resultMap_sound_empty`
- `resultMap_bounded_empty`
- `memo_sound_empty`
- `memo_bounded_empty`
- `memo_wellFormed_empty`
- `cachedResultMap_memoWithCachedResult_self`
- `cachedResultMap_memoWithCachedResult_ne`
- `cachedResultMap_eq_of_getElem?_eq_some`
- `resultMap_sound_of_memo_sound`
- `resultMap_bounded_of_memo_bounded`
- `resultMap_sound_of_memo_sound_of_getElem?_eq_some`
- `resultMap_bounded_of_memo_bounded_of_getElem?_eq_some`
- `memo_sound_memoWithCachedResult`
- `memo_bounded_memoWithCachedResult`
- `memo_wellFormed_memoWithCachedResult`
- `resultMap_sound_sup`
- `resultMap_bounded_sup`
- `positionMap_sound`
- `positionMap_bounded`
- `positionMap_sound_empty`
- `positionMap_bounded_empty`
- `positionMap_sound_of_memo_sound`
- `positionMap_bounded_of_memo_bounded`
- `resultMap_sound_of_quot_eq`
- `resultMap_bounded_of_quot_eq`
- `positionMapUnion`
- `positionMap_sound_sup`
- `positionMap_bounded_sup`
- `resultMap_sound_memoizeStep_cache`
- `resultMap_bounded_memoizeStep_cache`
- `resultMap_sound_memoizeStep_compute`
- `resultMap_bounded_memoizeStep_compute`
- `resultMap_sound_memoizeStep`
- `resultMap_bounded_memoizeStep`
- `memoizeStep_cache_snd_val_eq`
- `memoizeStep_compute_snd_val_eq`
- `memo_sound_memoizeStep_cache`
- `memo_bounded_memoizeStep_cache`
- `memo_wellFormed_memoizeStep_cache`

This proves that the empty memo state is a valid starting point for the
sound/bounds part of the future invariant, and that inserting a newly proved
sound/bounded result map preserves that part of the invariant.  The
`memoizeStep` branch lemmas additionally prove that the result map returned by
a cache hit is sound/bounded when the incoming memo table is sound/bounded, and
that a cache miss is sound/bounded when the computed body result is
sound/bounded.  The cache-hit state theorem also proves that a cache hit returns
the original memo table unchanged, so the whole memo sound/bounds invariant is
preserved on that branch.  The compute-state theorem exposes the remaining
obligation exactly: the returned memo table is the body memo table with the new
exact-counter result inserted, unioned with the body memo table.  This is still
not the full exact-counter reachability/coherence condition needed for
generated-parser completeness under continuation memo states, nor does it yet
prove that the compute branch's insertion and union preserve the whole memo
invariant.

The `ResultMap.unionSup` preservation lemmas are the innermost union layer
needed for that compute-branch proof: when two cached result maps are
sound/bounded, their pointwise `unionSup` is sound/bounded.

The position-map predicates lift the same sound/bounds invariant one level up,
from individual result maps to the per-nonterminal map keyed by
`(counterKey, start)`.  The proved layer covers empty position maps, projection
from `memo_sound` / `memo_bounded`, and preservation under the implementation
shaped `positionMapUnion`.  The union proof uses quotient-equality transport
for result maps, since the outer `HashMap.unionSup` facts expose equality in
the quotient by `Std.HashMap.isSetoid`.

## `Memoized.memo` / `Memoized.memo'`

Original sketch:

```lean
def memo
  (g : ParserM (tag := tag) β μ α → ParserM (tag := tag) β μ α) :
    ParserM (tag := tag) β μ α

def memo'
  (g : (τ → ParserM (tag := tag) β μ α) →
       τ → ParserM (tag := tag) β μ α) :
    τ → ParserM (tag := tag) β μ α
```

Why this did not match the implementation:

`memoize` stores cached results in `MemoData tag μ`, whose entries for key `t`
contain values of type `tag t`.  The old sketches attempted to memoize an
arbitrary result type `α` under an unrelated tag family `tag : τ → Type`, so
there is no honest way to implement them with the real memo table.

Replacement:

`memo` and `memo'` now use constant tag families and delegate directly to the
finite-counter `memoize` implementation:

- `memo'` memoizes homogeneous finite parser families.
- `memo` is the single-parser specialization, using `PUnit.{u+1}` as the
  singleton tag index.
- `memo'_eq_memoize` and `memo_eq_memoize` record the definitional
  relationship to `memoize`.

The old `memo_sound` / `memo_complete` fuel-subsumption sketches were removed
as active theorem declarations after theorem-adjustment review.  They require
counter/fuel adequacy plus cache-coherence invariants and should be
reintroduced only when those proof ingredients are available.

## `Lemmas.runParser_sup_eq_sup_runParser`

Original statement:

```lean
axiom runParser_sup_eq_sup_runParser
  : ∀ start : ℕ,
    (runParser (parser₁ ⊔ parser₂) input start).1.EquivQuot
      ((runParser parser₁ input start).1 ⊔
       (runParser parser₂ input start).1)
```

Why this is not sound:

`Parser.orElse` is implemented with `joinUnderCache (r1 pos) (r2 pos)`.
Because `joinUnderCache` sequences through `MStateT`, the right parser runs in
the memo state produced by the left parser.  The original statement compares
against `runParser parser₂ input start`, which runs `parser₂` from
`startState`.  For memo-sensitive parsers these can differ: the right parser
can hit cache entries produced by the left parser.

Replacement direction:

Use state-aware parser-level facts, where the right branch is run after the
left-produced memo state:

```lean
theorem parser_orElse_fst_eq_unionSup
  (p q : Parser (tag := tag) β List α)
  (memo : MemoData tag List) (input : Array β)
  (start : ℕ) :
    ((Parser.orElse p q start) memo input).1 =
      ((p start) memo input).1.unionSup
        ((q start) (↑((p start) memo input).2) input).1

theorem mem_parser_orElse_iff
  (p q : Parser (tag := tag) β List α)
  (memo : MemoData tag List) (input : Array β)
  (start end_pos : ℕ) (x : α) :
    x ∈ ((Parser.orElse p q start) memo input).1.getD end_pos [] ↔
      x ∈ ((p start) memo input).1.getD end_pos [] ∨
      x ∈ ((q start) (↑((p start) memo input).2) input).1.getD end_pos []
```

The corresponding `runParser`-level replacement is now also proved:

```lean
theorem mem_runParser_sup_iff_after_left
  (p q : ParserM (tag := tag) β List α)
  (input : Array β) (start end_pos : ℕ) (x : α) :
    x ∈ (runParser (p ⊔ q) input start).1.getD end_pos [] ↔
      x ∈ (runParser p input start).1.getD end_pos [] ∨
      x ∈ ((q.lower start)
        (↑(((p.lower start) startState input).2)) input).1.getD end_pos []
```

Gen now also has state-aware wrappers:

- `sound_of_sup_sound_after_left`
- `bounded_of_sup_bounded_after_left`
- `complete_of_sup_right_after_left`

The remaining work is to thread state-aware soundness/boundedness/completeness,
or prove the needed generated-parser cache-coherence theorem, so downstream
proofs no longer need the old state-insensitive axiom.
