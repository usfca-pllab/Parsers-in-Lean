# Memoization Strategies

This note records the design discussion around preserving proper memoization
while making `memoize` coherent enough for soundness and completeness proofs.

## Constraints

- Memoization is the key contribution of this project.  A final design should
  preserve real cache reuse and the intended performance benefits.
- Replacing memoization with proof-friendly recomputation is not acceptable as
  a final implementation strategy.
- Chart parsing, packed forests, or a separate fixed-point chart parser are not
  the intended direction.  The contribution should remain recursive parsing via
  memoization.
- Keep using the existing `Counter τ` map for now.  It is already well-founded,
  and comparing counters componentwise is linear in the grammar/nonterminal
  size.  That comparison cost is acceptable initially and can be optimized
  later.

## Current Problem

The original `memoize` cache was keyed only by `(tag, position)` and reused any
cached result immediately.  That is efficient, but it is not coherent with the
finite recursion counter:

- A result computed with a lower counter can be cached.
- A later call with a higher counter for the same `(tag, position)` can hit the
  lower-counter cache entry.
- The higher-counter call then skips recomputation and can miss parses that
  should be available with more recursion budget.

The temporary recompute-and-union implementation avoids this cache poisoning,
but it does so by giving up the main cache-hit performance benefit.  It is a
proof-coherence stopgap, not the final strategy.

## Option 1.1: Exact-Counter Cache Keys

Key cache entries by the full operational state:

```text
(tag, position, counter)
```

A cache hit is valid only when the requested counter is exactly the same as the
stored counter.

### Theoretical Property

This has the cleanest equivalence theorem:

```text
memoize counter tag position = withFuel counter tag position
```

or, more generally, a direct extensional equivalence between memoized execution
and the non-memoized counter-bounded semantics at the same counter.

### Proof Shape

The proof is comparatively direct:

- cache lookup is exact;
- no result computed under a different counter is reused;
- memoization is observationally transparent relative to `withFuel`;
- recursive calls decrease the counter as before, preserving well-foundedness.

The main invariant is that each stored entry is correct for exactly its stored
counter.

### Performance

This preserves real memoization, but shares less than a dominance-based cache.
Two calls at the same `(tag, position)` but different counters cannot reuse each
other.

Because `Counter τ` is a map, this may create many distinct cache keys in
mutually recursive grammars.  It is still conceptually simple and is likely the
best first proof target if exact equivalence with `withFuel` matters most.

## Option 1.2: Counter-Dominance Cache Reuse

Store the counter used to compute each cached result.  Reuse a cached result
when its counter dominates the requested counter:

```text
cachedCounter >= requestedCounter
```

For `Counter τ`, this comparison is componentwise over grammar tags.  The cost
is linear in the number of nonterminals, which is acceptable for now.

### Theoretical Property

This does not generally preserve exact equivalence to `withFuel requested`.
Instead, the expected property is a sandwich:

```text
withFuel requestedCounter
  <= memoize requestedCounter
  <= withFuel cachedCounter
```

for some cached counter that dominates the requested counter.

So `memoize` may produce a sound superset of the exact requested-counter
semantics.  That is acceptable if the public contract is soundness plus
completeness, not exact agreement with a specific bounded interpreter.

### Proof Shape

This requires monotonicity of the counter-bounded semantics:

```text
counter1 <= counter2 →
withFuel counter1 <= withFuel counter2
```

The cache invariant says each stored result is correct for its stored counter.
A dominance hit is justified by monotonicity.

With full `Counter τ` values, counters can be incomparable.  The cache design
therefore has two variants:

- Store one entry and replace it only when the new counter dominates the old
  counter.
- Store an antichain of maximal counter/result entries for each `(tag,
  position)`.

The one-entry version is simpler but may miss reuse opportunities or need a
policy for incomparable counters.  The antichain version is more complete but
more complex.

### Performance

This is likely better than exact-counter caching when higher-counter calls are
common.  A high-counter result can satisfy lower-counter requests.

The costs are:

- componentwise counter comparison;
- possible antichain management;
- more complex cache invariants.

This is the most promising strategy if we want proper memoization and are
willing to prove a slightly weaker relationship than exact `withFuel`
equivalence.

## Option 2: Saturated Markers

A saturated marker distinguishes an incomplete approximation from a result that
is known complete for some counter.

For example:

```lean
inductive CacheStatus where
  | computing
  | done (counter : Counter τ)
```

A cache entry can then record:

```text
result, status
```

or:

```text
result, completedCounter
```

### Counter-Saturated Version

This version still uses recursive memoization and the existing counter map.
It does not imply chart parsing.

An entry marked `done counter` means the result is complete for that counter.
It can be reused:

- exactly, if using Option 1.1 semantics;
- for lower requested counters, if using Option 1.2 dominance semantics.

This makes the cache invariant more explicit and prevents reusing entries that
were only partially computed.

### Computing Markers

A `computing` marker can prevent nontermination or reentrant recomputation for
the same key.  However, it must be handled carefully:

- returning the current approximation during `computing` is efficient but can
  reintroduce incompleteness unless the algorithm later revisits callers;
- blocking reuse of `computing` entries is simpler semantically but may reduce
  sharing during active recursion;
- treating `computing` as failure is usually too weak for completeness.

For this project, saturated markers seem most useful as metadata on
counter-aware entries, not as a separate fixed-point/chart algorithm.

### Proof Shape

The cache invariant becomes:

```text
done counter result → result is complete and sound for counter
```

Then exact reuse or dominance reuse follows from the chosen strategy.

### Performance

Saturated markers can avoid unsafe cache hits while still preserving real
memoization.  They add bookkeeping but make the implementation more explicit
about which entries are safe to reuse.

## Rejected Direction: Chart/Fixed-Point Parsing

A full chart or worklist fixed-point algorithm could solve some left-recursion
and saturation issues, but it is not aligned with this project goal.  The goal
is verified recursive memoizing parser combinators, not a separate chart parser.

This direction should not guide the near-term implementation plan.

## Implemented Baseline: Option 1.1

The current implementation uses exact-counter cache keys.  The memo table is
indexed by:

```text
tag, (counterKey, position)
```

`counterKey` is an executable key obtained from the existing `Counter τ`
hash-map entries.  This avoids making `memoize` noncomputable.  The tradeoff is
that extensionally equal counters with different internal entry-list order may
miss a cache hit, but that only reduces sharing; it does not allow unsafe reuse.

### Counter-Key Performance Follow-Up

The current implementation rebuilds `counterKey` from the `Counter τ` hash-map
entries on each memoized call.  A direct `Counter τ` cache key is not available
for free because `Std.HashMap` does not provide `BEq` or `Hashable` instances
for itself.

A future optimization should make `Counter` carry an executable memo key or
fingerprint alongside the map:

```lean
structure Counter τ where
  map : Std.HashMap τ ℕ
  key : MemoKey τ
```

Then `Counter.dec` can update both fields incrementally, and `memoize` can use
`counter.key` without rebuilding a list on every lookup.  Defining
`BEq`/`Hashable` directly for a wrapper around `Counter τ` is possible, but it
would still need to inspect or canonicalize the map unless the wrapper stores a
maintained key/fingerprint.

On a cache hit, the result was computed for the same exact counter key and
input position.  On a miss, `memoize` computes the result using the existing
`remaining input + 1` recursive budget rule, stores it under that exact key, and
returns it.

This is the simplest coherent proof target.  Counter-dominance reuse remains a
future optimization if we later want more sharing and are willing to prove the
counter monotonicity/sandwich theorem.
