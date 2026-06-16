# Proof Simplification Opportunities

This report records follow-up cleanup after the axiom-removal work. The goal is
to make the now-working proof path easier to maintain without changing the
memoization algorithm or broadening theorem statements unnecessarily.

## Baseline

- `lake build` succeeds on the current `codex-experiment` branch.
- `rg -n "\baxiom\b|\bsorry\b" ParserCombinators` reports no matches, so no
  `axiom` or `sorry` remains under `ParserCombinators`.
- `Gen.lean` now routes generated-parser completeness through the exact-counter
  `memo_complete` path: lower-state parser execution, cache entries keyed by
  `Counter.toKey`, and final instantiation at the public generated-parser
  theorem boundary.

## Simplification Areas

### Guarded generated-traverse helpers

Tags: `[remove-helper]`

Simplification opportunity: the generated-traverse proof area has both guarded
and unguarded memoized variants for soundness, boundedness, valid-pair, and
rule-branch facts. The guarded variants are closer to the active proof path
because they carry the cache well-formedness needed around `memoizeStep`.

Action checklist:

- [ ] Inventory unguarded generated-traverse helpers and their guarded
  counterparts.
- [ ] For each unguarded helper, list the remaining call sites.
- [ ] Move call sites to the guarded helper when the guarded hypotheses are
  already available.
- [ ] Keep an unguarded name only as a thin wrapper if it still improves
  readability at a public or frequently used boundary.
- [ ] Delete unguarded helpers that only preserve stale proof structure.

Stop condition: do not remove a wrapper if doing so forces large unrelated
rewrites of downstream generated-rule proofs.

### Lower-state memo preservation

Tags: `[factor-lemma]`, `[remove-helper]`

Simplification opportunity: the `lower_memo_wellFormed_*` and
`lower_memo_complete_*` traversal families share proof shape. Both run a lowered
parser, thread the later memo state through terminal, failure, bind, traverse,
choice, and memoize cases, then prove that the relevant invariant is preserved.

Action checklist:

- [ ] Compare the well-formedness and completeness traversal proofs case by
  case.
- [ ] Mark the repeated state-threading step where a lower parser run produces a
  later memo state.
- [ ] Draft one narrow state-preservation lemma if it removes duplicated proof
  blocks from both families.
- [ ] Replace local duplicated blocks with the shared lemma in two call sites
  before expanding its use.
- [ ] Remove older helper paths only after the compact lower-state path is the
  only active route.

Candidate helper shape: a generated-parser-specific lemma saying that a lower
run from `memo` to a later memo state preserves the named invariant required by
the current proof, with hypotheses specialized to the generated parser fragment
that actually occurs.

Stop condition: do not generalize this into a fresh-state equivalence theorem
for arbitrary `ParserM`.

### Result-map and position-map transport

Tags: `[factor-lemma]`, `[remove-helper]`

Simplification opportunity: helpers such as
`resultMap_complete_unionSup_left/right`, `positionMap_complete_*`, and nearby
map/union transport lemmas expose `HashMap.getD`, `HashMap.getElem?`, and
`unionSup` details across many generated-parser proof sites.

Action checklist:

- [ ] Group current transport lemmas by the semantic move they perform:
  result-map union, position-map lookup, or map/getD conversion.
- [ ] Identify call sites that only need the semantic statement that
  membership or completeness survives the transport.
- [ ] Introduce one or two semantic wrappers around the implementation-heavy
  hash-map facts.
- [ ] Rename or retire lower-level wrappers that no longer clarify call sites.
- [ ] Keep the raw hash-map lemmas available only inside the transport proofs.

Candidate helper shape: a small theorem at the result-map/position-map boundary
stating that completeness or membership is preserved by the specific union or
lookup transport used by generated parser proofs.

Stop condition: avoid building a broad map algebra library; stop once generated
parser call sites no longer repeat hash-map plumbing.

### `memoize` and `memoizeStep` splits

Tags: `[factor-lemma]`, `[factor-tactic]`

Simplification opportunity: `memoize` proofs repeatedly split on zero and
nonzero counter cases before exposing the relevant `memoizeStep` behavior. The
same local setup is repeated in soundness, boundedness, well-formedness, and
completeness arguments.

Action checklist:

- [ ] Locate repeated zero/nonzero case splits around `memoize`.
- [ ] Separate the nonzero compute path from the zero/failure path.
- [ ] Factor the nonzero path into a small exposure lemma when several proofs
  unfold or apply the same `memoizeStep` facts.
- [ ] Factor repeated tactical setup only after the lemma boundary is clear.
- [ ] Re-run the generated-parser proof sections after each factoring step.

Candidate helper shape: an exposure lemma that states the lower run of
`memoize counter g n` in the nonzero case is the corresponding `memoizeStep`
run, preserving the exact cache key `(Counter.toKey counter, start)`.

Stop condition: keep the exact-counter cache discipline visible; do not replace
same-key reuse with counter subsumption or recomputation.

### Terminal, lift, and failure traversal cases

Tags: `[factor-lemma]`, `[factor-tactic]`

Simplification opportunity: terminal, lift, and failure cases recur in
generated-traverse soundness, boundedness, valid-pair, well-formedness, and
completeness proofs. These cases are small individually, but together they make
the active proof path noisy.

Action checklist:

- [ ] Collect repeated terminal, lift, and failure case blocks from the
  generated-traverse proofs.
- [ ] Extract compact generated-parser-specific case lemmas when the same
  hypotheses and conclusions recur.
- [ ] Prefer local helper lemmas over tactic scripts if the case carries
  semantic facts such as bounds, validity, or memo-state preservation.
- [ ] Use a tactic helper only for pure unfolding/splitting boilerplate.
- [ ] Keep the helpers near the generated-traverse proof area in `Gen.lean`.

Candidate helper shape: a case lemma that discharges one traversal constructor
case while preserving the exact result bound, validity, or memo invariant needed
by the surrounding generated parser proof.

Stop condition: do not hide important parse-position bounds or validity
obligations behind an overly broad automation block.

### Exact-counter lookup transfer

Tags: `[factor-lemma]`, `[factor-tactic]`

Simplification opportunity: exact-counter arguments repeatedly move through
`Counter.toKey`, `getElem?`, and `dec`. Existing counter-congruence lemmas cover
most of the logic, but call sites still repeat the same lookup-transfer setup.

Action checklist:

- [ ] Find repeated lookup-transfer blocks involving `Counter.toKey`,
  `getElem?`, and `dec`.
- [ ] Reuse existing counter-congruence lemmas where they already express the
  needed lookup equality.
- [ ] Add a wrapper only when multiple call sites need the same
  executable-key-after-decrement or admissible-forest lookup transfer.
- [ ] Make the executable counter-key condition explicit in the wrapper
  statement.
- [ ] Replace local rewrite blocks with the wrapper only after checking the
  proof still reads as exact-counter memoization.

Candidate helper shape: a call-site-shaped theorem saying that the relevant
counter lookup or admissible-forest predicate is unchanged under the specific
`Counter.toKey`/`dec` equality used by the generated completeness proof.

Stop condition: do not weaken the key discipline into fuel subsumption,
counter dominance, or proof-friendly recomputation.

### Generated rule folds

Tags: `[factor-lemma]`, `[remove-helper]`, `[factor-tactic]`

Simplification opportunity: generated rule proofs repeatedly thread memo state
through fold prefixes before invoking a selected rule branch or generated
traverse fact. The existing fold-prefix lemmas help, but call sites still carry
substantial prefix/suffix plumbing.

Action checklist:

- [ ] Review fold-prefix lemmas used by generated rule soundness and
  completeness.
- [ ] Mark call sites that manually assemble the prefix memo state, selected
  rule branch, and suffix continuation.
- [ ] Draft a narrower fold-step helper if it packages that recurring setup
  without hiding the selected branch.
- [ ] Replace the bulkiest call sites first and check whether older fold helper
  paths become unused.
- [ ] Delete obsolete helper paths once the compact fold-prefix route is in
  place.

Candidate helper shape: a generated-rule-specific fold lemma that exposes the
memo state after a prefix fold and transports the selected branch result through
the remaining suffix.

Stop condition: do not introduce a broad fold library for all parser choice
combinators; keep the helper tied to generated parser folds.

## Tag Meanings

- `[remove-helper]`: collapse, wrap, or delete stale helper layers after their
  active call sites have moved to the current proof path.
- `[factor-lemma]`: introduce one named semantic fact at the narrow proof
  boundary where repeated reasoning occurs.
- `[factor-tactic]`: factor repeated tactical setup such as unfolding, splitting,
  or rewriting without broadening theorem scope.

## Global Guardrails

- Do not reintroduce broad fresh-state parser algebra lemmas.
- Do not replace exact-counter memoization with proof-friendly recomputation.
- Do not switch to chart parsing, a worklist parser, or another algorithm as a
  substitute for recursive memoization.
- Avoid large refactors that obscure the now-working proof path.
- Add a helper only when it removes real duplication, exposes a recurring
  implementation fact, or discharges a live downstream proof obligation.
