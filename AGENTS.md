# AGENTS.md

Guidance for coding agents working in this repository.

## Project Shape

This is a Lean 4/Lake project about verified memoizing parser combinators.
Prioritize these files when building context:

- `ParserCombinators/Memoized.lean`: parser representation, combinators,
  `runParser`, memo tables, recursion counters, and `memoize`.
- `ParserCombinators/Gen.lean`: CFG-to-parser generation and the main
  soundness/completeness proof work.
- `ParserCombinators/Lemmas.lean`: supporting parser algebra and `runParser`
  lemmas, currently including axioms intended to become proofs.

Related background is in `ParserCombinators/CFG.lean`, `MState.lean`,
`Util.lean`, `Order.lean`, and `Range.lean`.

## Build And Check

- Use `lake build` as the default verification command.
- The Lean toolchain is pinned in `lean-toolchain`.
- The project depends on mathlib and aesop through `lakefile.lean`.

## Proof State

The core verification is incomplete.  Expect `sorry` and `axiom` in
`Gen.lean`, `Lemmas.lean`, and `Memoized.lean`.

When changing proofs:

- Prefer replacing axioms with proved lemmas when possible.
- Keep temporary proof helpers close to the module that needs them unless they
  are generally useful.
- Avoid hiding important proof obligations behind broader axioms.
- Preserve existing theorem statements unless the surrounding definitions force
  a sharper statement.

## Proof Compactness

The remaining proof work should stay focused on the generated parser and the
exact-counter memoization argument.  Avoid growing a broad parser algebra
library unless a live proof obligation genuinely needs it.

- Prefer generated-parser-specific, lower-state, or exact-prefix lemmas over
  broad fresh-state equivalences for all `ParserM`.
- Keep `memo_complete` as the central cache-completeness invariant unless a
  narrower local refinement is forced by a concrete goal.
- Avoid repetitive proof logic.  If the same unfolding, split, or map/union
  transport appears several times, introduce one small named helper at the
  semantic boundary and use it directly.
- Avoid excessive inlining of `gen'`, `memoizeStep`, `Parser.bind`, and
  `Parser.orElse` in large proofs.  Name the small fact needed from the
  definition instead of replaying the implementation structure at each call
  site.
- Do not create parallel theorem families that differ only by restating the
  same proof under slightly different wrappers.  Prefer one stronger local
  statement that matches the live generated-parser proof path, then instantiate
  it at the public theorem boundary.
- Keep proof edits proportional to the remaining goal.  When a proof starts to
  require repeated tactical blocks, stop and factor the recurring semantic fact
  into a named lemma instead of copying the block.
- Do not preserve stale helper paths just to keep old names alive.  Once a
  compact lower-state replacement exists, delete or stop using fresh-state
  helpers that encode the wrong abstraction.
- New helper lemmas should either remove real duplication, expose a reusable
  implementation fact, or discharge a live downstream proof.  Otherwise keep
  the proof local.

## Memoization Priority

The key contribution of this project is verified memoization, so changes to
`memoize` must preserve proper cache reuse and the intended performance
characteristics.  Do not replace memoized behavior with proof-friendly
recomputation as a final design.  If cache coherence blocks completeness,
prefer designs that keep efficient reuse, such as fuel-aware cache entries,
saturation markers, or counter-dominance reuse.  Do not switch to chart parsing
or a separate worklist/fixed-point parser as a substitute for recursive
memoization.

The current baseline is exact-counter memoization: cache entries are keyed by
tag, input position, and the executable counter key.  A cached result should be
reused only when the requested counter key is the same.

## Adjusting Axioms

Axioms in `ParserCombinators/Lemmas.lean` may be adjusted when the current
statement blocks progress, but only under this workflow:

- Draft the smallest replacement statement that downstream code needs.
- Sketch a viable proof outline showing how the new axiom could later become a
  theorem from the existing definitions and helper lemmas.
- Use a sub-agent to review the proposed statement and proof outline before
  editing the axiom.  Ask it to look for missing hypotheses, false directions,
  problematic equivalences, or a simpler provable statement.
- Adjust the axiom only when the sub-agent is satisfied, or when its concrete
  corrections have been incorporated.
- Run `lake build` after the change.

Use the repo-local skill at
`skills/axiom-adjustment-review/SKILL.md` for this workflow.

## Adjusting Theorem Statements

Public theorem statements and definition-like theorem contracts may be adjusted
when the current statement no longer matches the implementation, but use the
same review discipline as axiom adjustments:

- Draft the smallest replacement statement.
- Sketch a viable proof outline from existing definitions, helper lemmas, and
  allowed axioms.
- Use a sub-agent to review the replacement before editing the theorem shape.
- Run `lake build` after the change.

Use the repo-local skill at
`skills/theorem-adjustment-review/SKILL.md` for this workflow.

## Coding Conventions

- Follow the existing Lean style: explicit namespaces, small local helper
  definitions, and direct theorem names that describe parser behavior.
- Keep edits scoped.  Do not refactor older experiments in `Basic.lean` or
  example files unless the task explicitly asks for it.
- Use `rg` for searching.
- Do not remove commented tests or TODO notes unless the underlying issue is
  actually resolved.

## Current Hot Spots

- `Lemmas.lean` still contains broad axioms for parser union and bind behavior.
  Each has a narrower state-aware replacement path under construction.
- The active proof path is to thread the existing exact-counter
  `memo_complete` invariant through one lower-state generated-parser
  completeness theorem, instantiate it at `startState` with
  `memo_complete_empty`, and then retire the stale fresh-state traversal and
  choice helpers.
- `Gen.gen_sound` no longer depends on the broad `memoize_induction` axiom; it
  now uses `memoize_counter_induction` plus a start-state memoize exposure
  lemma.  The remaining active axiom dependencies are the state-insensitive
  bind/traverse and sup/choice helper paths.
- `Memoized.memo` and `Memoized.memo'` are thin homogeneous wrappers around the
  implemented finite-counter `memoize`.  Fuel/subsumption correctness for those
  wrappers remains future proof work rather than an active placeholder theorem.
