# Future Work

These are suggestions beyond the concrete `TODO`, `sorry`, and `axiom` sites
tracked in `TASKS.md`.

## Semantics And Specifications

- Clarify the intended semantic preorder on parser results.
  `Memoized.subsumed` currently compares `ResultMap`s pointwise via `⊔`.
  Decide whether this is the main refinement relation for soundness,
  completeness, and memoization.

- Decide the final relationship between `memoize`, `memo`, and `memo'`.
  `memoize` is implemented with finite counters; `memo` and `memo'` appear to
  be placeholders for single-parser and parser-family memoization.

- Decide whether `withFuel` and `withFuel'` are only test scaffolding or the
  specification model for memoization correctness.

- Strengthen `Gen.complete`.
  The current definition asks for some tree in the result at position `0?`.
  A stronger statement should likely mention the final input span, tree root,
  validity, and the derivation witness.

## Proof Organization

- Consider carrying more validity information in generated parser results.
  `Gen.gen'` currently builds `ParseTree.Node`s from subtype rules; richer
  result types may simplify soundness.

- Add reusable helper lemmas for `ParseTree.Valid`, especially node length,
  child validity, roots, and CFG rule membership.

- Collect derivation congruence lemmas for completeness proofs.
  Existing lemmas such as `yields_of_append_left` and
  `yields_of_append_right` are useful starting points.

- Relate `CFG.derives`, `CFG.derives_nth`, and parse trees.
  A finite derivation index may be easier to use in executable completeness
  arguments.

- Prove soundness and completeness of `ParseTree.Valid` with respect to
  `CFG.derives`.

## Regression And Examples

- Keep `lake build` passing after each proof step.

- Add small `#guard` examples for generated CFG parsers where evaluation is
  stable.

- Re-enable or replace commented examples in `Memoized.lean` once the stack
  overflow or evaluation behavior is understood.

- Track any newly introduced temporary `axiom` or `sorry` before merging proof
  work.
