---
name: axiom-adjustment-review
description: Use when Codex needs to adjust, refine, weaken, strengthen, replace, or add Lean axioms, especially in ParserCombinators/Lemmas.lean. Requires a sub-agent check that the proposed axiom version has a coherent theorem-proof path before changing the axiom.
---

# Axiom Adjustment Review

## Workflow

Use this skill before editing an axiom statement.

1. Identify why the current axiom is insufficient or too strong.
2. Draft the smallest viable replacement statement.
3. Write a proof outline explaining how the replacement could later become a theorem.
4. Check the compactness criteria below and revise the proposal before review
   if it adds broad scaffolding that is not needed by a live downstream proof.
5. Spawn a sub-agent to review the proposed statement and proof outline.
6. Adjust the axiom only if the sub-agent is satisfied that the statement is coherent and plausibly provable.
7. Record the rationale near the edited axiom when a short comment would prevent future confusion.
8. Run `lake build`.

## Compactness Criteria

This repository should avoid proof growth that hides the main memoization
argument behind broad generic infrastructure.  Before proposing an axiom
adjustment, check:

- Prefer a generated-parser-specific, lower-state, or exact-prefix statement
  over a broad parser-algebra equivalence.
- Do not replace an unsound fresh-state axiom with another statement that
  implicitly restarts parsers from `startState` when the implementation threads
  memo state.
- Reuse the exact-counter `memo_complete` invariant for cache completeness
  unless a concrete obligation requires a smaller local refinement.
- Avoid adding duplicate sound/bounded/complete variants when one named helper
  can expose the needed fact.
- Avoid excessive unfolding of `gen'`, `memoizeStep`, `Parser.bind`, or
  `Parser.orElse`; prefer a small helper that names the semantic boundary.
- Reject proposals that solve one blocked proof by adding a broad family of
  near-duplicate lemmas when a generated-parser-specific or lower-state helper
  would cover the live obligation.
- If the proof outline repeats the same map/union transport, bind-state
  threading, or parser unfolding in multiple places, ask for that recurring
  fact to be factored before the axiom is changed.
- Delete or stop using stale helper paths instead of preserving old theorem
  names with surprising new meanings.

## Sub-Agent Prompt Shape

Ask the sub-agent for an independent proof-feasibility review.  Include:

- the current axiom statement
- the proposed replacement statement
- the definitions and lemmas the proof outline relies on
- the proof outline
- the specific file path
- why the proposal is compact: which live downstream proof needs it, what
  broader theorem it deliberately avoids, and whether any old helper can be
  deleted after the change

Do not ask the sub-agent to rubber-stamp the change.  Ask it to identify
missing hypotheses, false directions, problematic equivalences, or a simpler
statement.  Also ask it to flag repetitive logic, excessive inlining, or a
broader statement than the remaining proof path needs.

## Acceptance Criteria

Proceed with an axiom adjustment only when:

- the replacement is no stronger than needed by downstream code, or the extra
  strength is justified by the semantics;
- the proof outline decomposes into plausible Lean lemmas over existing
  definitions;
- the proposal keeps the proof path compact and does not introduce broad
  generic infrastructure merely to satisfy one generated-parser obligation;
- the proposal avoids repetitive proof logic and excessive inlining, or names
  the recurring semantic fact as a helper with a clear downstream use;
- the sub-agent agrees that the statement has a viable theorem path, or gives
  concrete edits that make it viable;
- `lake build` succeeds after the change.

If the sub-agent rejects the proof path, do not adjust the axiom.  Either keep
the original statement or make only the refined version that the sub-agent
finds viable.
