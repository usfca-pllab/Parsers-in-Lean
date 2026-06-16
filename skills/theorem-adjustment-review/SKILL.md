---
name: theorem-adjustment-review
description: Use when Codex needs to adjust, refine, weaken, strengthen, replace, or add public Lean theorem statements in this ParserCombinators repository. Requires a sub-agent check that the proposed theorem statement has a coherent proof path before changing the theorem shape.
---

# Theorem Adjustment Review

## Workflow

Use this skill before editing a public theorem statement or definition-like
theorem contract.

1. Identify why the current statement is insufficient, too strong, or no longer
   matches the definitions.
2. Draft the smallest viable replacement statement.
3. Write a proof outline explaining how the replacement should be proved from
   the existing definitions, helper lemmas, and allowed axioms.
4. Check the compactness criteria below and revise the proposal before review
   if it adds broad scaffolding that is not needed by a live downstream proof.
5. Spawn a sub-agent to review the proposed statement and proof outline.
6. Adjust the theorem statement only if the sub-agent is satisfied that the
   statement is coherent and plausibly provable.
7. Record the rationale near the edited theorem when a short comment would
   prevent future confusion.
8. Run `lake build`.

Proof-body-only edits do not require this workflow.  Local helper lemmas do not
require this workflow unless they become part of the public proof interface.

## Compactness Criteria

The remaining proof work should converge on a small generated-parser
completeness argument rather than a broad parser algebra library.  Before
proposing a theorem statement change, check:

- Prefer generated-parser-specific, lower-state, or exact-prefix theorem
  statements over broad fresh-state equivalences for all `ParserM`.
- Keep `memo_complete` as the central exact-counter cache-completeness
  invariant unless a concrete proof obligation requires a narrower local
  refinement.
- Avoid duplicate theorem families that separately restate the same
  sound/bounded/complete logic.
- Avoid excessive unfolding of `gen'`, `memoizeStep`, `Parser.bind`, or
  `Parser.orElse`; introduce a named helper only when it removes real
  repetition or marks a useful semantic boundary.
- Reject statement changes that make the remaining proof path sprawl into
  parallel theorem families, compatibility wrappers, or repeated tactical
  blocks when one lower-state/generated-parser theorem would suffice.
- If the proof outline repeats the same map/union transport, bind-state
  threading, or parser unfolding in multiple places, ask for that recurring
  fact to be factored before the theorem shape is changed.
- Prefer deleting or retiring stale helper paths over preserving old names with
  surprising new semantics.
- A public theorem statement should become broader only when the broader
  contract is semantically important, not merely to make a local proof easier.

## Sub-Agent Prompt Shape

Ask the sub-agent for an independent proof-feasibility review.  Include:

- the current theorem statement
- the proposed replacement statement
- the definitions and lemmas the proof outline relies on
- the proof outline
- the specific file path
- why the proposal is compact: which live downstream proof needs it, what
  broader theorem it deliberately avoids, and whether any old helper can be
  deleted after the change

Do not ask the sub-agent to approve the change by default.  Ask it to identify
missing hypotheses, false directions, problematic equivalences, or a simpler
statement.  Also ask it to flag repetitive logic, excessive inlining, or a
broader theorem statement than the remaining proof path needs.

## Acceptance Criteria

Proceed with a theorem adjustment only when:

- the replacement is no stronger than needed by downstream code, or the extra
  strength is justified by the semantics;
- the proof outline decomposes into plausible Lean lemmas over existing
  definitions;
- the proposal keeps the proof path compact and avoids broad generic
  infrastructure when a generated-parser-specific theorem would suffice;
- the proposal avoids repetitive proof logic and excessive inlining, or names
  the recurring semantic fact as a helper with a clear downstream use;
- the sub-agent agrees that the statement has a viable proof path, or gives
  concrete edits that make it viable;
- `lake build` succeeds after the change.

If the sub-agent rejects the proof path, do not adjust the theorem statement.
Either keep the original statement or make only the refined version that the
sub-agent finds viable.
