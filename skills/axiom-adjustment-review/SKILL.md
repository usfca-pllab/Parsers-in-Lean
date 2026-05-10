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
4. Spawn a sub-agent to review the proposed statement and proof outline.
5. Adjust the axiom only if the sub-agent is satisfied that the statement is coherent and plausibly provable.
6. Record the rationale near the edited axiom when a short comment would prevent future confusion.
7. Run `lake build`.

## Sub-Agent Prompt Shape

Ask the sub-agent for an independent proof-feasibility review.  Include:

- the current axiom statement
- the proposed replacement statement
- the definitions and lemmas the proof outline relies on
- the proof outline
- the specific file path

Do not ask the sub-agent to rubber-stamp the change.  Ask it to identify
missing hypotheses, false directions, problematic equivalences, or a simpler
statement.

## Acceptance Criteria

Proceed with an axiom adjustment only when:

- the replacement is no stronger than needed by downstream code, or the extra
  strength is justified by the semantics;
- the proof outline decomposes into plausible Lean lemmas over existing
  definitions;
- the sub-agent agrees that the statement has a viable theorem path, or gives
  concrete edits that make it viable;
- `lake build` succeeds after the change.

If the sub-agent rejects the proof path, do not adjust the axiom.  Either keep
the original statement or make only the refined version that the sub-agent
finds viable.
