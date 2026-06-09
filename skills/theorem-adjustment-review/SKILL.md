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
4. Spawn a sub-agent to review the proposed statement and proof outline.
5. Adjust the theorem statement only if the sub-agent is satisfied that the
   statement is coherent and plausibly provable.
6. Record the rationale near the edited theorem when a short comment would
   prevent future confusion.
7. Run `lake build`.

Proof-body-only edits do not require this workflow.  Local helper lemmas do not
require this workflow unless they become part of the public proof interface.

## Sub-Agent Prompt Shape

Ask the sub-agent for an independent proof-feasibility review.  Include:

- the current theorem statement
- the proposed replacement statement
- the definitions and lemmas the proof outline relies on
- the proof outline
- the specific file path

Do not ask the sub-agent to approve the change by default.  Ask it to identify
missing hypotheses, false directions, problematic equivalences, or a simpler
statement.

## Acceptance Criteria

Proceed with a theorem adjustment only when:

- the replacement is no stronger than needed by downstream code, or the extra
  strength is justified by the semantics;
- the proof outline decomposes into plausible Lean lemmas over existing
  definitions;
- the sub-agent agrees that the statement has a viable proof path, or gives
  concrete edits that make it viable;
- `lake build` succeeds after the change.

If the sub-agent rejects the proof path, do not adjust the theorem statement.
Either keep the original statement or make only the refined version that the
sub-agent finds viable.
