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

## Coding Conventions

- Follow the existing Lean style: explicit namespaces, small local helper
  definitions, and direct theorem names that describe parser behavior.
- Keep edits scoped.  Do not refactor older experiments in `Basic.lean` or
  example files unless the task explicitly asks for it.
- Use `rg` for searching.
- Do not remove commented tests or TODO notes unless the underlying issue is
  actually resolved.

## Current Hot Spots

- `Gen.gen_sound` is partially proved and depends on traversal/runParser facts
  about child parsers.
- `Lemmas.lean` contains axioms for memoization induction, parser union,
  functor mapping, `pure`, and bind behavior.
- `Memoized.memo`, `Memoized.memo'`, `memo_sound`, and `memo_complete` are
  placeholders separate from the implemented finite-counter `memoize`.
