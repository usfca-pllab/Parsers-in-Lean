# ParserCombinators

**This repository is work-in-progress!**

Verified parser combinator experiments in Lean 4.  The core contribution is to
provide memoizing parser combinators that can capture context-free languages,
and can be mapped 1:1 to grammars with no restrictions.

Copyright Madison Kuriny, Mehmet Emre. The code in this repository is licensed
under Apache License 2.0 (see LICENSE).

## Structure of the code

The module structure under `ParserCombinators` is below.

### General utilities/definitions/etc.

- `Basic`: a simple set of verified non-memoizing, Parsec-style parser
  combinators.
- `CFG`: Definitions of context-free grammars, derivations, parse trees, and
  helper lemmas.
- `Order`: Structures related to order theory that extend the definitions from
  mathlib.  The core structure is `Semilatticeoid` which captures setoids that
  can be quotiened into a a semilattice.  This allows using lists rather than
  sets in the parsers while maintainging some monotonicity properties needed
  for memoization.
- `Util`: Assorted helper lemmas that extend mathlib.  Most of these pertain to
  sequences or equivalence relations over nested hashmaps.

### Memoization-related modules

- `MState`: **Monotonic state** monad.  This provides a type that acts as a
  state, but updates perform a join operation rather than replacement (akin to
  weak updates from program analysis).  This allows maintaining monotonicity in
  the memoization state transparently.
- `Memoized`: The memoized parser combinators, which is the core programmatic
  contribution in the repository.  We borrow some techniques from the Haskell
  community to make them work over constrained types.  Memoization works over a
  family of parsers by taking a (finite) tag type: the parsers can be indexed
  by tag, and this allows combining all parsers' memoization states together.

  The termination argument for the memoized parser relies on a notion of fuel
  that is tracked per tag using a hash map.  Although the idea is simple, the
  proof in Lean for it is currently rather arcane.
- `Lemmas`: Posited properties/lemmas of the memoized parser combinators.  They
  are used for proving the correctness of the parser generator.  A lot of the
  lemmas are currently axioms, and we are in the process of proving and/or
  refining them.
- `Gen`: Verified parser generator: It transforms a grammar into a family of
  mutually-recursive memoized parsers.

## Development

This project uses Lake with Lean `leanprover/lean4:v4.22.0-rc4`, mathlib, and
aesop.  Build the library with:

```sh
lake build
```
