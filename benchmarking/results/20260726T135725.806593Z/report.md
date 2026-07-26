# Benchmark analysis: `20260726T135725.806593Z`

The dataset contains 549 planned parser/input rows. Each non-skipped row represents one parser invocation; there are no repetitions or warm-up samples.

## Execution and semantic outcomes

| Suite | Parser | Execution status | Parse outcome | Rows |
|---|---|---|---|---|
| classical | costar | ok | accept | 17 |
| classical | costar | timeout | unknown | 1 |
| classical | earley | ok | accept | 18 |
| classical | lean | ok | accept | 18 |
| earley | costar | ok | accept | 66 |
| earley | costar | ok | parser_error | 99 |
| earley | earley | ok | accept | 165 |
| earley | lean | ok | accept | 144 |
| earley | lean | skipped_after_timeout | unknown | 19 |
| earley | lean | timeout | unknown | 2 |

## Completion and timeout frontiers

| Suite | Grammar | Parser | Largest completed input | First timeout input | Skipped later inputs |
|---|---|---|---|---|---|
| classical | A1 | costar | 41 | 161 | 0 |
| classical | A1 | earley | 161 | — | 0 |
| classical | A1 | lean | 161 | — | 0 |
| classical | C1 | costar | 511 | — | 0 |
| classical | C1 | earley | 511 | — | 0 |
| classical | C1 | lean | 511 | — | 0 |
| classical | P1 | costar | 512 | — | 0 |
| classical | P1 | earley | 512 | — | 0 |
| classical | P1 | lean | 512 | — | 0 |
| classical | P2 | costar | 512 | — | 0 |
| classical | P2 | earley | 512 | — | 0 |
| classical | P2 | lean | 512 | — | 0 |
| classical | R1 | costar | 257 | — | 0 |
| classical | R1 | earley | 257 | — | 0 |
| classical | R1 | lean | 257 | — | 0 |
| classical | R2 | costar | 513 | — | 0 |
| classical | R2 | earley | 513 | — | 0 |
| classical | R2 | lean | 513 | — | 0 |
| earley | cfg1 | costar | 65 | — | 0 |
| earley | cfg1 | earley | 65 | — | 0 |
| earley | cfg1 | lean | 39 | 41 | 12 |
| earley | cfg2 | costar | 65 | — | 0 |
| earley | cfg2 | earley | 65 | — | 0 |
| earley | cfg2 | lean | 65 | — | 0 |
| earley | cfg3 | costar | 65 | — | 0 |
| earley | cfg3 | earley | 65 | — | 0 |
| earley | cfg3 | lean | 65 | — | 0 |
| earley | cfg4 | costar | 65 | — | 0 |
| earley | cfg4 | earley | 65 | — | 0 |
| earley | cfg4 | lean | 65 | — | 0 |
| earley | cfg5 | costar | 65 | — | 0 |
| earley | cfg5 | earley | 65 | — | 0 |
| earley | cfg5 | lean | 49 | 51 | 7 |

## Cross-parser acceptance checks

No disagreement was found among parsers that reported a known Boolean acceptance result for the same input.

## Parser, process, and timeout diagnostics

| Suite | Grammar | Parser | Status | Kind | Rows | First input | Last input | Detail |
|---|---|---|---|---|---|---|---|---|
| classical | A1 | costar | timeout | timeout | 1 | classical.A1.large | classical.A1.large | no RESULT within 60 seconds |
| earley | cfg1 | costar | ok | left_recursion | 33 | earley.cfg1.n001 | earley.cfg1.n065 | PredictionError (SpLeftRecursion 0) |
| earley | cfg1 | lean | timeout | timeout | 1 | earley.cfg1.n041 | earley.cfg1.n041 | no RESULT within 60 seconds |
| earley | cfg4 | costar | ok | left_recursion | 33 | earley.cfg4.n001 | earley.cfg4.n065 | PredictionError (SpLeftRecursion 0) |
| earley | cfg5 | costar | ok | left_recursion | 33 | earley.cfg5.n001 | earley.cfg5.n065 | PredictionError (SpLeftRecursion 0) |
| earley | cfg5 | lean | timeout | timeout | 1 | earley.cfg5.n051 | earley.cfg5.n051 | no RESULT within 60 seconds |

## Direct timing ratios

| Suite | Grammar | Ratio | Largest shared input | Ratio at that input |
|---|---|---|---|---|
| classical | A1 | costar/earley | 41 | 15.3 |
| classical | A1 | costar/lean | 41 | 0.912 |
| classical | A1 | earley/lean | 161 | 0.0106 |
| classical | C1 | costar/earley | 511 | 16 |
| classical | C1 | costar/lean | 511 | 0.498 |
| classical | C1 | earley/lean | 511 | 0.0311 |
| classical | P1 | costar/earley | 512 | 0.0484 |
| classical | P1 | costar/lean | 512 | 0.000329 |
| classical | P1 | earley/lean | 512 | 0.00679 |
| classical | P2 | costar/earley | 512 | 0.0251 |
| classical | P2 | costar/lean | 512 | 0.000824 |
| classical | P2 | earley/lean | 512 | 0.0328 |
| classical | R1 | costar/earley | 257 | 0.0387 |
| classical | R1 | costar/lean | 257 | 0.000907 |
| classical | R1 | earley/lean | 257 | 0.0235 |
| classical | R2 | costar/earley | 513 | 0.0236 |
| classical | R2 | costar/lean | 513 | 0.000386 |
| classical | R2 | earley/lean | 513 | 0.0164 |
| earley | cfg1 | earley/lean | 39 | 0.000485 |
| earley | cfg2 | costar/earley | 65 | 0.00416 |
| earley | cfg2 | costar/lean | 65 | 0.000192 |
| earley | cfg2 | earley/lean | 65 | 0.0462 |
| earley | cfg3 | costar/earley | 65 | 2.63 |
| earley | cfg3 | costar/lean | 65 | 0.476 |
| earley | cfg3 | earley/lean | 65 | 0.181 |
| earley | cfg4 | earley/lean | 65 | 0.000622 |
| earley | cfg5 | earley/lean | 49 | 1.42e-05 |

Each displayed ratio uses the single observations at the largest input completed by both parsers. `ratios.csv` contains every direct per-input ratio.
