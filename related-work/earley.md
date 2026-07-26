# Earley Parser (Isabelle)

## What this directory contains

`related-work/Earley_Parser` is the AFP `Earley_Parser` session by Martin
Rau. Its eight original theory files and document sources are byte-for-byte
identical to the AFP release for Isabelle2025-2 (2026-02-06). The local `ROOT`
has been extended with the benchmark session described below.

The session has the following layers:

- `Limit.thy`, `CFG.thy`, and `Derivations.thy` provide the CFG and derivation
  foundations, adapted from the AFP `LocalLexing` entry.
- `Earley.thy` defines abstract Earley items and proves soundness,
  completeness, correctness, and finiteness.
- `Earley_Fixpoint.thy` gives a set/fixpoint implementation and connects it to
  the abstract specification.
- `Earley_Recognizer.thy` implements the executable list-of-bins recognizer.
  Its entries carry `Null`, predecessor (`Pre`), or predecessor/reduction
  (`PreRed`) pointers. `Earley\<^sub>L` constructs the bins and `recognizer`
  tests whether the final bin contains a finished item.
- `Earley_Parser.thy` uses those pointers to construct a parse tree with
  `build_tree` and proves its correctness.
- `Examples.thy` defines grammars with linear, quadratic, and cubic behavior,
  evaluates bin/pointer counts, and checks Scala code generation. A larger
  JSON example is present but commented out.
- `benchmark/Benchmark.thy` is a separate, executable benchmark harness. It
  currently contains the ambiguous epsilon-free grammar
  `S -> S S | a | b` and input `(ab)^3`.
- `ROOT` declares the `Earley_Parser` session over Isabelle/HOL and
  `HOL-Library`, with a 600-second theory timeout and a LaTeX document. It also
  declares the small child session `Earley_Benchmark`, so a benchmark can be
  rebuilt without rechecking the complete proof development.

This is an Isabelle theory development, not a standalone command-line parser.
Building the session checks the proofs, evaluates the active `value` commands,
and runs the Scala `export_code` check in `Examples.thy`.

## Required tooling

- **Isabelle2025-2 for Linux x86-64.** The platform bundle is self-contained:
  it includes the required Java runtime, Poly/ML, Isabelle/HOL, Scala, and
  `HOL-Library`. A separate AFP checkout is not needed because this directory
  contains the complete entry.
- **TeX Live with LuaLaTeX and BibTeX** is needed only to generate the optional
  proof-document PDF. It is not needed for proof checking.

Installed on this machine:

- Isabelle: `/home/emre/.local/opt/Isabelle2025-2`
- Command: `/home/emre/.local/bin/isabelle` (already on `PATH`)
- Isabelle download SHA-256:
  `a20a507bc7c1270d8be96a9f3fbec06345387789d2dc2c4d3df6260d47bfb33c`
- PDF tools: `/usr/bin/lualatex`, `/usr/bin/pdflatex`, and `/usr/bin/bibtex`

The Isabelle distribution is available from the
[official Isabelle download page](https://www.cl.cam.ac.uk/research/hvg/Isabelle/installation.html).
The matching source release is on the
[AFP Earley Parser page](https://isa-afp.org/entries/Earley_Parser.html).

## Build and run

Run these commands from the repository root:

```sh
isabelle version
isabelle build -v -D related-work/Earley_Parser
```

The expected version is `Isabelle2025-2`. A successful build ends with
`Finished Earley_Parser`. On this machine a clean proof build used 8 threads
and took about 29 seconds.

To force a clean build and generate the proof PDF plus browsable HTML:

```sh
isabelle build -c -v -P : -o document=pdf -D related-work/Earley_Parser
```

The generated outputs are:

- `~/.isabelle/Isabelle2025-2/browser_info/AFP/Earley_Parser/index.html`
- `~/.isabelle/Isabelle2025-2/browser_info/AFP/Earley_Parser/document.pdf`

The `-c` matters when a non-document build is already cached: it ensures the
document is regenerated. The full clean proof, PDF, and presentation build was
verified successfully on this machine.

For interactive evaluation, open `Examples.thy` in Isabelle/jEdit with the
correct session:

```sh
isabelle jedit \
  -d related-work/Earley_Parser \
  -l Earley_Parser \
  related-work/Earley_Parser/Examples.thy
```

Edit or add a `value` command in `Examples.thy` to evaluate a grammar,
recognition result, or parse tree. The main executable expressions are:

```text
Earley\<^sub>L cfg input
recognizer cfg input
build_tree cfg input (Earley\<^sub>L cfg input)
```

## Benchmarking a grammar and input

The reusable harness is
`related-work/Earley_Parser/benchmark/Benchmark.thy`. Run it from the
repository root with:

```sh
related-work/Earley_Parser/benchmark.sh
```

The script cleans and rebuilds only the `Earley_Benchmark` child session. The
much larger `Earley_Parser`, HOL, and `HOL-Library` sessions remain cached. It
then prints the result and the timings stored in Isabelle's session database.
Do not use `isabelle build -f` for this purpose: `-f` also forces dependency
sessions to rebuild.

The current benchmark defines:

```text
S -> S S
S -> a
S -> b

input = [a, b, a, b, a, b] = (ab)^3
```

This grammar accepts every nonempty string over `a` and `b`. It is ambiguous:
a six-token string has the fifth Catalan number, 42, different binary
association trees. The AFP parser stores alternative reduction pointers but
`build_tree` returns one parse tree.

It performs one untimed warm-up and then 1,000 timed calls for each operation:

- `recognizer`: constructs the Earley bins and checks the final bin.
- `parser`: constructs the bins and calls `build_tree`.

The isolated run on this machine produced:

```text
BENCHMARK result accepted=true parse_tree=Some chart_items=63 pointers=83
BENCHMARK recognizer iterations=1000 elapsed_ms=20.868 cpu_ms=20.716 mean_elapsed_us=20.868
BENCHMARK parser iterations=1000 elapsed_ms=26.320 cpu_ms=29.741 mean_elapsed_us=26.320
```

### Important epsilon-production limitation

An earlier benchmark used `S -> a S S | b S S | epsilon`. Although `(ab)^3`
is in that grammar, this implementation reported `accepted=false`. The
executable parser's completeness and correctness theorems assume
`epsilon_free G`, and the list-of-bins implementation does not correctly
saturate that nullable grammar. In particular, a completed epsilon item can
need to advance an item added later to the same bin, after that epsilon item
has already been processed.

Consequently, performance results for grammars containing epsilon productions
measure what this implementation executes, but acceptance and parse-tree
results are not reliable for those grammars. Use epsilon-free grammars when
benchmarking the parser within its verified correctness envelope, or treat
nullable-grammar runs explicitly as limitation/regression tests.

### Supplying another grammar or string

Edit these definitions near the top of `benchmark/Benchmark.thy`:

1. `benchmark_symbol`: add all terminals and nonterminals as datatype
   constructors.
2. `benchmark_rules`: encode each rule as `(lhs, rhs_list)`. Use `[]` for an
   epsilon right-hand side.
3. `benchmark_cfg`: pass the rule list and start symbol to `CFG`.
4. `benchmark_input`: write the token sequence as an Isabelle list.
5. `benchmark_iterations`: increase it when a small input produces timings too
   close to the clock resolution.

For example, `(ab)^n` can be written directly as a token list or generated by:

```isabelle
definition benchmark_input :: "benchmark_symbol list" where
  "benchmark_input = concat (replicate n [a, b])"
```

Replace `n` with a concrete natural number, then rerun `benchmark.sh`. Keep the
grammar and input fixed while comparing implementations, use enough iterations
to obtain stable totals, and report both the recognition result and chart size
alongside timing. A rejected input can be much cheaper than an accepted one.
