# CoStar setup and custom benchmarking

These instructions set up the verified CoStar parser with current pinned
versions of OCaml, Rocq, and CoLoR. They also describe the lightweight
custom benchmark harness in `CoStar/benchmarks`; it does not require the
repository's Java/Python evaluation framework.

All commands below assume the current directory is the `CoStar` repository
unless stated otherwise.

## OCaml

The project uses OCaml 4.14.4 with Flambda enabled in the
`4.14.4+flambda` opam switch.

```sh
CFLAGS='-std=gnu17' opam switch create 4.14.4+flambda \
  --packages=ocaml-variants.4.14.4+options,ocaml-option-flambda
eval "$(opam env --switch=4.14.4+flambda)"
```

The explicit C language version is required when building older OCaml
runtime code with GCC 15 or newer, whose default C dialect is GNU C23.

## Rocq

Add the official released-package repository to the switch and install
Rocq with its core version fixed at 9.2.0:

```sh
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install rocq-prover rocq-core=9.2.0
```

`rocq-prover` is an unversioned metapackage, so the release version is
specified on `rocq-core`.

## CoLoR and parser

The original README's `coq-color.1.7.0` only supports Coq 8.10 and 8.11.
Install the renamed Rocq-compatible CoLoR release and the arithmetic
plugin used by the ported proofs:

```sh
opam install rocq-color.1.8.6 rocq-micromega-plugin.1.1.1
```

Build only the verified parser:

```sh
make parser
```

Validate every compiled proof object with `rocqchk`:

```sh
make -C parser validate
```

## Custom benchmark example

The example in `benchmarks/Ab3.v` defines:

```text
S -> a S S | b S S | epsilon
```

The input in `benchmarks/benchmark_ab3.ml` is:

```text
(ab)^3 = ababab
```

Build the extracted native-code parser and run 1,000 timed trials:

```sh
make -C benchmarks
./benchmarks/benchmark_ab3 1000
```

The optional numeric argument is the number of trials; it defaults to
1,000. A run on this machine produced:

```text
grammar: S -> a S S | b S S | epsilon
input:   (ab)^3 = ababab (6 tokens)
result:  Ambig
runs:    1000
median:  4091.024 us
mean:    4514.028 us
min:     2401.114 us
max:     19474.030 us
```

Timings vary with machine load. `Ambig` is the expected result because
the six terminals admit multiple binary-tree decompositions under this
grammar.

The harness partially applies `parse` to the grammar and start symbol
before starting the timer. This computes CoStar's production and closure
maps once; each sample measures only parsing the token list, matching the
method used by the original evaluation driver.

## Near-ambiguity benchmark

The second example in `benchmarks/NearAmbig.v` defines:

```text
S -> a S S c | a S b | epsilon
```

It is tested on:

```text
a^5 b^5 = aaaaabbbbb
```

The `a S S c` alternative creates competing prediction work, but cannot
complete because the input contains no `c`. The only successful derivation
uses `a S b` five times followed by epsilon, so the expected result is the
unambiguous `Accept`.

Build both benchmarks and run this case with 1,000 trials:

```sh
make -C benchmarks
./benchmarks/benchmark_near_ambig 1000
```

A run on this machine produced:

```text
grammar: S -> a S S c | a S b | epsilon
input:   a^5 b^5 = aaaaabbbbb (10 tokens)
result:  Accept
runs:    1000
median:  637.054 us
mean:    666.908 us
min:     484.943 us
max:     2753.973 us
```

As with the first benchmark, one untimed parse warms the code and checks
the result before sample collection. Grammar preprocessing is outside the
timed loop.

To remove generated extraction and native-build artifacts:

```sh
make -C benchmarks clean
```

## Using another grammar and input

Use `benchmarks/Ab3.v` and `benchmarks/benchmark_ab3.ml` as the smallest
working template.

1. Copy `Ab3.v` and give its modules and grammar definition a new name.
2. Define one constructor for each terminal and nonterminal.
3. Implement `compareT`, `compareNT`, `showT`, and `showNT` following the
   finite pattern matches in `Ab3.v`.
4. Write productions as a Rocq list of `(nonterminal, rhs)` pairs:

   ```coq
   Definition myGrammar : grammar :=
     [ (Start, [T TokA; NT Start])
     ; (Start, [])
     ].
   ```

   `T x` denotes a terminal, `NT x` a nonterminal, and `[]` is epsilon.
5. Keep a second unused nonterminal constructor when the grammar has only
   one real nonterminal. This prevents Rocq extraction from erasing the
   singleton type; `ExtractionSentinel` in `Ab3.v` is the example.
6. Keep `Separate Extraction` and an extraction output directory. This
   is required because CoLoR dependencies cannot be handled by Rocq's
   monolithic extraction command.
7. In the OCaml driver, represent each token as
   `(terminal_constructor, literal_as_char_list)`. For example:

   ```ocaml
   let input = [ (A, ['a']); (B, ['b']) ]
   ```

8. Alias the extracted parser module and partially apply it outside the
   timing loop:

   ```ocaml
   module Parser = Grammar.PG.ParserAndProofs.PEF.PS.P
   let parse_input = Parser.parse Grammar.myGrammar Start
   let result = parse_input input
   ```

9. Add or adapt a Makefile/Dune executable target following
   `benchmarks/Makefile` and `benchmarks/dune`, then run the resulting
   executable with the desired trial count.

For comparable measurements, use a release/native build, perform at least
one untimed call before collecting samples if warm-cache behavior is
desired, keep grammar preprocessing outside the timing loop, report the
trial count and summary statistic, and run on an otherwise idle machine.
