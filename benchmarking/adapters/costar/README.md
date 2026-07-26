# CoStar benchmark worker

Build the verified CoStar parser, extract the generic indexed grammar module,
and compile the native worker:

```sh
benchmarking/adapters/costar/build.sh
```

The build runs entirely in the `4.14.4+flambda` opam switch. Start the
persistent worker with:

```sh
benchmarking/adapters/costar/worker.sh
```

The worker accepts one grammar followed by any number of inputs. Its
tab-separated protocol is:

```text
INIT	<grammar_id>	<start_nt_id>	<nt_count>	<term_count>	<rule_count>
RULE	<lhs_id>	<T:id,N:id,...|->
...
END
READY	<grammar_id>

RUN	<case_id>	<terminal_id,...|->
RESULT	<case_id>	<elapsed_ns>	<outcome>	<accepted>	<ambiguity>	<tree_present>	-	<error_kind>	<detail>

STOP
```

Terminal and nonterminal identifiers occupy separate zero-based spaces. A
right-hand side of `-` is epsilon; a `RUN` input of `-` is empty. Fields must
not contain tabs or newlines.

Grammar preprocessing occurs when `parse` is partially applied, before
`READY`. Each `RUN` calls the resulting parser exactly once and measures that
call only. Results use the following canonical semantic fields:

| CoStar result | outcome | accepted | ambiguity | tree_present |
| --- | --- | --- | --- | --- |
| `Accept` | `accept` | `true` | `unique` | `true` |
| `Ambig` | `ambiguous` | `true` | `ambiguous` | `true` |
| `Reject` | `reject` | `false` | `unknown` | `false` |
| `Error` | `parser_error` | `unknown` | `unknown` | `false` |

Both direct and prediction-time left-recursion errors use
`error_kind=left_recursion`. Protocol failures emit a `FATAL` line and exit
nonzero. The launcher attempts to remove the native process's soft stack limit
so deep inputs are governed by the runner's explicit timeout rather than an
incidental shell default.
