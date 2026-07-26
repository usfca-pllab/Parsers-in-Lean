# Earley benchmark worker

Build the child Isabelle session:

```sh
benchmarking/adapters/earley/build.sh
```

Then start its persistent, single-threaded worker:

```sh
benchmarking/adapters/earley/worker.sh
```

The wrapper forwards standard input through a private FIFO because Isabelle's
low-level `ML_process` tool reserves and closes its own standard input. This is
transparent to callers: communicate with `worker.sh` through ordinary stdin
and stdout.

The worker uses a tab-separated line protocol. It accepts one or more grammar
initializations, and any number of runs after each successful initialization:

```text
INIT	<grammar_id>	<start_nt_id>	<nt_count>	<term_count>	<rule_count>
RULE	<lhs_id>	<T:id,N:id,...|->
...
END
READY	<grammar_id>

RUN	<case_id>	<terminal_id,...|->
RESULT	<case_id>	<elapsed_ns>	<outcome>	<accepted>	unknown	<tree_present>	chart_items=<n>;pointers=<n>	-	-

STOP
```

Nonterminals and terminals have separate zero-based identifier spaces. An
epsilon right-hand side or empty input is written as `-`. Fields must not
contain tabs or newlines.

The timed operation constructs the bins with `Earley_L` and calls
`build_tree`. Both returned structures are fully constructed by Standard ML's
eager evaluation. Acceptance and metric aggregation consume those structures
afterward, outside the timed region. Grammar construction and protocol parsing
are also outside the timed region.
