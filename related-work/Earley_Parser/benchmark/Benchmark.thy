theory Benchmark
  imports
    "Earley_Parser.Earley_Parser"
    "HOL-Library.Code_Target_Nat"
begin

section \<open>Small reproducible benchmark\<close>

datatype benchmark_symbol = a | b | S

definition benchmark_rules :: "benchmark_symbol rule list" where
  "benchmark_rules = [
    (S, [S, S]),
    (S, [a]),
    (S, [b])
  ]"

definition benchmark_cfg :: "benchmark_symbol cfg" where
  "benchmark_cfg = CFG benchmark_rules S"

lemma benchmark_epsilon_free:
  "\<epsilon>_free benchmark_cfg"
  by (simp add: \<epsilon>_free_def benchmark_cfg_def benchmark_rules_def rhs_rule_def)

definition benchmark_input :: "benchmark_symbol list" where
  "benchmark_input = [a, b, a, b, a, b]"

definition benchmark_bins :: "benchmark_symbol bins" where
  "benchmark_bins = Earley\<^sub>L benchmark_cfg benchmark_input"

definition benchmark_recognizer :: bool where
  "benchmark_recognizer = recognizer benchmark_cfg benchmark_input"

definition benchmark_parser :: "benchmark_symbol tree option" where
  "benchmark_parser = build_tree benchmark_cfg benchmark_input benchmark_bins"

definition run_recognizer :: "benchmark_symbol list \<Rightarrow> bool" where
  "run_recognizer input = recognizer benchmark_cfg input"

definition run_parser :: "benchmark_symbol list \<Rightarrow> benchmark_symbol tree option" where
  "run_parser input =
    (let bins = Earley\<^sub>L benchmark_cfg input
     in build_tree benchmark_cfg input bins)"

definition benchmark_bin_count :: nat where
  "benchmark_bin_count = fold (+) (map length benchmark_bins) 0"

definition benchmark_pointer_count :: nat where
  "benchmark_pointer_count =
    fold (+)
      (map (\<lambda>b. fold (+)
        (map (\<lambda>e. case snd e of PreRed _ ps \<Rightarrow> 1 + length ps | _ \<Rightarrow> 1) b) 0)
      benchmark_bins) 0"

value [code] "benchmark_recognizer"
value [code] "benchmark_bin_count"
value [code] "benchmark_pointer_count"

ML \<open>
  fun repeat_benchmark 0 _ last = last
    | repeat_benchmark n run _ = repeat_benchmark (n - 1) run (run ())

  fun report_benchmark name iterations run initial =
    let
      val _ = run ()
      val ({elapsed, cpu, ...}, result) =
        Timing.timing (fn () => repeat_benchmark iterations run initial) ()
      val elapsed_ms = Time.toReal elapsed * 1000.0
      val cpu_ms = Time.toReal cpu * 1000.0
      val _ =
        writeln ("BENCHMARK " ^ name ^
          " iterations=" ^ string_of_int iterations ^
          " elapsed_ms=" ^ Real.fmt (StringCvt.FIX (SOME 3)) elapsed_ms ^
          " cpu_ms=" ^ Real.fmt (StringCvt.FIX (SOME 3)) cpu_ms ^
          " mean_elapsed_us=" ^
            Real.fmt (StringCvt.FIX (SOME 3))
              (elapsed_ms * 1000.0 / Real.fromInt iterations))
    in result end

  val benchmark_iterations = 1000

  val _ =
    writeln ("BENCHMARK result accepted=" ^
      Bool.toString @{code benchmark_recognizer} ^
      " parse_tree=" ^
      (if Option.isSome @{code benchmark_parser} then "Some" else "None") ^
      " chart_items=" ^
      string_of_int (@{code integer_of_nat} @{code benchmark_bin_count}) ^
      " pointers=" ^
      string_of_int (@{code integer_of_nat} @{code benchmark_pointer_count}))

  val _ =
    report_benchmark "recognizer" benchmark_iterations
      (fn () => @{code run_recognizer} @{code benchmark_input}) false

  val _ =
    report_benchmark "parser" benchmark_iterations
      (fn () => @{code run_parser} @{code benchmark_input}) NONE
\<close>

end
