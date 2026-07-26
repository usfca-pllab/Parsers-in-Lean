theory Earley_Benchmark_Adapter
  imports
    "Earley_Parser.Earley_Parser"
    "HOL-Library.Code_Target_Nat"
begin

section \<open>Generic indexed benchmark interface\<close>

datatype indexed_symbol =
    Nonterminal nat
  | Terminal nat

fun indexed_rule :: "nat \<times> indexed_symbol list \<Rightarrow> indexed_symbol rule" where
  "indexed_rule (lhs, rhs) = (Nonterminal lhs, rhs)"

fun pointer_size :: "pointer \<Rightarrow> nat" where
  "pointer_size (PreRed _ alternatives) = 1 + length alternatives"
| "pointer_size _ = 1"

definition chart_item_count :: "'a bins \<Rightarrow> nat" where
  "chart_item_count bs = sum_list (map length bs)"

definition pointer_count :: "'a bins \<Rightarrow> nat" where
  "pointer_count bs =
    sum_list (map (\<lambda>bin. sum_list (map (\<lambda>entry. pointer_size (snd entry)) bin)) bs)"

definition accepts_bins :: "'a cfg \<Rightarrow> 'a list \<Rightarrow> 'a bins \<Rightarrow> bool" where
  "accepts_bins G input bs =
    (filter (is_finished G input) (items (bs ! length input)) \<noteq> [])"

definition indexed_cfg ::
  "nat \<Rightarrow> (nat \<times> indexed_symbol list) list \<Rightarrow> indexed_symbol cfg"
where
  "indexed_cfg start rules =
    CFG (map indexed_rule rules) (Nonterminal start)"

definition indexed_input :: "nat list \<Rightarrow> indexed_symbol list" where
  "indexed_input tokens = map Terminal tokens"

definition parse_indexed ::
  "indexed_symbol cfg \<Rightarrow> indexed_symbol list
    \<Rightarrow> indexed_symbol bins \<times> indexed_symbol tree option"
where
  "parse_indexed G input =
    (let bs = Earley\<^sub>L G input
     in (bs, build_tree G input bs))"

definition summarize_indexed ::
  "indexed_symbol cfg \<Rightarrow> indexed_symbol list
    \<Rightarrow> indexed_symbol bins \<times> indexed_symbol tree option
    \<Rightarrow> (bool \<times> bool) \<times> (nat \<times> nat)"
where
  "summarize_indexed G input parsed =
    (case parsed of (bs, tree) \<Rightarrow>
      ((accepts_bins G input bs, tree \<noteq> None),
       (chart_item_count bs, pointer_count bs)))"

section \<open>Persistent TSV worker\<close>

ML_export \<open>
structure Earley_Benchmark_Worker =
struct

datatype parsed_symbol =
    Parsed_Nonterminal of int
  | Parsed_Terminal of int

type parsed_rule = int * parsed_symbol list

type grammar =
  {id: string,
   start: int,
   nonterminals: int,
   terminals: int,
   rules: parsed_rule list}

exception Protocol_Error of string

fun protocol_error message = raise Protocol_Error message

fun fields separator text =
  String.fields (fn character => character = separator) text

fun strip_line line =
  if String.isSuffix "\n" line then
    let
      val without_lf = String.substring (line, 0, size line - 1)
    in
      if String.isSuffix "\r" without_lf
      then String.substring (without_lf, 0, size without_lf - 1)
      else without_lf
    end
  else line

val input_stream = Unsynchronized.ref TextIO.stdIn

fun read_line () = Option.map strip_line (TextIO.inputLine (!input_stream))

fun write_fields values =
  (TextIO.output (TextIO.stdOut, space_implode "\t" values ^ "\n");
   TextIO.flushOut TextIO.stdOut)

fun parse_nat label text =
  Value.parse_nat text
    handle Fail _ => protocol_error ("invalid " ^ label ^ ": " ^ text)

fun check_bound label bound value =
  if value < bound then value
  else protocol_error
    (label ^ " " ^ string_of_int value ^
     " is outside [0," ^ string_of_int bound ^ ")")

fun parse_symbol nonterminals terminals text =
  (case fields #":" text of
    ["N", identifier] =>
      Parsed_Nonterminal
        (check_bound "nonterminal" nonterminals
          (parse_nat "nonterminal identifier" identifier))
  | ["T", identifier] =>
      Parsed_Terminal
        (check_bound "terminal" terminals
          (parse_nat "terminal identifier" identifier))
  | _ => protocol_error ("invalid RHS symbol: " ^ text))

fun parse_rhs nonterminals terminals "-" = []
  | parse_rhs nonterminals terminals text =
      if text = "" then protocol_error "empty RHS field (use - for epsilon)"
      else map (parse_symbol nonterminals terminals) (fields #"," text)

fun parse_rule nonterminals terminals line =
  (case fields #"\t" line of
    ["RULE", lhs, rhs] =>
      (check_bound "rule LHS" nonterminals (parse_nat "rule LHS" lhs),
       parse_rhs nonterminals terminals rhs)
  | _ => protocol_error ("expected RULE, received: " ^ line))

fun read_rules 0 _ _ accumulated = rev accumulated
  | read_rules count nonterminals terminals accumulated =
      (case read_line () of
        NONE => protocol_error "unexpected EOF while reading rules"
      | SOME line =>
          read_rules (count - 1) nonterminals terminals
            (parse_rule nonterminals terminals line :: accumulated))

fun expect_end () =
  (case read_line () of
    SOME "END" => ()
  | SOME line => protocol_error ("expected END, received: " ^ line)
  | NONE => protocol_error "unexpected EOF before END")

fun parse_init grammar_id start_text nonterminal_text terminal_text rule_text =
  let
    val nonterminals = parse_nat "nonterminal count" nonterminal_text
    val terminals = parse_nat "terminal count" terminal_text
    val rule_count = parse_nat "rule count" rule_text
    val _ =
      if grammar_id = "" then protocol_error "grammar identifier is empty"
      else ()
    val start =
      check_bound "start nonterminal" nonterminals
        (parse_nat "start nonterminal" start_text)
    val rules = read_rules rule_count nonterminals terminals []
    val _ = expect_end ()
  in
    {id = grammar_id,
     start = start,
     nonterminals = nonterminals,
     terminals = terminals,
     rules = rules}
  end

fun code_nat value = @{code nat_of_integer} value

fun code_symbol (Parsed_Nonterminal identifier) =
      @{code Nonterminal} (code_nat identifier)
  | code_symbol (Parsed_Terminal identifier) =
      @{code Terminal} (code_nat identifier)

fun code_rule (lhs, rhs) = (code_nat lhs, map code_symbol rhs)

fun parse_tokens terminals "-" = []
  | parse_tokens terminals text =
      if text = "" then protocol_error "empty token field (use - for empty input)"
      else
        map
          (fn token =>
            check_bound "input terminal" terminals
              (parse_nat "input terminal" token))
          (fields #"," text)

fun bool_text true = "true"
  | bool_text false = "false"

fun safe_detail text =
  String.translate
    (fn #"\t" => " "
      | #"\n" => " "
      | #"\r" => " "
      | character => String.str character)
    text

fun runtime_error case_id elapsed exn =
  write_fields
    ["RESULT",
     case_id,
     elapsed,
     "parser_error",
     "unknown",
     "unknown",
     "unknown",
     "-",
     "runtime",
     safe_detail (Runtime.exn_message exn)]

fun run ({start, terminals, rules, ...}: grammar) case_id token_text =
  let
    val tokens = parse_tokens terminals token_text
    val grammar =
      @{code indexed_cfg}
        (code_nat start)
        (map code_rule rules)
    val input = @{code indexed_input} (map code_nat tokens)
    val run_parser =
      fn () => @{code parse_indexed} grammar input
    val result = Exn.capture (Timing.timing run_parser) ()
  in
    (case result of
      Exn.Res ({elapsed, ...}, parsed) =>
        let
          val elapsed_text = string_of_int (Time.toNanoseconds elapsed)
          val summary =
            Exn.capture
              (fn () => @{code summarize_indexed} grammar input parsed) ()
        in
          (case summary of
            Exn.Res ((accepted, tree_present), (items, pointers)) =>
              write_fields
                ["RESULT",
                 case_id,
                 elapsed_text,
                 if accepted then "accept" else "reject",
                 bool_text accepted,
                 "unknown",
                 bool_text tree_present,
                 "chart_items=" ^
                   string_of_int (@{code integer_of_nat} items) ^
                   ";pointers=" ^
                   string_of_int (@{code integer_of_nat} pointers),
                 "-",
                 "-"]
          | Exn.Exn exn => runtime_error case_id elapsed_text exn)
        end
    | Exn.Exn exn => runtime_error case_id "0" exn)
  end

fun result_protocol_error case_id message =
  write_fields
    ["RESULT",
     case_id,
     "0",
     "parser_error",
     "unknown",
     "unknown",
     "unknown",
     "-",
     "protocol",
     safe_detail message]

fun loop current =
  (case read_line () of
    NONE => ()
  | SOME "STOP" => ()
  | SOME line =>
      let
        val next =
          (case fields #"\t" line of
            ["INIT", grammar_id, start, nonterminals, terminals, rules] =>
              let
                val grammar =
                  parse_init grammar_id start nonterminals terminals rules
                val _ = write_fields ["READY", grammar_id]
              in SOME grammar end
          | ["RUN", case_id, tokens] =>
              (case current of
                NONE =>
                  (result_protocol_error case_id
                    "RUN received before successful INIT";
                   current)
              | SOME grammar =>
                  ((run grammar case_id tokens
                    handle Protocol_Error message =>
                      result_protocol_error case_id message);
                   current))
          | command :: _ =>
              (write_fields
                ["ERROR", if command = "" then "-" else command,
                 "protocol", "invalid command"];
               current)
          | [] =>
              (write_fields ["ERROR", "-", "protocol", "empty command"];
               current))
          handle Protocol_Error message =>
            (write_fields ["ERROR", "-", "protocol", safe_detail message];
             current)
      in loop next end)

fun main () =
  (case OS.Process.getEnv "EARLEY_BENCHMARK_INPUT" of
    NONE => loop NONE
  | SOME path =>
      let
        val stream = TextIO.openIn path
        val _ = input_stream := stream
      in Exn.release (Exn.capture loop NONE) before TextIO.closeIn stream end)

end
\<close>

end
