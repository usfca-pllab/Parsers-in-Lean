module Grammar = Indexed
module Parser = Grammar.PG.ParserAndProofs.PEF.PS.P
module Defs = Grammar.D.Defs
module Prediction = Parser.SOS.SLLPEF.SLLS.SLLP.GA.LLPC.LLPEF.LLP

exception Protocol_error of string

type initialization = {
  grammar_id : string;
  start : int;
  nt_count : int;
  term_count : int;
  rule_count : int;
}

let split_tabs line = Stdlib.String.split_on_char '\t' line

let nonnegative_int field text =
  match int_of_string_opt text with
  | Some value when value >= 0 -> value
  | _ -> raise (Protocol_error (field ^ " must be a non-negative integer"))

let ensure_field field text =
  if text = "" || Stdlib.String.contains text '\t'
     || Stdlib.String.contains text '\n'
     || Stdlib.String.contains text '\r'
  then raise (Protocol_error (field ^ " is empty or contains a delimiter"))

let check_index kind upper value =
  if value < 0 || value >= upper then
    raise
      (Protocol_error
         (Printf.sprintf "%s index %d is outside [0,%d)" kind value upper))

let parse_init = function
  | ["INIT"; grammar_id; start; nt_count; term_count; rule_count] ->
      ensure_field "grammar_id" grammar_id;
      let init =
        {
          grammar_id;
          start = nonnegative_int "start_nt_id" start;
          nt_count = nonnegative_int "nt_count" nt_count;
          term_count = nonnegative_int "term_count" term_count;
          rule_count = nonnegative_int "rule_count" rule_count;
        }
      in
      check_index "start nonterminal" init.nt_count init.start;
      init
  | _ ->
      raise
        (Protocol_error
           "expected INIT grammar_id start_nt_id nt_count term_count rule_count")

let parse_symbol init text =
  if Stdlib.String.length text < 3 || Stdlib.String.get text 1 <> ':' then
    raise (Protocol_error ("invalid grammar symbol " ^ text));
  let index =
    nonnegative_int "grammar symbol index"
      (Stdlib.String.sub text 2 (Stdlib.String.length text - 2))
  in
  match Stdlib.String.get text 0 with
  | 'T' ->
      check_index "terminal" init.term_count index;
      Defs.T index
  | 'N' ->
      check_index "nonterminal" init.nt_count index;
      Defs.NT index
  | _ -> raise (Protocol_error ("grammar symbol must start with T: or N:"))

let parse_rhs init text =
  if text = "-" then []
  else
    let fields = Stdlib.String.split_on_char ',' text in
    if Stdlib.List.exists (( = ) "") fields then
      raise (Protocol_error "empty symbol in rule right-hand side");
    Stdlib.List.map (parse_symbol init) fields

let parse_rule init = function
  | ["RULE"; lhs; rhs] ->
      let lhs = nonnegative_int "rule lhs" lhs in
      check_index "rule lhs nonterminal" init.nt_count lhs;
      (lhs, parse_rhs init rhs)
  | _ -> raise (Protocol_error "expected RULE lhs_id rhs")

let input_line () =
  match Stdlib.input_line stdin with
  | line -> line
  | exception End_of_file ->
      raise (Protocol_error "unexpected end of input")

let read_initialization () =
  let init = parse_init (split_tabs (input_line ())) in
  let rec rules remaining reversed =
    if remaining = 0 then Stdlib.List.rev reversed
    else
      let rule = parse_rule init (split_tabs (input_line ())) in
      rules (remaining - 1) (rule :: reversed)
  in
  let grammar = rules init.rule_count [] in
  match split_tabs (input_line ()) with
  | ["END"] -> (init, grammar)
  | _ -> raise (Protocol_error "expected END after the declared rules")

let chars_to_string chars =
  let bytes = Bytes.create (Stdlib.List.length chars) in
  Stdlib.List.iteri (Bytes.set bytes) chars;
  Bytes.unsafe_to_string bytes

let sanitize text =
  let text =
    Stdlib.String.map
      (function '\t' | '\n' | '\r' -> ' ' | character -> character)
      text
  in
  if text = "" then "-" else text

let parse_tokens init text =
  if text = "-" then []
  else
    let fields = Stdlib.String.split_on_char ',' text in
    if Stdlib.List.exists (( = ) "") fields then
      raise (Protocol_error "empty token in RUN input");
    Stdlib.List.map
      (fun field ->
        let token = nonnegative_int "RUN terminal" field in
        check_index "RUN terminal" init.term_count token;
        (token, []))
      fields

let classify = function
  | Parser.Accept _ ->
      ("accept", "true", "unique", "true", "-", "-")
  | Parser.Ambig _ ->
      ("ambiguous", "true", "ambiguous", "true", "-", "-")
  | Parser.Reject message ->
      ("reject", "false", "unknown", "false", "-",
       sanitize (chars_to_string message))
  | Parser.Error error ->
      let error_kind, detail =
        match error with
        | Parser.InvalidState -> ("invalid_state", "InvalidState")
        | Parser.LeftRecursion nt ->
            ("left_recursion", Printf.sprintf "LeftRecursion %d" nt)
        | Parser.PredictionError prediction_error ->
            (match prediction_error with
             | Prediction.SpInvalidState ->
                 ("prediction_invalid_state",
                  chars_to_string (Parser.showParseError error))
             | Prediction.SpLeftRecursion nt ->
                 ("left_recursion",
                  Printf.sprintf "PredictionError (SpLeftRecursion %d)" nt))
      in
      ("parser_error", "unknown", "unknown", "false", error_kind,
       sanitize detail)

let emit_result case_id elapsed_ns result =
  let outcome, accepted, ambiguity, tree_present, error_kind, detail =
    classify result
  in
  Printf.printf "RESULT\t%s\t%Ld\t%s\t%s\t%s\t%s\t-\t%s\t%s\n%!"
    (sanitize case_id) elapsed_ns outcome accepted ambiguity tree_present
    error_kind detail

let run_once init parse_input = function
  | ["RUN"; case_id; tokens] ->
      ensure_field "case_id" case_id;
      let input = parse_tokens init tokens in
      let started = Unix.gettimeofday () in
      let result = parse_input input in
      let finished = Unix.gettimeofday () in
      let elapsed_ns = Int64.of_float ((finished -. started) *. 1_000_000_000.) in
      emit_result case_id elapsed_ns result;
      true
  | ["STOP"] -> false
  | _ -> raise (Protocol_error "expected RUN case_id terminal_ids or STOP")

let fatal detail =
  Printf.printf "FATAL\tprotocol_error\t%s\n%!" (sanitize detail);
  exit 2

let () =
  try
    let init, grammar = read_initialization () in
    (* CoStar constructs its production and closure maps at this application. *)
    let parse_input = Parser.parse grammar init.start in
    Printf.printf "READY\t%s\n%!" init.grammar_id;
    let rec loop () =
      if run_once init parse_input (split_tabs (input_line ())) then loop ()
    in
    loop ()
  with
  | Protocol_error detail -> fatal detail
  | Failure detail -> fatal detail
  | Invalid_argument detail -> fatal detail
