import ParserCombinators.Gen

namespace JointBenchmark.Lean

open CFG Symbol

inductive RawSymbol where
  | term : Nat → RawSymbol
  | nonterm : Nat → RawSymbol
  deriving Repr

structure RawRule where
  lhs : Nat
  rhs : List RawSymbol
  deriving Repr

structure Init where
  grammarId : String
  start : Nat
  nonterminalCount : Nat
  terminalCount : Nat
  ruleCount : Nat
  deriving Repr

structure Observation where
  accepted : Bool
  successfulEnds : Nat
  memoTags : Nat
  memoEntries : Nat
  cachedEndpoints : Nat
  representativeTreeNodes : Nat

def Observation.digest (observation : Observation) : Nat :=
  (if observation.accepted then 1 else 0) +
    observation.successfulEnds +
    observation.memoTags +
    observation.memoEntries +
    observation.cachedEndpoints +
    observation.representativeTreeNodes

private def parseNat (field value : String) : Except String Nat :=
  match value.toNat? with
  | some n => .ok n
  | none => .error s!"invalid {field}: {value}"

private def splitTabs (line : String) : List String :=
  line.trim.splitOn "\t"

private def parseInit (line : String) : Except String Init := do
  match splitTabs line with
  | ["INIT", grammarId, start, nonterminalCount, terminalCount, ruleCount] =>
      pure {
        grammarId
        start := ← parseNat "start nonterminal" start
        nonterminalCount := ← parseNat "nonterminal count" nonterminalCount
        terminalCount := ← parseNat "terminal count" terminalCount
        ruleCount := ← parseNat "rule count" ruleCount
      }
  | _ => .error "expected INIT with six tab-separated fields"

private def parseRawSymbol (value : String) : Except String RawSymbol := do
  match value.splitOn ":" with
  | ["T", id] => pure (.term (← parseNat "terminal id" id))
  | ["N", id] => pure (.nonterm (← parseNat "nonterminal id" id))
  | _ => .error s!"invalid grammar symbol: {value}"

private def parseRhs (value : String) : Except String (List RawSymbol) :=
  if value == "-" then
    .ok []
  else
    value.splitOn "," |>.mapM parseRawSymbol

private def parseRule (line : String) : Except String RawRule := do
  match splitTabs line with
  | ["RULE", lhs, rhs] =>
      pure {
        lhs := ← parseNat "rule lhs" lhs
        rhs := ← parseRhs rhs
      }
  | _ => .error "expected RULE with three tab-separated fields"

private def parseInput (terminalCount : Nat) (value : String) :
    Except String (Array Nat) := do
  let tokens ←
    if value == "-" then
      .ok []
    else
      value.splitOn "," |>.mapM (parseNat "input terminal")
  for token in tokens do
    if token ≥ terminalCount then
      throw s!"input terminal {token} is outside the terminal range"
  pure tokens.toArray

private def validateRule (init : Init) (rule : RawRule) : Except String Unit := do
  if rule.lhs ≥ init.nonterminalCount then
    throw s!"rule lhs {rule.lhs} is outside the nonterminal range"
  for symbol in rule.rhs do
    match symbol with
    | .term id =>
        if id ≥ init.terminalCount then
          throw s!"terminal {id} is outside the terminal range"
    | .nonterm id =>
        if id ≥ init.nonterminalCount then
          throw s!"nonterminal {id} is outside the nonterminal range"

private def convertSymbol (init : Init) (symbol : RawSymbol) :
    Except String (Symbol Nat (Fin init.nonterminalCount)) :=
  match symbol with
  | .term id =>
      if id < init.terminalCount then
        .ok (.term id)
      else
        .error s!"terminal {id} is outside the terminal range"
  | .nonterm id =>
      if h : id < init.nonterminalCount then
        .ok (.nonterm ⟨id, h⟩)
      else
        .error s!"nonterminal {id} is outside the nonterminal range"

private def buildGrammar (init : Init) (rawRules : List RawRule) :
    Except String (@CFG Nat (Fin init.nonterminalCount)) := do
  if rawRules.length != init.ruleCount then
    throw s!"expected {init.ruleCount} rules, received {rawRules.length}"
  if hStart : init.start < init.nonterminalCount then
    let rules ← rawRules.mapM fun (rule : RawRule) => do
      let lhs : Fin init.nonterminalCount ←
        if hLhs : rule.lhs < init.nonterminalCount then
          pure ⟨rule.lhs, hLhs⟩
        else
          throw s!"rule lhs {rule.lhs} is outside the nonterminal range"
      pure (lhs, ← rule.rhs.mapM (convertSymbol init))
    pure {
      start := ⟨init.start, hStart⟩
      rules := fun n => (rules.filter fun rule => rule.1 == n).map Prod.snd
    }
  else
    throw s!"start nonterminal {init.start} is outside the nonterminal range"

private def memoEntries {n : Nat} (cfg : @CFG Nat (Fin n))
    (memo : MemoData (Gen.tag cfg) Option) : Nat :=
  memo.fold (fun total _ entries => total + entries.size) 0

private def cachedEndpoints {n : Nat} (cfg : @CFG Nat (Fin n))
    (memo : MemoData (Gen.tag cfg) Option) : Nat :=
  memo.fold
    (fun total _ entries =>
      entries.fold
        (fun total _ resultMap => total + resultMap.size)
        total)
    0

private def treeNodes {n : Nat} (cfg : @CFG Nat (Fin n)) : ParseTree cfg → Nat
  | .Leaf _ => 1
  | .Node _ _ children =>
      1 + children.foldl (fun total tree => total + treeNodes cfg tree) 0

private def resultTreeNodes {n : Nat} (cfg : @CFG Nat (Fin n))
    (results : ResultMap Option (ParseTree cfg)) : Nat :=
  results.fold
    (fun total _ tree? => total + (tree?.map (treeNodes cfg)).getD 0)
    0

private def cachedTreeNodes {n : Nat} (cfg : @CFG Nat (Fin n))
    (memo : MemoData (Gen.tag cfg) Option) : Nat :=
  memo.fold
    (fun total _ entries =>
      entries.fold
        (fun total _ resultMap => total + resultTreeNodes cfg resultMap)
        total)
    0

@[noinline]
private def parse {n : Nat}
    (cfg : @CFG Nat (Fin n)) (input : Array Nat) :
    ResultMap Option (ParseTree cfg) × MemoData (Gen.tag cfg) Option :=
  runParser (Gen.gen (μ := Option) cfg cfg.start) input

private def summarize {n : Nat}
    (cfg : @CFG Nat (Fin n))
    (results : ResultMap Option (ParseTree cfg))
    (memo : MemoData (Gen.tag cfg) Option)
    (accepted : Bool) : Observation :=
  {
    accepted
    successfulEnds := results.size
    memoTags := memo.size
    memoEntries := memoEntries cfg memo
    cachedEndpoints := cachedEndpoints cfg memo
    representativeTreeNodes :=
      resultTreeNodes cfg results + cachedTreeNodes cfg memo
  }

private def acceptedAtEnd {n : Nat}
    (cfg : @CFG Nat (Fin n))
    (input : Array Nat)
    (results : ResultMap Option (ParseTree cfg)) : Bool :=
  let accepted :=
    match results[input.size]? with
    | some (some _) => true
    | _ => false
  accepted

private def cleanField (value : String) : String :=
  value.replace "\t" " " |>.replace "\n" " " |>.replace "\r" " "

private def printLine (line : String) : IO Unit := do
  let stdout ← IO.getStdout
  stdout.putStrLn line
  stdout.flush

private def printProtocolError (message : String) : IO Unit :=
  printLine s!"ERROR\tprotocol\t{cleanField message}"

private def readRules (stdin : IO.FS.Stream) : Nat → List RawRule →
    IO (Except String (List RawRule))
  | 0, rules => pure (.ok rules.reverse)
  | count + 1, rules => do
      let line ← stdin.getLine
      match parseRule line with
      | .error message => pure (.error message)
      | .ok rule => readRules stdin count (rule :: rules)

private def runOne {n : Nat}
    (cfg : @CFG Nat (Fin n)) (terminalCount : Nat) (sink : IO.Ref Nat)
    (caseId inputText : String) : IO Unit := do
  match parseInput terminalCount inputText with
  | .error message =>
      printLine s!"RESULT\t{caseId}\t0\tparser_error\tunknown\tunknown\tunknown\t-\tprotocol\t{cleanField message}"
  | .ok input =>
      let started ← IO.monoNanosNow
      let (results, memo) := parse cfg input
      let accepted := acceptedAtEnd cfg input results
      sink.set ((if accepted then 1 else 0) + results.size + memo.size)
      let finished ← IO.monoNanosNow
      let observation := summarize cfg results memo accepted
      -- Keep the full summary live even though reporting metrics is outside
      -- the parser timing interval.
      sink.set observation.digest
      let outcome := if observation.accepted then "accept" else "reject"
      let accepted := if observation.accepted then "true" else "false"
      let treePresent := accepted
      let metrics := String.intercalate ";" [
        s!"successful_ends={observation.successfulEnds}",
        s!"memo_tags={observation.memoTags}",
        s!"memo_entries={observation.memoEntries}",
        s!"cached_endpoints={observation.cachedEndpoints}",
        s!"representative_tree_nodes={observation.representativeTreeNodes}"
      ]
      printLine s!"RESULT\t{caseId}\t{finished - started}\t{outcome}\t{accepted}\tunknown\t{treePresent}\t{metrics}\t-\t-"

partial def requestLoop {n : Nat}
    (cfg : @CFG Nat (Fin n)) (terminalCount : Nat)
    (stdin : IO.FS.Stream) (sink : IO.Ref Nat) :
    IO UInt32 := do
  let line ← stdin.getLine
  if line.isEmpty then
    pure 0
  else
    match splitTabs line with
    | ["RUN", caseId, input] =>
        runOne cfg terminalCount sink caseId input
        requestLoop cfg terminalCount stdin sink
    | ["STOP"] => pure 0
    | _ =>
        printProtocolError "expected RUN or STOP"
        pure 2

def run : IO UInt32 := do
  let stdin ← IO.getStdin
  let initLine ← stdin.getLine
  match parseInit initLine with
  | .error message =>
      printProtocolError message
      pure 2
  | .ok init => do
      match ← readRules stdin init.ruleCount [] with
      | .error message =>
          printProtocolError message
          pure 2
      | .ok rules => do
          let endLine ← stdin.getLine
          if endLine.trim != "END" then
            printProtocolError "expected END after grammar rules"
            pure 2
          else
            match buildGrammar init rules with
            | .error message =>
                printProtocolError message
                pure 2
            | .ok cfg =>
                printLine s!"READY\t{init.grammarId}"
                let sink ← IO.mkRef 0
                requestLoop cfg init.terminalCount stdin sink

end JointBenchmark.Lean

def main : IO UInt32 :=
  JointBenchmark.Lean.run
