import ParserCombinators

@[simp]
def tag : PUnit → Type := fun _ => List Char

instance : DecidableEq (tag t) := by
  unfold tag
  infer_instance

-- rightRec ::= a | a rightRec
def rightRec : ParserM (tag := tag) Char Const (List Char) :=
  memoize Counter.empty (fun recur _ =>
    let secondCase := liftA2 List.cons (terminal'  'a') (recur PUnit.unit)
    (pure <$> terminal'  'a') ⊔ secondCase
  ) PUnit.unit

-- leftRec ::= a | leftRec a
def leftRec : ParserM (tag := tag) Char Const (List Char) :=
  memoize Counter.empty (fun recur _ =>
    let secondCase := liftA2 List.concat (recur PUnit.unit) (terminal'  'a')
    (pure <$> terminal'  'a') ⊔ secondCase
  ) PUnit.unit

def parsers := [("leftRec", leftRec), ("rightRec", rightRec)]

def main (args : List String) : IO UInt32 := match args with
  | [] => do
    for (name, parser) in parsers do
      IO.println $ "running " ++ name
      for n in List.range 5 do
        let len := 2 ^ n + 1
        let input := Array.replicate len 'a'
        let _ <- timeit len.repr $ pure $ (runParser parser input).1.toList
    pure 0
  | _ => pure 1
