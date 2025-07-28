import ParserCombinators

def main (args : List String) : IO UInt32 := match args with
  | [s] => do
    IO.println $ (runParser'.{0} (μ := Const) concatParser s).1.toList
    pure 0
  | _ => pure 1
