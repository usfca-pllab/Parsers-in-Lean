/-!

# Parser Monad
This file defines `Parser`, a monadic structure to enable
the writing of efficient parsers. `Parser` takes in a String as input,
and returns a structured result, consisting of the parsed input character,
concatenated with the rest of the (unparsed) string. Also handles errors for
unexpected input end and unexpected characters.

This file also defines the various functions that can be applied to the Parser structure.

## Example usage of Parser
def parseA : Parser Char :=
  λ input, match input.toList with
   | [] => ParseResult.failure "Unexpeced end of input"
   | c :: cs if c = 'a' then
        ParseResult.success c (String.mk cs)
      else
        ParseResult.failure ("Unexpected character: " ++ c.toString)
-/

variable {a b : Type}

def Str := List Char
/-
Parser, returns an instance of the monadic ParseResult (either returns
none or, in the success case, the parsed result and the rest of the unparsed input)
-/
structure Parser (a : Type) where
  run : Str → Option (a × Str)
  decreases : ∀ s result,
    -- run s = some result → result.2.length ≤ s.length
    run s = some result → result.2.IsSuffix s

--
def nullable (p : Parser a) : Prop = (∀ s : String) (∀ x : a) (p.run s) ≠ (some (s, x))

def fail  (_ : Parser a) : Parser a where
  run := fun _ => none
  decreases := by {
    intro s result h
    contradiction
  }

def or  (p1 : Parser a) (p2 : Parser a) : Parser a where
  run := fun input =>
    match p1.run input with
       | some (success_parser, success_input)=> some (success_parser, success_input)
       | none => match p2.run input with
          | some (success_parser, success_input)=> some (success_parser, success_input)
          | none => none
  decreases := by {
    sorry
  }

-- Parser Concatenations
def concat  (p1 : Parser a) (p2 : Parser b) : Parser (a × b) where
  -- Run p1 on the input (will return Some(v1, rest1) if successful)
  -- Run p2 on rest1 (will return Some (v2, rest2))
  -- If both succeed, return Some ((v1, v2), rest2)
  -- If both or either fail, return None
  run := fun input =>
    match p1.run input with
      | some (v1, rest1) =>
        match p2.run rest1 with
          | some (v2, rest2) => some ((v1, v2), rest2)
          | none => none
      | none => none
  decreases := by {
    sorry
  }
def extractR  (p1 : Parser a) (p2 : Parser b) : Parser b where
  run := fun input =>
  match p1.run input with
    | some (_, rest1) =>
      match p2.run rest1 with
        | some (v2, rest2) => some (v2, rest2)
        | none => none
    | none => none
  decreases := by {
    sorry
  }
def extractL  (p1 : Parser a) (p2 : Parser b) : Parser a where
  run := fun input =>
    match p1.run input with
      | some (v1, rest1) =>
        match p2.run rest1 with
          | some (_, _) => some (v1, rest1)
          | none => none
      | none => none
  decreases := by {
    sorry
  }

-- Lean doesn't recognize that rest is strictly smaller; need to convince it of
-- this fact!!
partial def many  (p : Parser a) : Parser (List a) where
  run := fun input =>
    match p.run input with
    | some (v, rest) =>
      match (many p).run rest with
      | some (vs, rest_rec) => some (v :: vs, rest_rec)
      | none => some ([v], rest)
    | none => some ([], input)
  decreases := by {
    sorry
  }

-- Attempt to get rid of partial:
-- def many  (p : Parser a) : Parser (List a) where
--   run := WellFounded.fix (measure String.length).wf (
--   fun input rec =>
--     match p.run input with
--     | some (v, rest) =>
--       match rec rest (by {
--         sorry
--       })
--       with
--       | some (vs, final_rest) => some (v :: vs, final_rest)
--       | none => some ([v], rest)
--     | none => some ([], input)
--   )
--   decreases := by {
--     sorry
--   }
partial def many1  (p : Parser a) : Parser (List a) where
  run := sorry
  decreases := sorry

-- Testing
def parseChar (pred : Char -> Bool): Parser Char where
  run := fun input =>
    match input with
      | []      => none
      | c :: cs =>
        if pred c then some (c, cs)
        else none
  decreases := by {
    sorry
  }
def parseA := parseChar (fun c => c == 'a')

def parseB := parseChar (fun c => c == 'b')

-- TODO: Not sure how to fix this
-- def eps : Parser Unit := fun input => (() , input)

-- #eval parseA.run "abc".data-- success
-- #eval parseA.run "madi".data-- failure
-- #eval parseA.run "a".data-- success
-- #eval parseA.run "".data-- failure
-- #eval parseA.run "aaaaaaaaaa".data-- success
--
--
-- #eval parseB.run "bc".data-- success
-- #eval parseB.run "madi".data-- failure
-- #eval parseB.run "b".data-- success
-- #eval parseB.run "".data-- failure
-- #eval parseB.run "bbbbbbbb".data--success
--
-- -- TODO: Not sure how to fix these:
-- #eval fail parseA.run "a".data
-- #eval fail parseB.run "b".data
-- #eval or parseA parseB "b".data
--
-- -- TODO: Write failure cases as well
-- #eval concat parseA parseB "ab".data
-- #eval extractL parseA parseB "ab".data
-- #eval extractR parseA parseB "ab".data
--
--
-- #eval many1 parseA "aaaaa".data
-- #eval many1 parseA "bbb".data
-- #eval many1 parseA "ba".data
-- #eval many parseA "".data
-- #eval many parseA "ba".data
