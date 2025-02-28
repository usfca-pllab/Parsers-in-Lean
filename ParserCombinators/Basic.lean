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
  decreases : ∀ s result, run s = some result → result.snd <:+ s

--
def not_nullable (p : Parser a) := ∀ s :Str, ∀ x : a, (p.run s) ≠ (some (x, s))

def fail  (_ : Parser a) : Parser a where
  run := fun _ => none
  decreases := by
    intro s result h
    contradiction

theorem fail_not_nullable : ∀ p : Parser a, not_nullable (fail p) := by
  simp [not_nullable, fail]

def or  (p1 : Parser a) (p2 : Parser a) : Parser a where
  run := fun input =>
    match p1.run input with
       | some (success_parser, success_input)=> some (success_parser, success_input)
       | none => match p2.run input with
          | some (success_parser, success_input)=> some (success_parser, success_input)
          | none => none
  decreases := by {
    intro s result
    simp
    intro h
    cases h1 : p1.run s
    · cases h2 : p2.run s
      · simp [h1, h2] at h
      · simp only [h1, h2, Option.some.injEq] at h
        rw [Prod.eta] at h
        rw [h] at h2
        exact p2.decreases s result h2
    · simp only [h1, Option.some.injEq] at h
      rw [Prod.eta] at h
      rw [h] at h1
      exact p1.decreases s result h1
  }

theorem or_not_nullable (p1 : Parser a) (p2 : Parser a)
  (h1 : not_nullable p1) (h2 : not_nullable p2) : not_nullable (or p1 p2) := by {
  revert h1 h2
  simp [not_nullable, _root_.or]
  intro h1 h2 s x
  have h_p1 : p1.run s ≠ some (x, s) := h1 s x
  have h_p2 : p2.run s ≠ some (x, s) := h2 s x
  intro h
  cases h1 : p1.run s
  · cases h2 : p2.run s
    · simp [h1, h2] at h
    · simp only [h1, h2, Option.some.injEq] at h
      rw [Prod.eta] at h
      rw [h] at h2
      exact h_p2 h2
  · simp only [h1, Option.some.injEq] at h
    rw [Prod.eta] at h
    rw [h] at h1
    exact h_p1 h1
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

def map  (f : a -> b) (p : Parser a) : Parser b where
  run := fun input =>
    match p.run input with
      | some (v, rest) => some (f v, rest)
      | none => none
  decreases := by {
    sorry
  }

def extractR  (p1 : Parser a) (p2 : Parser b) : Parser b :=
  map (fun x => x.2) (concat p1 p2)

def extractL  (p1 : Parser a) (p2 : Parser b) : Parser a :=
  map (fun x => x.1) (concat p1 p2)

-- Lean doesn't recognize that rest is strictly smaller; need to convince it of
-- this fact!!
partial def many (p : Parser a) : Parser (List a) where
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
