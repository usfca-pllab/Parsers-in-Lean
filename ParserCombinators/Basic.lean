open Option
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

def not_nullable (p : Parser a) := ∀ s :Str, ∀ x : a, (p.run s) ≠ (some (x, s))

theorem decreases_if_not_nullable (p : Parser a) (h : not_nullable p) (s : Str) (result : a × Str)
  (h_run : p.run s = some result) :
  result.snd.length < s.length := by
    have h_non_increasing := p.decreases s result h_run
    obtain ⟨x', s'⟩ := result
    simp at h_non_increasing
    have h_not_eq := h s
    simp only [h_run, ne_eq, Option.some.injEq] at h_not_eq
    simp
    have h_not_eq' : s' ≠ s := by
      intro h_eq
      exact h_not_eq x' (congrArg (Prod.mk x') h_eq)

    rw [@Nat.lt_iff_le_and_ne]
    constructor
    · exact List.IsSuffix.length_le h_non_increasing
    · intro h_eq
      exact h_not_eq' (List.IsSuffix.eq_of_length h_non_increasing h_eq)

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
    intro s result h_run
    cases h1 : p1.run s with
    | none => simp [h1] at h_run
    | some pair1 =>
      let (v1, rest1) := pair1
      cases h2 : p2.run rest1 with
      | none => simp [h1, h2] at h_run
      | some pair2 =>
        let (v2, rest2) := pair2
        have h_p1 := p1.decreases s (v1, rest1) h1
        have h_p2 := p2.decreases rest1 (v2, rest2) h2
        simp only at h_p1
        simp only at h_p2
        simp only [Option.some.injEq, h1, h2] at h_run
        rw [<- h_run]
        exact List.IsSuffix.trans h_p2 h_p1
  }

theorem concat_not_nullable (p1 : Parser a) (p2 : Parser b)
  (h1 : not_nullable p1) (h2 : not_nullable p2) : not_nullable (concat p1 p2) := by {
    intro s x h_run
    simp [concat] at h_run
    cases h1_case : p1.run s with
    | none => simp [h1_case] at h_run
    | some pair =>
      let (v1, rest1) := pair
      cases h2_case : p2.run rest1 with
      | none => simp [h1_case, h2_case] at h_run
      | some =>
        -- have h_p2 := h2 rest1
        -- I just need to rewrite h_p2 somehow to fit what Lean is looking for
        -- contradiction
        sorry
  }

def map  (f : a -> b) (p : Parser a) : Parser b where
  run := fun input =>
    match p.run input with
      | some (v, rest) => some (f v, rest)
      | none => none
  decreases := by {
    intro s result
    cases h : p.run s with
    | none => simp [h]
    | some pair =>
      simp only [Option.some.injEq, h]
      intro h_snd
      rw [← h_snd]
      simp [p.decreases s pair h]
  }

theorem map_not_nullable (f : a → b) (p : Parser a)
  (h1 : not_nullable p) : not_nullable (map f p1) := by {
    intro s y
    simp [map]
    cases h_p : p.run s with
    | none => sorry
    | some pair => sorry
  }
def extractR  (p1 : Parser a) (p2 : Parser b) : Parser b :=
  map (fun x => x.2) (concat p1 p2)

def extractL  (p1 : Parser a) (p2 : Parser b) : Parser a :=
  map (fun x => x.1) (concat p1 p2)

-- Making this a separate def makes writing the recursive function easier to work with.
private def many_run (p : Parser a) (h : not_nullable p) (input : Str) : Option (List a × Str) :=
  match h_run : p.run input with
  | some (v, rest) =>
    -- for termination
    have : rest.length < input.length := decreases_if_not_nullable p h input (v, rest) h_run
    match many_run p h rest with
    | some (vs, rest_rec) => some (v :: vs, rest_rec)
    | none => some ([v], rest)
  | none => some ([], input)
termination_by input.length

def many (p : Parser a) (h : not_nullable p) : Parser (List a) where
  run := many_run p h
  decreases := by sorry

def many1 (p : Parser a) (h : not_nullable p) : Parser (List a) :=
  map (fun x => x.1 :: x.2) (concat p (many p h))

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
