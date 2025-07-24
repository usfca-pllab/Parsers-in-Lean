-- A sketch of the port of the memoized combinators from Haskell, without the
-- CPS transformation

import Std.Data.DHashMap.Basic
import Std.Data.HashMap.Basic
import Std.Data.HashMap.AdditionalOperations
import Std.Data.HashMap.Lemmas
import Mathlib.Control.Traversable.Basic
import Mathlib.Control.Fold
import Batteries.Control.AlternativeMonad
import ParserCombinators.MState
import ParserCombinators.Util
import Aesop

-- β is the alphabet: parsers work over Array β
universe u v
variable {τ} { α β : Type u } {tag : τ → Type u} { μ : Type u → Type u } [BEq β] [BEq τ] [LawfulBEq τ] [Hashable τ]

-- Tags for each parser, these don't carry type information.
--
-- NOTE(maemre): A better option would be to use pointers to the parser functions as keys,
-- but I am not sure if that runs into issues with the termination checker.
--
-- If we want, we can store the type names here later.
structure Tag where
  id : Int
  deriving DecidableEq, BEq, Hashable

def startState {μ} [CollectionLike μ] : MemoData tag μ := {
  table := Std.DHashMap.emptyWithCapacity
}

abbrev UChar := ULift Char
abbrev UString := ULift String

@[inline]
def liftA2 {F : Type u → Type v} [Applicative F] {α β γ : Type u} (f : α → β → γ) (fa : F α) (fb : F β) : F γ :=
  f <$> fa <*> fb

def joinUnderCache {γ} [CollectionLike μ] (s1 s2 : MStateT (MemoData tag μ) (ReaderM (Array β)) (Std.HashMap Int (μ γ)))
    : MStateT (MemoData tag μ) (ReaderM (Array β)) (Std.HashMap Int (μ γ)) :=
  liftA2 (fun m1 m2 => Std.HashMap.unionWith m1 m2 (fun v1 v2 => v1 <|> v2)) s1 s2

-- Some of the α's here should become existential/hidden
abbrev Parser (β : Type u) (μ : Type u → Type u) [CollectionLike μ] (α : Type u) :=
  Int → MStateT (MemoData tag μ) (ReaderM (Array β)) (Std.HashMap Int (μ α))

instance [CollectionLike μ] : Functor (Parser (tag := tag) β μ) where
  map f x := Functor.map (Std.HashMap.map (fun _ => Functor.map f)) ∘ x

-- N.B. Have to define `pure` separately so that we can use it in `seq`
-- Defines the ability to create the simplest parser possible
instance [CollectionLike μ] : Pure (Parser (tag := tag) β μ) where
  pure a := fun pos => pure {(pos, pure a)}

-- might need other type class instances (e.g. to make fold work)
-- also, you may need to define or find a fold operation for Std.HashMap
instance [CollectionLike μ] [Traversable μ] : Bind (Parser (tag := tag) β μ) where
  bind {_ β'} x f := fun pos => do
      let pivotToResult ← x pos
      let actions : List (μ (MStateT (MemoData tag μ) (ReaderM (Array β)) (Std.HashMap Int (μ β')))) :=
        pivotToResult.toList.map (fun (j, ma) => (fun a => f a j) <$> ma)
      actions.foldl
        (Traversable.foldl joinUnderCache)
        (pure Std.HashMap.emptyWithCapacity)

instance [CollectionLike μ] [Traversable μ] : Monad (Parser (tag := tag) β μ) where

instance [CollectionLike μ] [Traversable μ] : Alternative (Parser (tag := tag) β μ) where
  failure _pos := pure Std.HashMap.emptyWithCapacity
  orElse r1 r2 pos :=
    let s1 := r1 pos
    let s2 := r2 () pos
    joinUnderCache s1 s2

instance [Monad μ] [Alternative μ] [Traversable μ] : LawfulMonad (Parser (tag := tag) β μ) := by {
  refine LawfulMonad.mk' (Parser β μ) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · sorry
  · sorry
  · sorry
  · sorry  -- use the proofs for the default impl
  · sorry  -- use the proofs for the default impl
  · sorry  -- use the proofs for the default impl
  · sorry  -- use the proofs for the default impl
  · sorry  -- use the proofs for the default impl
}

instance [Monad μ] [Alternative μ] [Traversable μ] : LawfulAlternative (Parser (tag := tag) β μ) where
  map_failure := sorry
  failure_seq := sorry
  orElse_failure := sorry
  failure_orElse := sorry
  orElse_assoc := sorry
  map_orElse := sorry

def epsilon [CollectionLike μ] : Parser (tag := tag) β μ PUnit := fun pos => pure {(pos, pure $ PUnit.unit)}

def terminal [CollectionLike μ] (s : String) : Parser (tag := tag) UChar μ UString := fun pos => do
  let input ← read
  if pos >= 0 && (s.data.map ULift.up).toArray.isPrefixOf (input.extract pos.toNat) then
    let endPos := pos + s.length
    pure {(endPos, pure $ ULift.up s)}
  else
    pure Std.HashMap.emptyWithCapacity

def terminal' [CollectionLike μ] (t: β) : Parser (tag := tag) β μ β := fun pos => do
  let input ← read
  if pos >= 0 && some t == input[pos.toNat]? then
    pure {(pos + 1, pure t)}
  else
    pure Std.HashMap.emptyWithCapacity

-- TODO(maemre): this is increasing the memoization table, which is a Noetherian lattice.
-- We need to make a termination argument using that.
partial def memoize [CollectionLike μ] [Traversable μ] (g : ((t : τ) → Parser (tag := tag) β μ (tag t)) → (t : τ) → Parser (tag := tag) β μ (tag t)) (t : τ) : Parser (tag := tag) β μ (tag t) :=
  fun pos => do
    let memo ← get
    -- Check if we have cached results for this tag and position
    match memo.table.get? t with
    | some positionMap =>
      match positionMap[pos]? with
      | some cachedResult => pure {(pos, cachedResult)}
      | none =>
        -- No cached result for this position, compute and cache
        let results ← g (memoize g) t pos
        -- Cache the new results
        let newPositionMap := results.fold (fun acc newPos result =>
          acc.insert newPos result) positionMap
        let newTable := memo.table.insert t newPositionMap
        set { memo with table := newTable }
        pure results
    | none =>
      -- No entry for this tag at all, so we compute it and cache it
      let results ← g (memoize g) t pos
      -- Create new position map and cache the results
      let newPositionMap := results.fold (fun acc newPos result =>
        acc.insert newPos result) Std.HashMap.emptyWithCapacity
      let newTable := memo.table.insert t newPositionMap
      set { memo with table := newTable }
      pure results

-- Testing

-- Will use `Option` as the concrete monad (some is success and none is failure)

def runParser [CollectionLike μ] (p : Parser (tag := tag) β μ α) (input : Array β) (pos : Int := 0) : (Std.HashMap Int (μ α)) × MemoData tag μ :=
  let stateTResult := (p pos).run startState
  let readerResult := stateTResult.run input
  readerResult

def runParser' [CollectionLike μ] (p : Parser (tag := tag) UChar μ α) (input : String) (pos : Int := 0) : (Std.HashMap Int (μ α)) × MemoData tag μ :=
  runParser p (input.toList.map ULift.up).toArray pos

def emptyTag : PUnit → Type := fun _ => PUnit

def runParserO {μ : Type → Type} {α : Type} [CollectionLike μ]
  (p : Parser (tag := emptyTag) UChar μ α) (input : String) (pos : Int := 0)
    : (Std.HashMap Int (μ α)) × MemoData emptyTag μ :=
  runParser'.{0} p input pos

-- Checking to make sure that runParser has correct type
#guard (runParserO (μ := Option) epsilon "test").1.toList == [(0, some PUnit.unit)]

-- Testing running the parsers (had to extract just the hashmap
-- because Lean couldn't extract a string from the full return type)
#guard (runParserO (μ := Option) (terminal "hello") "hello world").1.toList == [(5, some $ ULift.up "hello")]
#guard (runParserO (μ := Option) (terminal "wo") "hello world" 6).1.toList == [(8, some $ ULift.up "wo")]

-- Failure
#guard (runParserO (μ := Option) (terminal "llo") "hello world" 5).1.isEmpty

-- Edge case for empty string
#guard (runParserO (μ := Option) (terminal "") "hello world" 6).1.toList == [(6, some $ ULift.up "")]


-- Testing instances:

-- Functor (`<$>`)
def funcParser : Parser (tag := emptyTag) UChar Option String := (fun _ => "matched!") <$> terminal "hello"
def funcParser2 : Parser (tag := emptyTag) UChar Option Int := (fun x => x * 3) <$> terminal "hello" $> 2

-- TODO: (Madi) Just beef this up by testing edge cases
#guard (runParserO (μ := Option) funcParser "hello world").1.toList == [(5, some "matched!")]
#guard (runParserO (μ := Option) funcParser "hell").1.toList == []
#guard (runParserO (μ := Option) funcParser2 "hello").1.toList == [(5, some 6)]

-- Alternative (`<|>`)
def altParser [CollectionLike μ] [Traversable μ] : Parser (tag := tag) UChar μ UString :=
  terminal "hello" <|> terminal "goodbye"

#guard (runParserO (μ := Option) altParser "hello").1.toList == [(5, some $ ULift.up "hello")]
#guard (runParserO (μ := Option) altParser "goodbye").1.toList == [(7, some $ ULift.up "goodbye")]
#guard (runParserO (μ := List) altParser "hello").1.toList == [(5, [ULift.up "hello"])]
#guard (runParserO (μ := List) altParser "goodbye").1.toList == [(7, [ULift.up "goodbye"])]

-- Concatenation via bind (`>>=`)
def concatParser {μ : Type → Type} [CollectionLike μ] [Traversable μ] : Parser (tag := emptyTag) UChar μ (Int × Int) :=
  (terminal "hello" $> 1) >>= (fun a => terminal "goodbye" $> (a, 2))
-- NOTE(maemre): the commented-out tests crash
#guard (runParserO (μ := Option) concatParser "hello").1.toList == []
#guard (runParserO (μ := Option) concatParser "goodbye").1.toList == []
#guard (runParserO (μ := Option) concatParser "hellogoodbye").1.toList == [(12, some (1, 2))]
-- #guard (runParser.{0} (μ := List) concatParser "hello").1.toList == []
#guard (runParserO (μ := List) concatParser "goodbye").1.toList == []
-- #guard (runParser.{0} (μ := List) (concatParser ()) "hellogoodbye").1.toList == [(12, some (1, 2))]

-- An ambiguous ε-free parser
def concatParser2 [CollectionLike μ] [Traversable μ] : Parser (tag := tag) UChar μ PUnit :=
  let p1 := terminal "a" <|> terminal "aa"
  p1 >>= fun _ => p1 $> PUnit.unit

-- Ambiguity under Option vs. List
#guard (runParserO (μ := Option) concatParser2 "").1.toList == []
#guard (runParserO (μ := Option) concatParser2 "a").1.toList == []
#guard (runParserO (μ := Option) concatParser2 "aa").1.toList == [(2, some PUnit.unit)]
#guard (runParserO (μ := Option) concatParser2 "aaa").1.toList == [(2, some PUnit.unit), (3, some PUnit.unit)]

#guard (runParserO (μ := List) concatParser2 "").1.toList == []
-- NOTE(maemre): The code below crashes for some reason
-- #eval (runParser.{0} (μ := List) concatParser2 "a").1.toList == []
-- #eval (runParser.{0} (μ := List) concatParser2 "aa").1.toList

@[inline]
def concat [CollectionLike μ] [Traversable μ] [Append α] (p₁ p₂ : Parser (tag := tag) β μ α)
    : Parser (tag := tag) β μ α := liftA2 Append.append p₁ p₂

instance [Append α] : Append (ULift α) where
  append a b := ULift.up $ a.down ++ b.down

-- recursion via the inner parser function
partial def recursiveParser [CollectionLike μ] [Traversable μ] : Parser (tag := tag) UChar μ UString :=
  let p1 : Parser (tag := tag) UChar μ UString := terminal "a"
  let p2 : Parser (tag := tag) UChar μ UString := terminal "b"
  (concat p1 recursiveParser <|> p2)

#guard (runParserO (μ := Option) recursiveParser "ab").1.toList == [(2, some $ ULift.up "ab")]

-- bounded recursion for a single parser
def withFuel [CollectionLike μ] [Traversable μ] (g : Parser (tag := tag) β μ α → Parser (tag := tag) β μ α) : ℕ → Parser (tag := tag) β μ α
  | 0 => failure
  | Nat.succ fuel => g (withFuel g fuel)

def fueledParser [CollectionLike μ] [Traversable μ] : ℕ → Parser (tag := tag) UChar μ UString := withFuel $ fun recur =>
  let p1 : Parser (tag := tag) UChar μ UString := terminal "a"
  let p2 : Parser (tag := tag) UChar μ UString := terminal "b"
  (concat p1 recur <|> p2)

#guard (runParserO (μ := Option) (fueledParser 4) "aaab").1.toList = [(4, some { down := "aaab" })]
#guard (runParserO (μ := Option) (fueledParser 3) "aaab").1.toList = []

-- bounded recursion for parser families
def withFuel' {τ'} [CollectionLike μ] [Traversable μ] (g : (τ' → Parser (tag := tag) β μ α) → τ' → Parser (tag := tag) β μ α) : ℕ → (t : τ') → Parser (tag := tag) β μ α
  | 0 => fun _ => failure
  | Nat.succ fuel => g (withFuel' g fuel)

/-
X₀ -> a X₁ | c
X₁ -> b X₀

X₀ =>⋆ (ab⋆)c
-/
def mutualRec : ℕ → Parser (tag := tag) UChar Option UString := flip (withFuel' (τ' := Fin 2) $ fun recur t =>
  match t with
    | 0 =>
      -- A
      concat (terminal "a") (recur 1) <|> terminal "c"
    | 1 =>
      -- B
      concat (terminal "b") (recur 0)
  ) (0 : Fin 2)

#guard (runParserO (mutualRec 5) "ababc").1.toList == [(5, some { down := "ababc" })]
#guard (runParserO (mutualRec 4) "ababc").1.toList == []

-- Induction theorem for bounded recursion
theorem withFuel'_induction {τ} [CollectionLike μ] [Traversable μ] {g : (τ → Parser (tag := tag) β μ α) → τ → Parser (tag := tag) β μ α}
  {p : (τ → Parser (tag := tag) β μ α) → Prop}
  (h_base : p (fun _ => failure))
  (h_recur : ∀ recur, p recur -> p (g recur))
  (n : ℕ)
    : p (withFuel' g n) := by induction n with
  | zero =>
    unfold withFuel'
    exact h_base
  | succ n' ih =>
    unfold withFuel'
    exact h_recur (withFuel' g n') ih

-- want something this:
def memo [CollectionLike μ] [Traversable μ] (g : Parser (tag := tag) β μ α → Parser (tag := tag) β μ α) : Parser (tag := tag) β μ α :=
  sorry

def memo' {τ} [CollectionLike μ] [Traversable μ] (g : (τ → Parser (tag := tag) β μ α) → τ → Parser (tag := tag) β μ α) : τ → Parser (tag := tag) β μ α :=
  sorry

-- this just defines a subset-like relation on the parse results, the details of implementation
-- aren't that crucial
def subsumed [CollectionLike μ] [Traversable μ] (a b : Std.HashMap Int (μ α)) : Prop :=
  ∀ k (h : k ∈ a), (a[k]'h <|> b[k]?.getD failure) = b[k]?.getD failure

infix:50 " ≼ " => subsumed

-- then, we want:
theorem memo_sound [CollectionLike μ] [Traversable μ] (g : Parser (tag := tag) β μ α → Parser (tag := tag) β μ α) n s
    : (runParser (withFuel g n) s).1 ≼ (runParser (μ := μ) (memo g) s).1 := by
  sorry

theorem memo_complete [CollectionLike μ] [Traversable μ] (g : Parser (tag := tag) β μ α → Parser (tag := tag) β μ α) s
    : ∃ n, (runParser (μ := μ) (memo g) s).1 ≼ (runParser (withFuel g n) s).1 := by
  sorry

def mutualRecMemo : Parser (τ := Fin 2) (tag := fun _ => UString) UChar Option UString := (memoize $ fun recur t =>
  match t with
    | 0 =>
      -- A
      concat (terminal "a") (recur 1) <|> terminal "c"
    | 1 =>
      -- B
      concat (terminal "b") (recur 0)
  ) (0 : Fin 2)

#guard (runParser' mutualRecMemo "ababc").1.toList == [(5, some { down := "ababc" })]


-- S -> S a | a
def leftRecMemo : Parser (τ := Unit) (tag := fun _ => UString) UChar Option UString := (memoize $ fun recur (_: Unit) =>
  concat (recur ()) (terminal "a") <|> terminal "a"
  ) ()

-- this still causes stack overflow because we don't have left recursion detection
-- #guard (runParser' leftRecMemo "aaa").1.toList == [(5, some { down := "aaa" })]
