-- A sketch of the port of the memoized combinators from Haskell, without the
-- CPS transformation

import Std.Data.DHashMap.Basic
import Std.Data.HashMap.Basic
import Std.Data.HashMap.AdditionalOperations
import Std.Data.HashMap.Lemmas
import Mathlib.Control.Traversable.Basic
import Mathlib.Control.Fold
import Aesop

-- β is the alphabet: parsers work over Array β
universe u v
variable { α β : Type u } { μ : Type u → Type u } [BEq β]

-- Tags for each parser, these don't carry type information.
--
-- NOTE(maemre): A better option would be to use pointers to the parser functions as keys,
-- but I am not sure if that runs into issues with the termination checker.
--
-- If we want, we can store the type names here later.
structure Tag where
  id : Int
  deriving DecidableEq, BEq, Hashable

structure MemoData : Type v where
  nextTag : Int -- need only the data inside
  table : Std.HashMap Tag (Std.HashMap Int Dynamic)

def startState : MemoData := {
  nextTag := 0
  table := Std.HashMap.emptyWithCapacity
}

abbrev Memo (β : Type v) := StateM MemoData β

abbrev UChar := ULift Char
abbrev UString := ULift String

def fresh : Memo Tag := do
  let memo <- get
  set { memo with nextTag := memo.nextTag + 1 }
  pure ⟨ memo.nextTag ⟩

namespace Std.HashMap
def unionWith {K V} [BEq K] [Hashable K] (m1 m2 : Std.HashMap K V) (f : V → V → V) : Std.HashMap K V :=
  m2.fold (fun m k v2 =>
    match m[k]? with
    -- Collision case, meshes the two values found into one new value (based on the given function `f`)
    | some v1 => m.insert k (f v1 v2)
    -- New key case, juar adds the value we found
    | none => m.insert k v2) m1
end Std.HashMap

@[inline]
def liftA2 {F : Type u → Type v} [Applicative F] {α β γ : Type u} (f : α → β → γ) (fa : F α) (fb : F β) : F γ :=
  f <$> fa <*> fb

def joinUnderCache {β γ} [Monad μ] [Alternative μ] (s1 s2 : StateT MemoData (ReaderM (Array β)) (Std.HashMap Int (μ γ))) : StateT MemoData (ReaderM (Array β)) (Std.HashMap Int (μ γ)) :=
  liftA2 (fun m1 m2 => Std.HashMap.unionWith m1 m2 (fun v1 v2 => v1 <|> v2)) s1 s2

abbrev ParserState (μ : Type u → Type u) [Monad μ] (α : Type u) :=
  StateT MemoData (ReaderM (Array β)) (Std.HashMap Int (μ α))

-- Some of the α's here should become existential/hidden
abbrev Parser (β : Type u) (μ : Type u → Type u) [Monad μ] (α : Type u) :=
  Int → StateT MemoData (ReaderM (Array β)) (Std.HashMap Int (μ α))

instance [Monad μ] : Functor (Parser β μ) where
  map f x := Functor.map (Std.HashMap.map (fun _ => Functor.map f)) ∘ x

-- N.B. Have to define `pure` separately so that we can use it in `seq`
-- Defines the ability to create the simplest parser possible
instance [Monad μ] : Pure (Parser β μ) where
  pure a := fun pos => pure {(pos, pure a)}

-- might need other type class instances (e.g. to make fold work)
-- also, you may need to define or find a fold operation for Std.HashMap
instance [Monad μ] [Alternative μ] [Traversable μ] : Bind (Parser β μ) where
  bind {_ β'} x f := fun pos => do
      let pivotToResult ← x pos
      let actions : List (μ (StateT MemoData (ReaderM (Array β)) (Std.HashMap Int (μ β')))) :=
        pivotToResult.toList.map (fun (j, ma) => (fun a => f a j) <$> ma)
      actions.foldl
        (Traversable.foldl joinUnderCache)
        (pure Std.HashMap.emptyWithCapacity)

instance [Monad μ] [Alternative μ] [Traversable μ] : Monad (Parser β μ) where

instance [Monad μ] [Alternative μ] [Traversable μ] : Alternative (Parser β μ) where
  failure _pos := pure Std.HashMap.emptyWithCapacity
  orElse r1 r2 pos :=
    let s1 := r1 pos
    let s2 := r2 () pos
    joinUnderCache s1 s2

def epsilon [Monad μ] : Parser β μ PUnit := fun pos => pure {(pos, pure $ PUnit.unit)}

def terminal [Monad μ] [Alternative μ] (s : String) : Parser UChar μ UString := fun pos => do
  let input ← read
  if pos >= 0 && (s.data.map ULift.up).toArray.isPrefixOf (input.extract pos.toNat) then
    let endPos := pos + s.length
    pure {(endPos, pure $ ULift.up s)}
  else
    pure Std.HashMap.emptyWithCapacity

def terminal' [Monad μ] [Alternative μ] (t: β) : Parser β μ β := fun pos => do
  let input ← read
  if pos >= 0 && some t == input[pos.toNat]? then
    pure {(pos + 1, pure t)}
  else
    pure Std.HashMap.emptyWithCapacity

def memoize [TypeName α] [Monad μ] [TypeName (μ α)] (tag : Tag) (p : Parser β μ α) : Parser β μ α :=
  fun pos => do
    let memo ← get
    -- Check if we have cached results for this tag and position
    match memo.table[tag]? with
    | some positionMap =>
      match positionMap[pos]? with
      | some dynamicResult =>
        -- We have a cached result, try to unbox it
        match dynamicResult.get? (μ α) with
        | some cachedResult => pure {(pos, cachedResult)}
        | none =>
          -- Type mismatch in cache, recompute
          let results ← p pos
          -- Cache the new results
          let newPositionMap := results.fold (fun acc newPos result =>
            acc.insert newPos (Dynamic.mk result)) positionMap
          let newTable := memo.table.insert tag newPositionMap
          set { memo with table := newTable }
          pure results
      | none =>
        -- No cached result for this position, compute and cache
        let results ← p pos
        -- Cache the new results
        let newPositionMap := results.fold (fun acc newPos result =>
          acc.insert newPos (Dynamic.mk result)) positionMap
        let newTable := memo.table.insert tag newPositionMap
        set { memo with table := newTable }
        pure results
    | none =>
      -- No entry for this tag at all, so we compute it and cache it
      let results ← p pos
      -- Create new position map and cache the results
      let newPositionMap := results.fold (fun acc newPos result =>
        acc.insert newPos (Dynamic.mk result)) Std.HashMap.emptyWithCapacity
      let newTable := memo.table.insert tag newPositionMap
      set { memo with table := newTable }
      pure results

-- Testing

-- Will use `Option` as the concrete monad (some is success and none is failure)

def runParser [Monad μ] (p : Parser β μ α) (input : Array β) (pos : Int := 0) : (Std.HashMap Int (μ α)) × MemoData :=
  let stateTResult := (p pos).run startState
  let readerResult := stateTResult.run input
  readerResult

def runParser' [Monad μ] (p : Parser UChar μ α) (input : String) (pos : Int := 0) : (Std.HashMap Int (μ α)) × MemoData :=
  runParser p (input.toList.map ULift.up).toArray pos


-- Checking to make sure that runParser has correct type
#guard (runParser'.{0} (μ := Option) epsilon "test").1.toList == [(0, some PUnit.unit)]

-- Testing running the parsers (had to extract just the hashmap
-- because Lean couldn't extract a string from the full return type)
#guard (runParser'.{0} (μ := Option) (terminal "hello") "hello world").1.toList == [(5, some $ ULift.up "hello")]
#guard (runParser'.{0} (μ := Option) (terminal "wo") "hello world" 6).1.toList == [(8, some $ ULift.up "wo")]

-- Failure
#guard (runParser'.{0} (μ := Option) (terminal "llo") "hello world" 5).1.isEmpty

-- Edge case for empty string
#guard (runParser'.{0} (μ := Option) (terminal "") "hello world" 6).1.toList == [(6, some $ ULift.up "")]


-- Testing instances:

-- Functor (`<$>`)
def funcParser : Parser UChar Option String := (fun _ => "matched!") <$> terminal "hello"
def funcParser2 : Parser UChar Option Int := (fun x => x * 3) <$> terminal "hello" $> 2

-- TODO: (Madi) Just beef this up by testing edge cases
#guard (runParser' (μ := Option) funcParser "hello world").1.toList == [(5, some "matched!")]
#guard (runParser' (μ := Option) funcParser "hell").1.toList == []
#guard (runParser' (μ := Option) funcParser2 "hello").1.toList == [(5, some 6)]

-- Alternative (`<|>`)
def altParser [Monad μ] [Alternative μ] [Traversable μ] : Parser  UChar μ UString :=
  terminal "hello" <|> terminal "goodbye"

#guard (runParser'.{0} (μ := Option) altParser "hello").1.toList == [(5, some $ ULift.up "hello")]
#guard (runParser'.{0} (μ := Option) altParser "goodbye").1.toList == [(7, some $ ULift.up "goodbye")]
#guard (runParser'.{0} (μ := List) altParser "hello").1.toList == [(5, [ULift.up "hello"])]
#guard (runParser'.{0} (μ := List) altParser "goodbye").1.toList == [(7, [ULift.up "goodbye"])]

-- Concatenation via bind (`>>=`)
def concatParser {μ : Type → Type} [Monad μ] [Alternative μ] [Traversable μ] : Parser UChar μ (Int × Int) :=
  (terminal "hello" $> 1) >>= (fun a => terminal "goodbye" $> (a, 2))
-- NOTE(maemre): the commented-out tests crash
#guard (runParser'.{0} (μ := Option) concatParser "hello").1.toList == []
#guard (runParser'.{0} (μ := Option) concatParser "goodbye").1.toList == []
#guard (runParser'.{0} (μ := Option) concatParser "hellogoodbye").1.toList == [(12, some (1, 2))]
-- #guard (runParser.{0} (μ := List) concatParser "hello").1.toList == []
#guard (runParser'.{0} (μ := List) concatParser "goodbye").1.toList == []
-- #guard (runParser.{0} (μ := List) (concatParser ()) "hellogoodbye").1.toList == [(12, some (1, 2))]

-- An ambiguous ε-free parser
def concatParser2 [Monad μ] [Alternative μ] [Traversable μ] : Parser UChar μ PUnit :=
  let p1 := terminal "a" <|> terminal "aa"
  p1 >>= fun _ => p1 $> PUnit.unit

-- Ambiguity under Option vs. List
#guard (runParser'.{0} (μ := Option) concatParser2 "").1.toList == []
#guard (runParser'.{0} (μ := Option) concatParser2 "a").1.toList == []
#guard (runParser'.{0} (μ := Option) concatParser2 "aa").1.toList == [(2, some PUnit.unit)]
#guard (runParser'.{0} (μ := Option) concatParser2 "aaa").1.toList == [(2, some PUnit.unit), (3, some PUnit.unit)]

#guard (runParser'.{0} (μ := List) concatParser2 "").1.toList == []
-- NOTE(maemre): The code below crashes for some reason
-- #eval (runParser.{0} (μ := List) concatParser2 "a").1.toList == []
-- #eval (runParser.{0} (μ := List) concatParser2 "aa").1.toList

@[inline]
def concat [Monad μ] [Alternative μ] [Traversable μ] [Append α] (p₁ p₂ : Parser β μ α)
    : Parser β μ α := liftA2 Append.append p₁ p₂

instance [Append α] : Append (ULift α) where
  append a b := ULift.up $ a.down ++ b.down

-- recursion via the inner parser function
partial def recursiveParser [Monad μ] [Alternative μ] [Traversable μ] : Parser UChar μ UString :=
  let p1 : Parser UChar μ UString := terminal "a"
  let p2 : Parser UChar μ UString := terminal "b"
  (concat p1 recursiveParser <|> p2)

#guard (runParser'.{0} (μ := Option) recursiveParser "ab").1.toList == [(2, some $ ULift.up "ab")]

-- bounded recursion for a single parser
def withFuel [Monad μ] [Alternative μ] [Traversable μ] (g : Parser β μ α → Parser β μ α) : ℕ → Parser β μ α
  | 0 => failure
  | Nat.succ fuel => g (withFuel g fuel)

def fueledParser [Monad μ] [Alternative μ] [Traversable μ] : ℕ → Parser UChar μ UString := withFuel $ fun recur =>
  let p1 : Parser UChar μ UString := terminal "a"
  let p2 : Parser UChar μ UString := terminal "b"
  (concat p1 recur <|> p2)

#guard (runParser'.{0} (μ := Option) (fueledParser 4) "aaab").1.toList = [(4, some { down := "aaab" })]
#guard (runParser'.{0} (μ := Option) (fueledParser 3) "aaab").1.toList = []

-- bounded recursion for parser families
def withFuel' {τ} [Monad μ] [Alternative μ] [Traversable μ] (g : (τ → Parser β μ α) → τ → Parser β μ α) : ℕ → (t : τ) → Parser β μ α
  | 0 => fun _ => failure
  | Nat.succ fuel => g (withFuel' g fuel)

/-
X₀ -> a X₁ | c
X₁ -> b X₀

X₀ =>⋆ (ab⋆)c
-/
def mutualRec : ℕ → Parser UChar Option UString := flip (withFuel' (τ := Fin 2) (fun recur t =>
  match t with
  | 0 =>
    -- A
    concat (terminal "a") (recur 1) <|> terminal "c"
  | 1 =>
    -- B
    concat (terminal "b") (recur 0)
)) (0 : Fin 2)

#guard (runParser'.{0} (mutualRec 5) "ababc").1.toList == [(5, some { down := "ababc" })]
#guard (runParser'.{0} (mutualRec 4) "ababc").1.toList == []

-- Induction theorem for bounded recursion
theorem withFuel'_induction {τ} [Monad μ] [Alternative μ] [Traversable μ] {g : (τ → Parser β μ α) → τ → Parser β μ α}
  {p : (τ → Parser β μ α) → Prop}
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
def memo [Monad μ] [Alternative μ] [Traversable μ] (g : Parser β μ α → Parser β μ α) : Parser β μ α :=
  sorry

def memo' {τ} [Monad μ] [Alternative μ] [Traversable μ] (g : (τ → Parser β μ α) → τ → Parser β μ α) : τ → Parser β μ α :=
  sorry

-- this just defines a subset-like relation on the parse results, the details of implementation
-- aren't that crucial
def subsumed [Monad μ] [Alternative μ] [Traversable μ] (a b : Std.HashMap Int (μ α)) : Prop :=
  ∀ k (h : k ∈ a), (a[k]'h <|> b[k]?.getD failure) = b[k]?.getD failure

infix:50 " ≼ " => subsumed

-- then, we want:
theorem memo_sound [Monad μ] [Alternative μ] [Traversable μ] (g : Parser β μ α → Parser β μ α) n s
    : (runParser (withFuel g n) s).1 ≼ (runParser (μ := μ) (memo g) s).1 := by
  sorry

theorem memo_complete [Monad μ] [Alternative μ] [Traversable μ] (g : Parser β μ α → Parser β μ α) s
    : ∃ n, (runParser (μ := μ) (memo g) s).1 ≼ (runParser (withFuel g n) s).1 := by
  sorry
