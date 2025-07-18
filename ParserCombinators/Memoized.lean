-- A sketch of the port of the memoized combinators from Haskell, without the
-- CPS transformation

import Std.Data.DHashMap.Basic
import Std.Data.HashMap.Basic
import Std.Data.HashMap.AdditionalOperations
import Std.Data.HashMap.Lemmas
import Mathlib.Control.Traversable.Basic
import Mathlib.Control.Fold
import Aesop

universe u v
variable { α : Type u }  { μ : Type u → Type u }

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

def liftA2 {F : Type u → Type v} [Applicative F] {α β γ : Type u} (f : α → β → γ) (fa : F α) (fb : F β) : F γ :=
  f <$> fa <*> fb

def joinUnderCache {γ} [Monad μ] [Alternative μ] (s1 s2 : StateT MemoData (ReaderM UString) (Std.HashMap Int (μ γ))) : StateT MemoData (ReaderM UString) (Std.HashMap Int (μ γ)) :=
  liftA2 (fun m1 m2 => Std.HashMap.unionWith m1 m2 (fun v1 v2 => v1 <|> v2)) s1 s2

abbrev ParserState (μ : Type u → Type u) [Monad μ] (α : Type u) :=
  StateT MemoData (ReaderM UString) (Std.HashMap Int (μ α))

-- Some of the α's here should become existential/hidden
structure Parser (μ : Type u → Type u) [Monad μ] (α : Type u) where
  -- getState : Int -> (StateT MemoData) (ReaderM UString) (Std.HashMap Int (μ α))
  getState : Int → StateT MemoData (ReaderM UString) (Std.HashMap Int (μ α))

instance [Monad μ] : Functor (Parser μ) where
  map f x := ⟨ Functor.map (Std.HashMap.map (fun _ => Functor.map f)) ∘ x.getState ⟩

-- N.B. Have to define `pure` separately so that we can use it in `seq`
-- Defines the ability to create the simplest parser possible
instance [Monad μ] : Pure (Parser μ) where
  pure a := ⟨fun pos => pure {(pos, pure a)}⟩

-- might need other type class instances (e.g. to make fold work)
-- also, you may need to define or find a fold operation for Std.HashMap
instance [Monad μ] [Alternative μ] [Traversable μ] : Bind (Parser μ) where
  bind {_ β} x f := {
    getState := fun pos => do
      let pivotToResult ← x.getState pos
      let actions : List (μ (StateT MemoData (ReaderM UString) (Std.HashMap Int (μ β)))) :=
        pivotToResult.toList.map (fun (j, ma) => (fun a => (f a).getState j) <$> ma)
      actions.foldl
        (Traversable.foldl joinUnderCache)
        (pure Std.HashMap.emptyWithCapacity)
  }

instance [Monad μ] [Alternative μ] [Traversable μ] : Monad (Parser μ) where

instance [Monad μ] [Alternative μ] [Traversable μ] : Alternative (Parser μ) where
  failure := { getState := fun _ => pure Std.HashMap.emptyWithCapacity }
  orElse r1 r2 := {
    getState := fun pos =>
      let s1 := r1.getState pos
      let s2 := (r2 ()).getState pos
      joinUnderCache s1 s2
  }

def epsilon [Monad μ] : Parser μ PUnit := {
  getState := fun pos => pure {(pos, pure $ PUnit.unit)}
}

def terminal [Monad μ] [Alternative μ] (s : String) : Parser μ UString := {
  getState := fun pos => do
    let input ← read
    if pos >= 0 && s.isPrefixOf (input.down.drop pos.toNat) then
      let endPos := pos + s.length
      pure {(endPos, pure $ ULift.up s)}
    else
      pure Std.HashMap.emptyWithCapacity
}

def memoize [TypeName α] [Monad μ] [TypeName (μ α)] (tag : Tag) (p : Parser μ α) : Parser μ α := {
  getState := fun pos => do
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
          let results ← p.getState pos
          -- Cache the new results
          let newPositionMap := results.fold (fun acc newPos result =>
            acc.insert newPos (Dynamic.mk result)) positionMap
          let newTable := memo.table.insert tag newPositionMap
          set { memo with table := newTable }
          pure results
      | none =>
        -- No cached result for this position, compute and cache
        let results ← p.getState pos
        -- Cache the new results
        let newPositionMap := results.fold (fun acc newPos result =>
          acc.insert newPos (Dynamic.mk result)) positionMap
        let newTable := memo.table.insert tag newPositionMap
        set { memo with table := newTable }
        pure results
    | none =>
      -- No entry for this tag at all, so we compute it and cache it
      let results ← p.getState pos
      -- Create new position map and cache the results
      let newPositionMap := results.fold (fun acc newPos result =>
        acc.insert newPos (Dynamic.mk result)) Std.HashMap.emptyWithCapacity
      let newTable := memo.table.insert tag newPositionMap
      set { memo with table := newTable }
      pure results
}

-- Testing

-- Will use `Option` as the concrete monad (some is success and none is failure)

def runParser [Monad μ] (p : Parser μ α) (input : String) (pos : Int := 0) : (Std.HashMap Int (μ α)) × MemoData :=
  let stateTResult := (p.getState pos).run startState
  let readerResult := stateTResult.run $ ULift.up input
  readerResult

-- Checking to make sure that runParser has correct type
#guard (runParser.{0} (μ := Option) epsilon "test").1.toList == [(0, some PUnit.unit)]

-- Testing running the parsers (had to extract just the hashmap
-- because Lean couldn't extract a string from the full return type)
#guard (runParser.{0} (μ := Option) (terminal "hello") "hello world").1.toList == [(5, some $ ULift.up "hello")]
#guard (runParser.{0} (μ := Option) (terminal "wo") "hello world" 6).1.toList == [(8, some $ ULift.up "wo")]

-- Failure
#guard (runParser.{0} (μ := Option) (terminal "llo") "hello world" 5).1.isEmpty

-- Edge case for empty string
#guard (runParser.{0} (μ := Option) (terminal "") "hello world" 6).1.toList == [(6, some $ ULift.up "")]


-- Testing instances:

-- Functor (`<$>`)
def funcParser : Parser Option String := (fun _ => "matched!") <$> terminal "hello"
def funcParser2 : Parser Option Int := (fun x => x * 3) <$> terminal "hello" $> 2

-- TODO: (Madi) Just beef this up by testing edge cases
#guard (runParser (μ := Option) funcParser "hello world").1.toList == [(5, some "matched!")]
#guard (runParser (μ := Option) funcParser "hell").1.toList == []
#guard (runParser (μ := Option) funcParser2 "hello").1.toList == [(5, some 6)]

-- Alternative (`<|>`)
def altParser [Monad μ] [Alternative μ] [Traversable μ] : Parser μ UString :=
  terminal "hello" <|> terminal "goodbye"

#guard (runParser.{0} (μ := Option) altParser "hello").1.toList == [(5, some $ ULift.up "hello")]
#guard (runParser.{0} (μ := Option) altParser "goodbye").1.toList == [(7, some $ ULift.up "goodbye")]
#guard (runParser.{0} (μ := List) altParser "hello").1.toList == [(5, [ULift.up "hello"])]
#guard (runParser.{0} (μ := List) altParser "goodbye").1.toList == [(7, [ULift.up "goodbye"])]

-- Concatenation via bind (`>>=`)
def concatParser {μ : Type → Type} [Monad μ] [Alternative μ] [Traversable μ] : Parser μ (Int × Int) :=
  (terminal "hello" $> 1) >>= (fun a => terminal "goodbye" $> (a, 2))
-- NOTE(maemre): the commented-out tests crash
#guard (runParser.{0} (μ := Option) concatParser "hello").1.toList == []
#guard (runParser.{0} (μ := Option) concatParser "goodbye").1.toList == []
#guard (runParser.{0} (μ := Option) concatParser "hellogoodbye").1.toList == [(12, some (1, 2))]
-- #guard (runParser.{0} (μ := List) concatParser "hello").1.toList == []
#guard (runParser.{0} (μ := List) concatParser "goodbye").1.toList == []
-- #guard (runParser.{0} (μ := List) (concatParser ()) "hellogoodbye").1.toList == [(12, some (1, 2))]

-- An ambiguous ε-free parser
def concatParser2 [Monad μ] [Alternative μ] [Traversable μ] : Parser μ PUnit :=
  let p1 := terminal "a" <|> terminal "aa"
  p1 >>= fun _ => p1 $> PUnit.unit

-- Ambiguity under Option vs. List
#guard (runParser.{0} (μ := Option) concatParser2 "").1.toList == []
#guard (runParser.{0} (μ := Option) concatParser2 "a").1.toList == []
#guard (runParser.{0} (μ := Option) concatParser2 "aa").1.toList == [(2, some PUnit.unit)]
#guard (runParser.{0} (μ := Option) concatParser2 "aaa").1.toList == [(2, some PUnit.unit), (3, some PUnit.unit)]

#guard (runParser.{0} (μ := List) concatParser2 "").1.toList == []
-- NOTE(maemre): The code below crashes for some reason
-- #eval (runParser.{0} (μ := List) concatParser2 "a").1.toList == []
-- #eval (runParser.{0} (μ := List) concatParser2 "aa").1.toList

@[inline]
def concat [Monad μ] [Alternative μ] [Traversable μ] [Append α] (p₁ p₂ : Parser μ α)
    : Parser μ α := liftA2 Append.append p₁ p₂

instance [Append α] : Append (ULift α) where
  append a b := ULift.up $ a.down ++ b.down

-- recursion via the inner parser function
partial def recursiveParserF [Monad μ] [Alternative μ] [Traversable μ] (pos : Int) : ParserState μ UString :=
  let p1 := terminal "a"
  let p2 := terminal "b"
  let p : Parser μ UString := (concat p1 ⟨recursiveParserF⟩) <|> p2
  p.getState pos

def recursiveParser [Monad μ] [Alternative μ] [Traversable μ] : Parser μ UString := Parser.mk recursiveParserF

#guard (runParser.{0} (μ := Option) recursiveParser "ab").1.toList == [(2, some $ ULift.up "ab")]
