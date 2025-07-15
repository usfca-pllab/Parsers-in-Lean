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

instance [Monad μ] [Alternative μ]  [Traversable μ] : Applicative (Parser μ) where
  -- derived from the Monad laws
  seq f x := bind (x ()) (fun a => bind f (fun b => pure (b a)))

instance [Monad μ] [Alternative μ] [Traversable μ] : Alternative (Parser μ) where
  failure := { getState := fun _ => pure Std.HashMap.emptyWithCapacity }
  orElse r1 r2 := {
    getState := fun pos =>
      let s1 := r1.getState pos
      let s2 := (r2 ()).getState pos
      joinUnderCache s1 s2
  }

instance [Monad μ] [Alternative μ] [Traversable μ] : Monad (Parser μ) where


def epsilon [Monad μ] : Parser μ PUnit := {
  getState := fun pos => pure {(pos, pure $ PUnit.unit)}
}

def terminal [Monad μ] [Alternative μ] (s : String) : Parser μ PUnit := {
  getState := fun pos => do
    let input ← read
    if pos >= 0 && s.isPrefixOf (input.down.drop pos.toNat) then
      let endPos := pos + s.length
      pure {(endPos, pure PUnit.unit)}
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
#check runParser (μ := Option) epsilon "test"

-- Testing running the parsers (had to extract just the hashmap
-- because Lean couldn't extract a string from the full return type)
#eval (runParser (μ := Option) (terminal "hello") "hello world").1


#eval (runParser (μ := Option) (terminal "wo") "hello world" 6).1

-- Failure
#eval (runParser (μ := Option) (terminal "llo") "hello world" 5).1

-- Edge case for empty string
#eval (runParser (μ := Option) (terminal "") "hello world" 6).1


-- Testing instances:

-- Functor (`<$>`)
def funcParser : Parser Option String := (fun _ => "matched!") <$> terminal "hello"

-- TODO: (Madi) Just beef this up by testing edge cases
#eval (runParser (μ := Option) funcParser "hello world").1


-- Alternative (`<|>`)
def altParser : Parser Option PUnit := (terminal "hello" : Parser Option PUnit) <|> (terminal "goodbye" : Parser Option PUnit)

#guard (runParser.{0} (μ := Option) altParser "hello").1.toList == [(5, some PUnit.unit)]
#guard (runParser.{0} (μ := Option) altParser "goodbye").1.toList == [(7, some PUnit.unit)]
