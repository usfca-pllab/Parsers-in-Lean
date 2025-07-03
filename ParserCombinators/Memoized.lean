-- A sketch of the port of the memoized combinators from Haskell, without the
-- CPS transformation

import Std.Data.DHashMap.Basic
import Std.Data.HashMap.Basic
import Std.Data.HashMap.AdditionalOperations
import Std.Data.HashMap.Lemmas

variable { α : Type }  { μ : Type → Type }

-- Tags for each parser, these don't carry type information.
--
-- NOTE(maemre): A better option would be to use pointers to the parser functions as keys,
-- but I am not sure if that runs into issues with the termination checker.
--
-- If we want, we can store the type names here later.
structure Tag where
  id : Int
  deriving DecidableEq, BEq, Hashable

structure MemoData where
  nextTag : Int -- need only the data inside
  table : Std.HashMap Tag (Std.HashMap Int Dynamic)

def startState : MemoData := {
  nextTag := 0
  table := Std.HashMap.empty
}

abbrev Memo (β : Type) := StateM MemoData β

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

def joinUnderCache {γ} [Monad μ] [Alternative μ] (s1 s2 : StateT MemoData (ReaderM String) (Std.HashMap Int (μ γ))) : StateT MemoData (ReaderM String) (Std.HashMap Int (μ γ)) :=
  liftA2 (fun m1 m2 => Std.HashMap.unionWith m1 m2 (fun v1 v2 => v1 <|> v2)) s1 s2

-- Some of the α's here should become existential/hidden
structure Parser (μ : Type → Type) [Monad μ] (α : Type) where
  -- getState : Int -> (StateT MemoData) (ReaderM String) (Std.HashMap Int (μ α))
  getState : Int → StateT MemoData (ReaderM String) (Std.HashMap Int (μ α))

instance [Monad μ] : Functor (Parser μ) where
  map f x := ⟨ Functor.map (Std.HashMap.map (fun _ => Functor.map f)) ∘ x.getState ⟩

-- N.B. Have to define `pure` separately so that we can use it in `seq`
-- Defines the ability to create the simplest parser possible
instance [Monad μ] : Pure (Parser μ) where
  pure a := ⟨fun pos => pure {(pos, pure a)}⟩

-- might need other type class instances (e.g. to make fold work)
-- also, you may need to define or find a fold operation for Std.HashMap
instance [Monad μ] [Alternative μ] [MonadLiftT μ (StateT MemoData (ReaderM String))] : Bind (Parser μ) where
  bind {_ β} x f := {
    -- This is the function that will get us our new parser after calling bind
    getState := fun pos => do
    -- Run first parser (`x`) starting at `pos`, results in `pivotToResult`
    --  (A HashMap with keys that are character indices where x successfully finished
    -- mapped to the result of that parse (wrapped in μ for failure / ambiguous cases)
      let pivotToResult ← x.getState pos
      -- Iterate over every successful parse, turn the map into a list of pairs
      -- TODO: (Madi) I feel like this step and the step below could be squished into one step
      -- but this way was clearer for me to figure out,
      -- so that could be a thing either I work on this coming week, or we do together today
      let actions : List (StateT MemoData (ReaderM String) (Std.HashMap Int (μ β))) :=
        pivotToResult.toList.map (fun (j, ma) =>
          -- TODO: (Madi) This is where the MonadLiftT restraint comes in, because we need to unwrap the value
          -- from /mu, and I couldn't get Lean to accept it unless I made it have `MonadLiftT`
          -- but maybe there's another way I don't know about?
          liftM ma >>= fun a => (f a).getState j
        )
      -- Then, we just combine all the results of all the possible paths that the parser can go down
      -- into one big HashMap, starting with an empty one
      actions.foldlM
        (fun acc m => joinUnderCache (pure acc) m)
        Std.HashMap.empty
  }

instance [Monad μ] [Alternative μ] [MonadLiftT μ (StateT MemoData (ReaderM String))] : Applicative (Parser μ) where
  -- derived from the Monad laws
  seq f x := bind (x ()) (fun a => bind f (fun b => pure (b a)))

instance [Monad μ] [Alternative μ] [MonadLiftT μ (StateT MemoData (ReaderM String))] : Alternative (Parser μ) where
  failure := { getState := fun _ => pure Std.HashMap.empty }
  orElse r1 r2 := {
    getState := fun pos =>
      let s1 := r1.getState pos
        -- (Madi) we want r2 to be lazy, so I made it of type Thunk (which I just learned about) and used it accordingly
      let s2 := (r2 ()).getState pos
      joinUnderCache s1 s2
  }

instance [Monad μ] [Alternative μ] [MonadLiftT μ (StateT MemoData (ReaderM String))] : Monad (Parser μ) where


def epsilon [Monad μ] : Parser μ Unit := {
  getState := fun pos => sorry
}

def terminal [Monad μ] [Alternative μ] (s : String) : Parser μ Unit := {
  getState := fun pos => sorry
}
