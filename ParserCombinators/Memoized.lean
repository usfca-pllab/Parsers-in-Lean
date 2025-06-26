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

-- Some of the α's here should become existential/hidden
structure Parser (μ : Type -> Type) [Monad μ] (α : Type) where
  getState : Int -> (StateT MemoData) (ReaderM String) (Std.HashMap Int (μ α))

instance [Monad μ] : Functor (Parser μ) where
  map f x := ⟨ Functor.map (Std.HashMap.map (fun _ => Functor.map f)) ∘ x.getState ⟩

-- N.B. Have to define `pure` separately so that we can use it in `seq`
instance [Monad μ] : Pure (Parser μ) where
  pure a := ⟨fun pos => pure {(pos, pure a)}⟩

-- might need other type class instances (e.g. to make fold work)
-- also, you may need to define or find a fold operation for Std.HashMap
instance [Monad μ] [Alternative μ] : Bind (Parser μ) where
  bind {α β} x f := {
    -- This is the function that will get us our new parser after calling bind
    getState := fun pos => do
    -- TODO: (Madi) I know fresh needs to be in here (right now it's not getting the correct tag, right?) but I can't figure out how to make it work
    let memo ← get
    let tagX : Tag := { id := memo.nextTag }
    match memo.table[tagX]? with
    -- Cache hit:
    | some cachedResults => (sorry : StateT MemoData (ReaderM String) (Std.HashMap Int (μ β)))
    -- TODO: (Madi)
    -- Retrieve the results that I got using the current `pos`, cast them from Dynamic back to μ β
    -- Needed to explicitly name the type of sorry apparently? Because it wouldn't compile otherwise
    -- Cache miss:
    | none => sorry
    -- TODO: (Madi)
    -- Actually do the computation and cache the results in the table
  }
instance [Monad μ] [Alternative μ] : Applicative (Parser μ) where
  -- derived from the Monad laws
  seq f x := bind (x ()) (fun a => bind f (fun b => pure (b a)))

instance [Monad μ] [Alternative μ] : Alternative (Parser μ) where
  failure := sorry -- empty in Haskell
  orElse r1 r2 := sorry -- (<|>) in Haskell but r2 is lazy

instance [Monad μ] [Alternative μ] : Monad (Parser μ) where
