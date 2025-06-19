-- A sketch of the port of the memoized combinators from Haskell, without the
-- CPS transformation

import Std.Data.DHashMap.Basic
import Std.Data.HashMap.Basic

variable { α : Type }  { μ : Type → Type }

structure Tag (α : Type) where
  id : Int
  deriving DecidableEq

instance : BEq (Tag α) where
  beq t u := t.id == u.id

instance : Hashable (Tag α) where
  hash t := hash t.id

def resultType (tag : Tag α) := α

-- TODO: derive hashable instances so we need it only for α
--
-- Also enforce some inequality constraint on carried types for tags?
-- Like if t : Tag α, u : Tag β then u == v → α = β
--
-- Also, the α should be pushed inside the table field as much as possible
structure MemoData [Hashable (Tag Unit)] [BEq (Tag Unit)] where
  nextTag : Int -- need only the data inside
  table : Std.DHashMap (Tag Unit) (fun t => Std.HashMap Int (resultType t))

def startState { α : Type } [Hashable (Tag α)] : MemoData := {
  nextTag := 0
  table := Std.DHashMap.empty
}

abbrev Memo (β : Type) := StateM MemoData β

def fresh : Memo (Tag α) := do
  let memo <- get
  set { memo with nextTag := memo.nextTag + 1 }
  pure ⟨ memo.nextTag ⟩

-- Some of the α's here should become existential/hidden
structure Parser (μ : Type -> Type) [Monad μ] (α : Type) where
  getState : Int -> (StateT MemoData) (ReaderM String) (Std.HashMap Int (μ a))


-- TODO: figure out if HashMap is not Functor?
-- instance [Monad μ] : Functor (Parser μ) where
--   map f x := ⟨ Functor.map ((Functor.map f) <$> _) ∘ x.getState ⟩
