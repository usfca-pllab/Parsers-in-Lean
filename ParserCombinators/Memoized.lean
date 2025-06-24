-- A sketch of the port of the memoized combinators from Haskell, without the
-- CPS transformation

import Std.Data.DHashMap.Basic
import Std.Data.HashMap.Basic
import Std.Data.HashMap.AdditionalOperations

variable { α : Type }  { μ : Type → Type }

structure Tag (α : Type) where
  id : Int
  deriving DecidableEq
  -- TODO: Can we add the below change here for code cleanup?

-- Is this necessary? I feel like DecidableEq does this, but maybe I'm misunderstanding what DecidableEq does?
-- I looked it up and it looks like we could just do this on line 13:
-- deriving DecidableEq, BEq, Hashable (we still need BEq to be added as an instance, but Lean can
-- supposedly do it for us??)
instance : BEq (Tag α) where
  beq t u := t.id == u.id

instance : Hashable (Tag α) where
  hash t := hash t.id

def resultType (tag : Tag α) := α

-- TODO: derive hashable instances so we need it only for α
--
-- Also enforce some inequality constraint on carried types for tags?
-- Like if t : Tag α, u : Tag β then u == v → α = β

-- TODO: Would type erasure be a better solution?
-- Here's why I think it would be:
---- It's a simpler approach from a design perspective.
---- While it would lead to a higher risk of runtime failures in theory, I think we could easily
---- encapsulate the lack of safety into one, guaranteed-to-compile function for memoization
---- This function would be something we write with guarantees that if we're at a specific cache slot, we could
---- ONLY have previously executed on the exact same parser (and thus it would have the exact same type)
---- Does this mean that we have more responsibility? Yes, but we only have to have that responsibility in one
---- specific "unsafe" function, and we could build the rest of our library on that function safely (AND elegantly, IMO)
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
  getState : Int -> (StateT MemoData) (ReaderM String) (Std.HashMap Int (μ α))


instance [Monad μ] : Functor (Parser μ) where
  map f x := ⟨ Functor.map (Std.HashMap.map (fun _ => Functor.map f)) ∘ x.getState ⟩

-- N.B. Have to define `pure` separately so that we can use it in `seq`
instance [Monad μ] : Pure (Parser μ) where
  pure a := ⟨fun pos => pure {(pos, pure a)}⟩

-- might need other type class instances (e.g. to make fold work)
-- also, you may need to define or find a fold operation for Std.HashMap
instance [Monad μ] [Alternative μ] : Bind (Parser μ) where
  bind := sorry

instance [Monad μ] [Alternative μ] : Applicative (Parser μ) where
  -- derived from the Monad laws
  seq f x := bind (x ()) (fun a => bind f (fun b => pure (b a)))

instance [Monad μ] [Alternative μ] : Alternative (Parser μ) where
  failure := sorry -- empty in Haskell
  orElse r1 r2 := sorry -- (<|>) in Haskell but r2 is lazy

instance [Monad μ] [Alternative μ] : Monad (Parser μ) where
