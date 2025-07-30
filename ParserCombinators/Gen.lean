/-

Parser generation from CFGs.

-/

import ParserCombinators.CFG
import ParserCombinators.Memoized

namespace Gen

universe u
variable {α ν : Type u} {μ : Type u → Type u} [Monad μ] [SemilatticeAlt μ] [Traversable μ] [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν]

open CFG
open ParseTree

abbrev tag (cfg : @CFG α ν) := Function.const ν (ParseTree cfg)

instance {cfg : @CFG α ν} (t : ν) : DecidableEq (tag cfg t) := by
  simp only [Function.const_apply]
  infer_instance

-- A generator function for a parser generator that discards the result.
--
-- g: input grammar
-- recur: for recursive calls
-- n: current nonterminal to parse
def gen' (cfg : @CFG α ν) (recur : ν → ParserM (tag := tag cfg) α μ (ParseTree cfg)) (n : ν)
    : ParserM (tag := tag cfg) α μ (ParseTree cfg) :=
  let parseSym (sym : Symbol α ν) : ParserM α μ (ParseTree cfg) := match sym with
    | Symbol.term a => ParseTree.Leaf <$> terminal' a
    | Symbol.nonterm n => recur n
  let parseRule (rule : {rule // rule ∈ cfg.rules n}) : ParserM α μ (ParseTree cfg) := do
    let children := List.map parseSym rule
    let children <- List.traverse id children
    pure $ ParseTree.Node n rule children
  ((cfg.rules n).attach.map parseRule).foldl ParserM.instMaxOfTraversableOfDecidableEq.max ⊥

def gen (cfg : @CFG α ν) : ℕ → ν → ParserM (tag := tag cfg) α μ (ParseTree cfg) := withFuel' $ gen' cfg

-- TODO(maemre): correctness theorem (by injecting validity proofs above)
-- TODO(maemre): correctness theorem (sound/complete)

-- abbrev sound (cfg : @CFG α ν) [Membership (ParseTree cfg) (μ (ParseTree cfg))]
--   (n : ν) (p : ParserM (tag := tag cfg) α μ (ParseTree cfg)) (input : Array α)
--   := ∀ tree ∈ (runParser p input).1[(0 : Int)]?.getD failure, tree.Valid ∧ tree.root = Symbol.nonterm n
--
-- abbrev complete (cfg : @CFG α ν) [Membership (ParseTree cfg) (μ (ParseTree cfg))] (n : ν) (p : Parser (tag := tag cfg) α μ (ParseTree cfg)) (input : Array α)
--   (h : cfg.derives [Symbol.nonterm n] (input.toList.map Symbol.term))
--   := ∃ tree, tree ∈ (runParser p input).1[(0 : Int)]?.getD failure

-- omit [BEq α] [DecidableEq α] in
-- lemma failure_empty : (runParser (failure : ParserM (tag := tag) α μ γ) input).1.isEmpty := by
--   rfl

-- theorem failure_sound (cfg : @CFG α ν) [Membership (ParseTree cfg) (μ (ParseTree cfg))] (n : ν) (input : Array α) : sound (μ := μ) cfg n failure input
--   := by
--   unfold sound
--   intro tree h
--   simp [Std.HashMap.getElem?_of_isEmpty, failure_empty] at h
--   sorry -- add a new type-class

end Gen
