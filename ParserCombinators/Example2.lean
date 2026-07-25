import ParserCombinators.Memoized
import ParserCombinators.CFG

namespace Example2

open CFG Symbol ParseTree

inductive Terminal where
  | a
  | b
  | c
  deriving DecidableEq, Repr

inductive MyVars where
  | S
  deriving DecidableEq, Repr

open MyVars

/-

An ε-free, non-left-recursive grammar:

S → a S | a | b

-/
private def my_cfg : @CFG Terminal MyVars where
  start := S
  rules
    | S => [[term .a, nonterm S], [term .a], [term .b]]

abbrev ValidTree := {tree : ParseTree my_cfg // tree.Valid}
abbrev ValidTreeS := {tree : ValidTree // tree.val.root = nonterm S}
private abbrev Tag (_ : Unit) := ValidTreeS

private def ruleAS : {rule // rule ∈ my_cfg.rules S} :=
  ⟨[term .a, nonterm S], by simp [my_cfg]⟩

private def ruleA : {rule // rule ∈ my_cfg.rules S} :=
  ⟨[term .a], by simp [my_cfg]⟩

private def ruleB : {rule // rule ∈ my_cfg.rules S} :=
  ⟨[term .b], by simp [my_cfg]⟩

private def justA : ValidTreeS :=
  ⟨⟨Node S ruleA [Leaf .a], by
      apply valid_node_of_ForestValid
      simpa [ruleA] using
        (ForestValid_map_leaf (cfg := my_cfg) [Terminal.a])⟩, rfl⟩

private def justB : ValidTreeS :=
  ⟨⟨Node S ruleB [Leaf .b], by
      apply valid_node_of_ForestValid
      simpa [ruleB] using
        (ForestValid_map_leaf (cfg := my_cfg) [Terminal.b])⟩, rfl⟩

private theorem tailForestValid (tail : ValidTreeS) :
    ForestValid (cfg := my_cfg) [nonterm S] [tail.val.val] := by
  rcases tail with ⟨⟨tree, hValid⟩, hRoot⟩
  cases tree with
  | Leaf terminal =>
      simp at hRoot
  | Node n rule children =>
      cases n
      unfold ForestValid
      simp [ForestPairValid, hValid]

private def consA (tail : ValidTreeS) : ValidTreeS :=
  ⟨⟨Node S ruleAS [Leaf .a, tail.val.val], by
      apply valid_node_of_ForestValid
      simpa [ruleAS] using
        ForestValid_append
          (ForestValid_map_leaf (cfg := my_cfg) [Terminal.a])
          (tailForestValid tail)⟩, rfl⟩

private def body
    {μ : Type → Type} [Monad μ] [SemilatticeAlt μ] [Traversable μ]
    (recur : Unit → ParserM (tag := Tag) Terminal μ ValidTreeS) :
    Unit → ParserM (tag := Tag) Terminal μ ValidTreeS
  | () =>
      (terminal' .a *> (consA <$> recur ())) ⊔
        ((terminal' .a $> justA) ⊔ (terminal' .b $> justB))

def parseS
    {μ : Type → Type} [Monad μ] [SemilatticeAlt μ] [Traversable μ] :
    ParserM (tag := Tag) Terminal μ ValidTreeS :=
  memoize (g := body) (t := ())

/--
Every result returned by `parseS` carries a grammar-valid tree rooted at `S`.
This is output certification only; it does not claim completeness or relate the
tree frontier to the consumed input.
-/
theorem parseS_output_certified
    (input : Array Terminal) (start endPos : ℕ) (tree : ValidTreeS)
    (_hMem :
      tree ∈
        (runParser (parseS (μ := List)) input start).1.getD endPos []) :
    tree.val.val.Valid ∧ tree.val.val.root = nonterm S :=
  ⟨tree.val.property, tree.property⟩

def accepts (input : Array Terminal) : Bool :=
  (runParser (parseS (μ := Const)) input).1.contains input.size

#guard accepts #[.a]
#guard accepts #[.b]
#guard accepts #[.a, .b]
#guard accepts #[.a, .a]
#guard !accepts #[]
#guard !accepts #[.c]
#guard !accepts #[.b, .a]

end Example2
