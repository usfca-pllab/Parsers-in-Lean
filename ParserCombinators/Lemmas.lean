-- Some potential lemmas we can use to prove correctness theorems for the parser generator.

import ParserCombinators.Memoized

universe u v
variable {τ} { α β : Type u } {tag : τ → Type u} { μ : Type u → Type u } [Fintype τ] [BEq τ] [LawfulBEq τ] [Hashable τ] [DecidableEq τ] [Monad μ] [Traversable μ] [semilat_μ : SemilatticeAlt μ] [h_eq : ∀ t : τ, DecidableEq (tag t)]

axiom memoize_induction
  (g : ((t : τ) → ParserM (tag := tag) β μ (tag t)) → (t : τ) → ParserM (tag := tag) β μ (tag t))
  (p : ((t : τ) → ParserM (tag := tag) β μ (tag t)) → Prop)
  (input : Array β)
  (h_failure : p (fun _ => ⊥))
  (h_induction : ∀ parser, p (parser) → p (g parser))
    : p (memoize Counter.empty g)


variable (parser₁ parser₂ : ParserM (tag := tag) β μ α) (input : Array β) [DecidableEq α]

axiom runParser_sup_eq_sup_runParser
  : (runParser (parser₁ ⊔ parser₂) input).1.EquivQuot ((runParser parser₁ input) ⊔ (runParser parser₂ input)).1

axiom mem_runParser_bind_iff_eq_bind_mem_runParser
  [DecidableEq α']
  (parser₂ : α → ParserM (tag := tag) β μ α')
  {start end_pos : ℕ}
  {r : μ α'}
    : ((runParser (parser₁ >>= parser₂) input start).1[end_pos]? = some r) ↔
  ∃ split : ℕ, ∃ s : μ α, (runParser parser₁ input start).1[split]? = some s ∧
    (s >>= (fun x => sequence (runParser (parser₂ x) input split).1[end_pos]?)) = r
