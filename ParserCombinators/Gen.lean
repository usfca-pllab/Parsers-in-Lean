/-

Parser generation from CFGs.

-/

import ParserCombinators.CFG
import ParserCombinators.Memoized
import ParserCombinators.Lemmas

namespace Gen

universe u
variable {α ν : Type u} {μ : Type u → Type u} [Monad μ] [SemilatticeAlt μ] [Traversable μ] [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν]

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
    ParseTree.Node n rule <$> List.traverse id children
  ((cfg.rules n).attach.map parseRule).foldl ParserM.instMaxOfTraversableOfDecidableEq.max ⊥

def gen (cfg : @CFG α ν) : ν → ParserM (tag := tag cfg) α μ (ParseTree cfg) := memoize (g := gen' cfg)

-- TODO(maemre): correctness theorem (by injecting validity proofs above)
-- TODO(maemre): correctness theorem (sound/complete)

-- NOTE: We are proving these for Lists, we can later on generalize it to
-- other "sensible" collections that preserve parts of a list.

abbrev sound (cfg : @CFG α ν)
  (n : ν) (p : ParserM (tag := tag cfg) α List (ParseTree cfg)) (input : Array α)
  := ∀ tree ∈ (runParser p input).1.getD 0 ⊥, tree.Valid ∧ tree.root = Symbol.nonterm n

abbrev complete (cfg : @CFG α ν) (n : ν) (p : ParserM (tag := tag cfg) α List (ParseTree cfg)) (input : Array α)
  (h : cfg.derives [Symbol.nonterm n] (input.toList.map Symbol.term))
  := ∃ tree, tree ∈ (runParser p input).1[0]?.getD ⊥

omit [Fintype ν] in
lemma failure_empty (cfg : @CFG α ν): (runParser (tag := tag cfg) (⊥ : ParserM α μ (ParseTree cfg)) input).1.isEmpty := by
  simp [Bot.bot, runParser, ReaderT.run, MStateT.run, ParserM.lift, ParserM.lower]
  unfold Parser.failure Parser.bind Bind.bind

  have h : @Std.HashMap.emptyWithCapacity.toList ℕ (μ (ParseTree cfg)) = [] := by
    apply List.isEmpty_iff.mp
    simp [Std.HashMap.isEmpty_emptyWithCapacity, Std.HashMap.isEmpty_toList]

  conv =>
    lhs
    enter [1, 1]
    whnf
    simp [h]
    left
    arg 1
    whnf
  simp

omit [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
theorem failure_sound (cfg : @CFG α ν) (n : ν) (input : Array α) : sound cfg n ⊥ input
  := by
  unfold sound
  intro tree
  simp [Std.HashMap.getD_of_isEmpty, failure_empty]
  simp [Bot.bot, SemilatticeAlt.failure]

omit [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
/-- The join operation on lists preserves soundness. -/
theorem sound_of_sup_sound (cfg : @CFG α ν) (n : ν) (p q : ParserM (tag := tag cfg) α List (ParseTree cfg)) (input : Array α)
  (h_p : sound cfg n p input) (h_q : sound cfg n q input) : sound cfg n (p ⊔ q) input
  := by
  unfold sound at *
  intro tree h_mem
  -- Extract subset relationships to use with h_mem
  have h := runParser_sup_eq_sup_runParser p q input
  have h' := Std.HashMap.EquivQuot.getD_eq (s := SemilatticeAlt.setoid) (k := 0) (fallback := ⊥) h
  simp [SemilatticeAlt.setoid, List.memSetoid] at h'
  dsimp [Subset, List.Subset] at *
  replace h_mem := @h'.1 tree h_mem
  dsimp [Max.max] at h_mem
  by_cases h_p_contains_0 : 0 ∈ (runParser p input).1
  · by_cases h_q_contains_0 : 0 ∈ (runParser q input).1
    · rw [<- Std.HashMap.getElem_eq_getD] at h_p <;> simp_all
      rw [<- Std.HashMap.getElem_eq_getD] at h_q <;> try simp_all
      -- The explicit application is for providing the Semilatticeoid instance.
      have h' := Std.HashMap.unionSup_getD_both (s := SemilatticeAlt.setoid) (semi := List.instSemilatticeAlt.instSemilatticeoidInstSetoid) h_p_contains_0 h_q_contains_0
      simp [SemilatticeAlt.setoid, List.memSetoid, Subset, List.Subset] at h'
      replace h_mem := @h'.1 tree h_mem
      simp [Max.max, SemilatticeAlt.orElse] at h_mem
      cases h_mem <;> rename_i h_mem
      · exact h_p tree h_mem
      · exact h_q tree h_mem
    · have h' := Std.HashMap.unionSup_getD_of_right_not_contains (s := SemilatticeAlt.setoid) (semi := List.instSemilatticeAlt.instSemilatticeoidInstSetoid) (fallback := ⊥) (runParser p input).1 (runParser q input).1 h_q_contains_0
      simp [SemilatticeAlt.setoid, List.memSetoid, Subset, List.Subset] at h'
      replace h_mem := @h'.1 tree h_mem
      exact h_p tree h_mem
  · have h' := Std.HashMap.unionSup_getD_of_not_contains (s := SemilatticeAlt.setoid) (semi := List.instSemilatticeAlt.instSemilatticeoidInstSetoid) (fallback := ⊥) (runParser p input).1 (runParser q input).1 h_p_contains_0
    simp [SemilatticeAlt.setoid, List.memSetoid, Subset, List.Subset] at h'
    replace h_mem := @h'.1 tree h_mem
    by_cases h_q_contains_0 : 0 ∈ (runParser q input).1
    · exact h_q tree h_mem
    · simp_all

set_option pp.proofs true
theorem gen_sound (cfg : @CFG α ν) n input : sound cfg n (gen (μ := List) cfg n) input := by
  unfold gen
  revert input
  let p (parser : (n : ν) → ParserM α List (tag cfg n)) := ∀ input, sound cfg n (parser n) input
  refine memoize_induction (gen' (μ := List) cfg) p ?_ ?_ <;> unfold p <;> simp
  · -- base case: failure
    intro input
    apply failure_sound cfg n input
  · -- inductive case
    intro recur h_recur input
    unfold gen'
    simp
    apply List.foldlRecOn (motive := (sound cfg n · input)) _ _ ?_ ?_
    · -- base case of fold
      apply failure_sound
    · -- inductive case
      simp_all
      intro b b_sound a rule h_rule h_a
      let buildNode := Node n ⟨rule, (Iff.of_eq (Eq.refl (rule ∈ cfg.rules n))).mpr h_rule⟩
      let children : ParserM α List (List (ParseTree cfg)) := List.traverse id
                (List.map
                  (fun sym ↦
                    match sym with
                    | Symbol.term a => Leaf <$> terminal' a
                    | Symbol.nonterm n => recur n)
                  rule)
      apply sound_of_sup_sound
      · assumption
      · subst h_a
        -- Experimenting with bind
        unfold sound
        intro tree h_tree
        conv at h_tree =>
          enter [1,1,1,1]
          conv => arg 1 ; change buildNode
          conv => arg 2 ; change children
        rw [Std.HashMap.Equiv.getD_eq (runParser_map _ _ _)] at h_tree
        rw [Std.HashMap.getD_eq_getD_getElem?] at h_tree
        let result := (Std.HashMap.map (fun x ↦ Functor.map buildNode) (runParser children input).1)
        by_cases h : 0 ∈ result <;> subst result <;> simp [h] at h_tree
        · subst buildNode
          replace ⟨a, h_a, h_tree⟩ := h_tree
          subst h_tree
          simp [ParseTree.Valid]

        · simp [Bot.bot, SemilatticeAlt.failure] at h_tree

end Gen
