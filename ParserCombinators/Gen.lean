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

-- Generated parsers return plain parse trees.  Correctness information is
-- attached externally by the soundness theorem below and the planned
-- completeness theorem, rather than by injecting validity proofs into parser
-- result types.

-- NOTE: We are proving these for Lists, we can later on generalize it to
-- other "sensible" collections that preserve parts of a list.

abbrev sound (cfg : @CFG α ν)
  (n : ν) (p : ParserM (tag := tag cfg) α List (ParseTree cfg)) (input : Array α)
  :=
  ∀ start end_ : ℕ,
  ∀ _h_bound : start ≤ end_ ∧ end_ ≤ input.size,
  ∀ tree ∈ (runParser p input start).1.getD end_ ⊥, tree.Valid ∧ tree.root = Symbol.nonterm n

abbrev complete (cfg : @CFG α ν) (n : ν) (p : ParserM (tag := tag cfg) α List (ParseTree cfg)) (input : Array α)
  :=
  cfg.derives [Symbol.nonterm n] (input.toList.map Symbol.term) →
    ∃ tree,
      tree ∈ (runParser p input 0).1.getD input.size [] ∧
      tree.Valid ∧
      tree.root = Symbol.nonterm n ∧
      tree.leaves = input.toList

abbrev result_bounded (cfg : @CFG α ν)
  (p : ParserM (tag := tag cfg) α List (ParseTree cfg)) (input : Array α)
  :=
  ∀ start end_ : ℕ,
  start ≤ input.size →
  ∀ tree, tree ∈ (runParser p input start).1.getD end_ [] →
    start ≤ end_ ∧ end_ ≤ input.size

abbrev generatedListSymbolParser
  (cfg : @CFG α ν)
  (counter : Counter ν)
  (g : ((t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg)) →
      (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg)) :
    Symbol α ν → ParserM (tag := tag cfg) α List (ParseTree cfg)
  | Symbol.term a => Leaf (cfg := cfg) <$> terminal' (tag := tag cfg) a
  | Symbol.nonterm n => memoize counter g n

abbrev cachedResultMap (cfg : @CFG α ν)
  (memo : MemoData (tag cfg) List)
  (n : ν) (key : MemoKey ν) (start : ℕ) :
    ResultMap List (ParseTree cfg) :=
  (memo.getD n
    (Std.HashMap.emptyWithCapacity :
      Std.HashMap (MemoEntryKey ν) (ResultMap List (ParseTree cfg)))).getD
    (key, start) Std.HashMap.emptyWithCapacity

abbrev memoWithCachedResult (cfg : @CFG α ν)
  (memo : MemoData (tag cfg) List)
  (n : ν) (key : MemoKey ν) (start : ℕ)
  (resultMap : ResultMap List (ParseTree cfg)) :
    MemoData (tag cfg) List :=
  memo.insert n
    ((memo.getD n
      (Std.HashMap.emptyWithCapacity :
        Std.HashMap (MemoEntryKey ν) (ResultMap List (ParseTree cfg)))).insert
      (key, start) resultMap)

abbrev resultMap_sound (cfg : @CFG α ν) (n : ν)
  (resultMap : ResultMap List (ParseTree cfg)) :=
  ∀ end_ : ℕ,
  ∀ tree ∈ resultMap.getD end_ [],
    tree.Valid ∧ tree.root = Symbol.nonterm n

abbrev resultMap_bounded (cfg : @CFG α ν) (input : Array α) (start : ℕ)
  (resultMap : ResultMap List (ParseTree cfg)) :=
  ∀ end_ : ℕ,
  start ≤ input.size →
  ∀ tree, tree ∈ resultMap.getD end_ [] →
    start ≤ end_ ∧ end_ ≤ input.size

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
theorem resultMap_sound_empty (cfg : @CFG α ν) (n : ν) :
    resultMap_sound cfg n (Std.HashMap.emptyWithCapacity : ResultMap List (ParseTree cfg)) := by
  intro end_ tree h_mem
  simp at h_mem

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
theorem resultMap_bounded_empty (cfg : @CFG α ν) (input : Array α) (start : ℕ) :
    resultMap_bounded cfg input start
      (Std.HashMap.emptyWithCapacity : ResultMap List (ParseTree cfg)) := by
  intro end_ h_start tree h_mem
  simp at h_mem

set_option linter.unusedSectionVars false in
theorem resultMap_sound_sup
  {cfg : @CFG α ν} {n : ν}
  {left right : ResultMap List (ParseTree cfg)}
  (h_left : resultMap_sound cfg n left)
  (h_right : resultMap_sound cfg n right) :
    resultMap_sound cfg n (left.unionSup right) := by
  intro end_ tree h_mem
  change tree ∈ (left.unionSup right).getD end_ [] at h_mem
  by_cases h_left_end : end_ ∈ left
  · by_cases h_right_end : end_ ∈ right
    · have h_union := Std.HashMap.unionSup_getD_both
        (s := SemilatticeAlt.setoid)
        (semi := List.instSemilatticeAlt.instSemilatticeoidInstSetoid)
        h_left_end h_right_end
      simp [SemilatticeAlt.setoid, List.memSetoid, Subset, List.Subset] at h_union
      replace h_mem := @h_union.1 tree (by simpa using h_mem)
      simp [Max.max, SemilatticeAlt.orElse] at h_mem
      cases h_mem with
      | inl h_tree =>
          exact h_left end_ tree (by simpa [Std.HashMap.getElem_eq_getD (fallback := [])] using h_tree)
      | inr h_tree =>
          exact h_right end_ tree (by simpa [Std.HashMap.getElem_eq_getD (fallback := [])] using h_tree)
    · have h_union := Std.HashMap.unionSup_getD_of_right_not_contains
        (s := SemilatticeAlt.setoid)
        (semi := List.instSemilatticeAlt.instSemilatticeoidInstSetoid)
        (fallback := []) left right h_right_end
      simp [SemilatticeAlt.setoid, List.memSetoid, Subset, List.Subset] at h_union
      replace h_mem := @h_union.1 tree h_mem
      exact h_left end_ tree h_mem
  · have h_union := Std.HashMap.unionSup_getD_of_not_contains
      (s := SemilatticeAlt.setoid)
      (semi := List.instSemilatticeAlt.instSemilatticeoidInstSetoid)
      (fallback := []) left right h_left_end
    simp [SemilatticeAlt.setoid, List.memSetoid, Subset, List.Subset] at h_union
    replace h_mem := @h_union.1 tree h_mem
    exact h_right end_ tree h_mem

set_option linter.unusedSectionVars false in
theorem resultMap_bounded_sup
  {cfg : @CFG α ν} {input : Array α} {start : ℕ}
  {left right : ResultMap List (ParseTree cfg)}
  (h_left : resultMap_bounded cfg input start left)
  (h_right : resultMap_bounded cfg input start right) :
    resultMap_bounded cfg input start (left.unionSup right) := by
  intro end_ h_start tree h_mem
  change tree ∈ (left.unionSup right).getD end_ [] at h_mem
  by_cases h_left_end : end_ ∈ left
  · by_cases h_right_end : end_ ∈ right
    · have h_union := Std.HashMap.unionSup_getD_both
        (s := SemilatticeAlt.setoid)
        (semi := List.instSemilatticeAlt.instSemilatticeoidInstSetoid)
        h_left_end h_right_end
      simp [SemilatticeAlt.setoid, List.memSetoid, Subset, List.Subset] at h_union
      replace h_mem := @h_union.1 tree (by simpa using h_mem)
      simp [Max.max, SemilatticeAlt.orElse] at h_mem
      cases h_mem with
      | inl h_tree =>
          exact h_left end_ h_start tree
            (by simpa [Std.HashMap.getElem_eq_getD (fallback := [])] using h_tree)
      | inr h_tree =>
          exact h_right end_ h_start tree
            (by simpa [Std.HashMap.getElem_eq_getD (fallback := [])] using h_tree)
    · have h_union := Std.HashMap.unionSup_getD_of_right_not_contains
        (s := SemilatticeAlt.setoid)
        (semi := List.instSemilatticeAlt.instSemilatticeoidInstSetoid)
        (fallback := []) left right h_right_end
      simp [SemilatticeAlt.setoid, List.memSetoid, Subset, List.Subset] at h_union
      replace h_mem := @h_union.1 tree h_mem
      exact h_left end_ h_start tree h_mem
  · have h_union := Std.HashMap.unionSup_getD_of_not_contains
      (s := SemilatticeAlt.setoid)
      (semi := List.instSemilatticeAlt.instSemilatticeoidInstSetoid)
      (fallback := []) left right h_left_end
    simp [SemilatticeAlt.setoid, List.memSetoid, Subset, List.Subset] at h_union
    replace h_mem := @h_union.1 tree h_mem
    exact h_right end_ h_start tree h_mem

set_option linter.unusedSectionVars false in
theorem resultMap_mem_unionSup_left
  {cfg : @CFG α ν}
  {left right : ResultMap List (ParseTree cfg)}
  {end_ : ℕ} {tree : ParseTree cfg}
  (h_mem : tree ∈ left.getD end_ []) :
    tree ∈ (left.unionSup right).getD end_ [] := by
  by_cases h_left_end : end_ ∈ left
  · by_cases h_right_end : end_ ∈ right
    · have h_union := Std.HashMap.unionSup_getD_both
        (s := SemilatticeAlt.setoid)
        (semi := List.instSemilatticeAlt.instSemilatticeoidInstSetoid)
        h_left_end h_right_end
      simp [SemilatticeAlt.setoid, List.memSetoid, Subset, List.Subset] at h_union
      apply h_union.2
      simp [Max.max, SemilatticeAlt.orElse]
      left
      simpa [Std.HashMap.getElem_eq_getD (fallback := [])] using h_mem
    · have h_union := Std.HashMap.unionSup_getD_of_right_not_contains
        (s := SemilatticeAlt.setoid)
        (semi := List.instSemilatticeAlt.instSemilatticeoidInstSetoid)
        (fallback := []) left right h_right_end
      simp [SemilatticeAlt.setoid, List.memSetoid, Subset, List.Subset] at h_union
      exact h_union.2 h_mem
  · simp [Std.HashMap.getD_eq_fallback h_left_end] at h_mem

set_option linter.unusedSectionVars false in
theorem resultMap_mem_unionSup_right
  {cfg : @CFG α ν}
  {left right : ResultMap List (ParseTree cfg)}
  {end_ : ℕ} {tree : ParseTree cfg}
  (h_mem : tree ∈ right.getD end_ []) :
    tree ∈ (left.unionSup right).getD end_ [] := by
  by_cases h_left_end : end_ ∈ left
  · by_cases h_right_end : end_ ∈ right
    · have h_union := Std.HashMap.unionSup_getD_both
        (s := SemilatticeAlt.setoid)
        (semi := List.instSemilatticeAlt.instSemilatticeoidInstSetoid)
        h_left_end h_right_end
      simp [SemilatticeAlt.setoid, List.memSetoid, Subset, List.Subset] at h_union
      apply h_union.2
      simp [Max.max, SemilatticeAlt.orElse]
      right
      simpa [Std.HashMap.getElem_eq_getD (fallback := [])] using h_mem
    · simp [Std.HashMap.getD_eq_fallback h_right_end] at h_mem
  · have h_union := Std.HashMap.unionSup_getD_of_not_contains
      (s := SemilatticeAlt.setoid)
      (semi := List.instSemilatticeAlt.instSemilatticeoidInstSetoid)
      (fallback := []) left right h_left_end
    simp [SemilatticeAlt.setoid, List.memSetoid, Subset, List.Subset] at h_union
    exact h_union.2 h_mem

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
theorem resultMap_sound_of_quot_eq
  {cfg : @CFG α ν} {n : ν}
  {left right : ResultMap List (ParseTree cfg)}
  (h_eq :
    Quotient.mk (Std.HashMap.isSetoid (s := List.memSetoid (ParseTree cfg))) left =
      Quotient.mk (Std.HashMap.isSetoid (s := List.memSetoid (ParseTree cfg))) right)
  (h_right : resultMap_sound cfg n right) :
    resultMap_sound cfg n left := by
  intro end_ tree h_mem
  have h_equiv :
      Std.HashMap.EquivQuot
        (s := List.memSetoid (ParseTree cfg)) left right :=
    Quotient.exact h_eq
  have h_getD := Std.HashMap.EquivQuot.getD_eq
    (s := List.memSetoid (ParseTree cfg)) (k := end_) (fallback := []) h_equiv
  simp [List.memSetoid, Subset, List.Subset] at h_getD
  exact h_right end_ tree (@h_getD.1 tree h_mem)

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
theorem resultMap_bounded_of_quot_eq
  {cfg : @CFG α ν} {input : Array α} {start : ℕ}
  {left right : ResultMap List (ParseTree cfg)}
  (h_eq :
    Quotient.mk (Std.HashMap.isSetoid (s := List.memSetoid (ParseTree cfg))) left =
      Quotient.mk (Std.HashMap.isSetoid (s := List.memSetoid (ParseTree cfg))) right)
  (h_right : resultMap_bounded cfg input start right) :
    resultMap_bounded cfg input start left := by
  intro end_ h_start tree h_mem
  have h_equiv :
      Std.HashMap.EquivQuot
        (s := List.memSetoid (ParseTree cfg)) left right :=
    Quotient.exact h_eq
  have h_getD := Std.HashMap.EquivQuot.getD_eq
    (s := List.memSetoid (ParseTree cfg)) (k := end_) (fallback := []) h_equiv
  simp [List.memSetoid, Subset, List.Subset] at h_getD
  exact h_right end_ h_start tree (@h_getD.1 tree h_mem)

abbrev positionMap_sound (cfg : @CFG α ν) (n : ν)
  (positionMap :
    Std.HashMap (MemoEntryKey ν) (ResultMap List (ParseTree cfg))) :=
  ∀ key start,
    resultMap_sound cfg n
      (positionMap.getD (key, start) Std.HashMap.emptyWithCapacity)

abbrev positionMap_bounded (cfg : @CFG α ν) (input : Array α)
  (positionMap :
    Std.HashMap (MemoEntryKey ν) (ResultMap List (ParseTree cfg))) :=
  ∀ key start,
    resultMap_bounded cfg input start
      (positionMap.getD (key, start) Std.HashMap.emptyWithCapacity)

set_option linter.unusedSectionVars false in
theorem positionMap_sound_empty (cfg : @CFG α ν) (n : ν) :
    positionMap_sound cfg n
      (Std.HashMap.emptyWithCapacity :
        Std.HashMap (MemoEntryKey ν) (ResultMap List (ParseTree cfg))) := by
  intro key start
  simpa using resultMap_sound_empty cfg n

set_option linter.unusedSectionVars false in
theorem positionMap_bounded_empty (cfg : @CFG α ν) (input : Array α) :
    positionMap_bounded cfg input
      (Std.HashMap.emptyWithCapacity :
        Std.HashMap (MemoEntryKey ν) (ResultMap List (ParseTree cfg))) := by
  intro key start
  simpa using resultMap_bounded_empty cfg input start

abbrev positionMapUnion
  (cfg : @CFG α ν)
  (left right :
    Std.HashMap (MemoEntryKey ν) (ResultMap List (ParseTree cfg))) :
    Std.HashMap (MemoEntryKey ν) (ResultMap List (ParseTree cfg)) :=
  Std.HashMap.unionSup
    (instMax := Std.HashMap.instMax
      (s := List.memSetoid (ParseTree cfg))
      (semi := List.instSemilatticeAlt.instSemilatticeoidInstSetoid))
    left right

set_option linter.unusedSectionVars false in
theorem positionMap_sound_sup
  {cfg : @CFG α ν} {n : ν}
  {left right :
    Std.HashMap (MemoEntryKey ν) (ResultMap List (ParseTree cfg))}
  (h_left : positionMap_sound cfg n left)
  (h_right : positionMap_sound cfg n right) :
    positionMap_sound cfg n (positionMapUnion cfg left right) := by
  intro key start
  by_cases h_left_key : (key, start) ∈ left
  · by_cases h_right_key : (key, start) ∈ right
    · have h_union := Std.HashMap.unionSup_getD_both
        (s := Std.HashMap.isSetoid
          (s := List.memSetoid (ParseTree cfg)))
        (semi := Std.HashMap.instSemilatticeoidIsSetoid
          (s := List.memSetoid (ParseTree cfg))
          (semi := List.instSemilatticeAlt.instSemilatticeoidInstSetoid))
        (m₁ := left) (m₂ := right) h_left_key h_right_key
      have h_target :
          resultMap_sound cfg n
            ((left.get (key, start) h_left_key).unionSup
              (right.get (key, start) h_right_key)) := by
        exact resultMap_sound_sup
          (cfg := cfg) (n := n)
          (left := left.get (key, start) h_left_key)
          (right := right.get (key, start) h_right_key)
          (by
            simpa [Std.HashMap.getElem_eq_getD
              (fallback := (Std.HashMap.emptyWithCapacity : ResultMap List (ParseTree cfg)))]
              using h_left key start)
          (by
            simpa [Std.HashMap.getElem_eq_getD
              (fallback := (Std.HashMap.emptyWithCapacity : ResultMap List (ParseTree cfg)))]
              using h_right key start)
      exact resultMap_sound_of_quot_eq
        (cfg := cfg) (n := n)
        (left := (positionMapUnion cfg left right).getD (key, start)
          (Std.HashMap.emptyWithCapacity : ResultMap List (ParseTree cfg)))
        (right := (left.get (key, start) h_left_key).unionSup
          (right.get (key, start) h_right_key))
        (by simpa [positionMapUnion, Max.max] using h_union)
        h_target
    · have h_union := Std.HashMap.unionSup_getD_of_right_not_contains
        (s := Std.HashMap.isSetoid
          (s := List.memSetoid (ParseTree cfg)))
        (semi := Std.HashMap.instSemilatticeoidIsSetoid
          (s := List.memSetoid (ParseTree cfg))
          (semi := List.instSemilatticeAlt.instSemilatticeoidInstSetoid))
        (fallback := (Std.HashMap.emptyWithCapacity : ResultMap List (ParseTree cfg)))
        left right h_right_key
      exact resultMap_sound_of_quot_eq
        (cfg := cfg) (n := n)
        (left := (positionMapUnion cfg left right).getD (key, start)
          (Std.HashMap.emptyWithCapacity : ResultMap List (ParseTree cfg)))
        (right := left.getD (key, start)
          (Std.HashMap.emptyWithCapacity : ResultMap List (ParseTree cfg)))
        (by simpa [positionMapUnion] using h_union)
        (h_left key start)
  · have h_union := Std.HashMap.unionSup_getD_of_not_contains
      (s := Std.HashMap.isSetoid
        (s := List.memSetoid (ParseTree cfg)))
      (semi := Std.HashMap.instSemilatticeoidIsSetoid
        (s := List.memSetoid (ParseTree cfg))
        (semi := List.instSemilatticeAlt.instSemilatticeoidInstSetoid))
      (fallback := (Std.HashMap.emptyWithCapacity : ResultMap List (ParseTree cfg)))
      left right h_left_key
    exact resultMap_sound_of_quot_eq
      (cfg := cfg) (n := n)
      (left := (positionMapUnion cfg left right).getD (key, start)
        (Std.HashMap.emptyWithCapacity : ResultMap List (ParseTree cfg)))
      (right := right.getD (key, start)
        (Std.HashMap.emptyWithCapacity : ResultMap List (ParseTree cfg)))
      (by simpa [positionMapUnion] using h_union)
      (h_right key start)

set_option linter.unusedSectionVars false in
theorem positionMap_bounded_sup
  {cfg : @CFG α ν} {input : Array α}
  {left right :
    Std.HashMap (MemoEntryKey ν) (ResultMap List (ParseTree cfg))}
  (h_left : positionMap_bounded cfg input left)
  (h_right : positionMap_bounded cfg input right) :
    positionMap_bounded cfg input (positionMapUnion cfg left right) := by
  intro key start
  by_cases h_left_key : (key, start) ∈ left
  · by_cases h_right_key : (key, start) ∈ right
    · have h_union := Std.HashMap.unionSup_getD_both
        (s := Std.HashMap.isSetoid
          (s := List.memSetoid (ParseTree cfg)))
        (semi := Std.HashMap.instSemilatticeoidIsSetoid
          (s := List.memSetoid (ParseTree cfg))
          (semi := List.instSemilatticeAlt.instSemilatticeoidInstSetoid))
        (m₁ := left) (m₂ := right) h_left_key h_right_key
      have h_target :
          resultMap_bounded cfg input start
            ((left.get (key, start) h_left_key).unionSup
              (right.get (key, start) h_right_key)) := by
        exact resultMap_bounded_sup
          (cfg := cfg) (input := input) (start := start)
          (left := left.get (key, start) h_left_key)
          (right := right.get (key, start) h_right_key)
          (by
            simpa [Std.HashMap.getElem_eq_getD
              (fallback := (Std.HashMap.emptyWithCapacity : ResultMap List (ParseTree cfg)))]
              using h_left key start)
          (by
            simpa [Std.HashMap.getElem_eq_getD
              (fallback := (Std.HashMap.emptyWithCapacity : ResultMap List (ParseTree cfg)))]
              using h_right key start)
      exact resultMap_bounded_of_quot_eq
        (cfg := cfg) (input := input) (start := start)
        (left := (positionMapUnion cfg left right).getD (key, start)
          (Std.HashMap.emptyWithCapacity : ResultMap List (ParseTree cfg)))
        (right := (left.get (key, start) h_left_key).unionSup
          (right.get (key, start) h_right_key))
        (by simpa [positionMapUnion, Max.max] using h_union)
        h_target
    · have h_union := Std.HashMap.unionSup_getD_of_right_not_contains
        (s := Std.HashMap.isSetoid
          (s := List.memSetoid (ParseTree cfg)))
        (semi := Std.HashMap.instSemilatticeoidIsSetoid
          (s := List.memSetoid (ParseTree cfg))
          (semi := List.instSemilatticeAlt.instSemilatticeoidInstSetoid))
        (fallback := (Std.HashMap.emptyWithCapacity : ResultMap List (ParseTree cfg)))
        left right h_right_key
      exact resultMap_bounded_of_quot_eq
        (cfg := cfg) (input := input) (start := start)
        (left := (positionMapUnion cfg left right).getD (key, start)
          (Std.HashMap.emptyWithCapacity : ResultMap List (ParseTree cfg)))
        (right := left.getD (key, start)
          (Std.HashMap.emptyWithCapacity : ResultMap List (ParseTree cfg)))
        (by simpa [positionMapUnion] using h_union)
        (h_left key start)
  · have h_union := Std.HashMap.unionSup_getD_of_not_contains
      (s := Std.HashMap.isSetoid
        (s := List.memSetoid (ParseTree cfg)))
      (semi := Std.HashMap.instSemilatticeoidIsSetoid
        (s := List.memSetoid (ParseTree cfg))
        (semi := List.instSemilatticeAlt.instSemilatticeoidInstSetoid))
      (fallback := (Std.HashMap.emptyWithCapacity : ResultMap List (ParseTree cfg)))
      left right h_left_key
    exact resultMap_bounded_of_quot_eq
      (cfg := cfg) (input := input) (start := start)
      (left := (positionMapUnion cfg left right).getD (key, start)
        (Std.HashMap.emptyWithCapacity : ResultMap List (ParseTree cfg)))
      (right := right.getD (key, start)
        (Std.HashMap.emptyWithCapacity : ResultMap List (ParseTree cfg)))
      (by simpa [positionMapUnion] using h_union)
      (h_right key start)

omit [BEq α] [DecidableEq α] [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
theorem cachedResultMap_memoWithCachedResult_self
  (cfg : @CFG α ν) (memo : MemoData (tag cfg) List)
  (n : ν) (key : MemoKey ν) (start : ℕ)
  (resultMap : ResultMap List (ParseTree cfg)) :
    cachedResultMap cfg
      (memoWithCachedResult cfg memo n key start resultMap)
      n key start = resultMap := by
  simp [cachedResultMap, memoWithCachedResult]

omit [BEq α] [DecidableEq α] [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
theorem cachedResultMap_memoWithCachedResult_ne
  (cfg : @CFG α ν) (memo : MemoData (tag cfg) List)
  (n n' : ν) (key key' : MemoKey ν) (start start' : ℕ)
  (resultMap : ResultMap List (ParseTree cfg))
  (h_ne : n' ≠ n ∨ (key', start') ≠ (key, start)) :
    cachedResultMap cfg
      (memoWithCachedResult cfg memo n key start resultMap)
      n' key' start' =
    cachedResultMap cfg memo n' key' start' := by
  by_cases h_tag : n' = n
  · subst h_tag
    have h_entry_ne : (key', start') ≠ (key, start) := by
      cases h_ne with
      | inl h_tag_ne =>
          exact False.elim (h_tag_ne rfl)
      | inr h_entry_ne =>
          exact h_entry_ne
    have h_entry_ne' : (key, start) ≠ (key', start') := by
      intro h_eq
      exact h_entry_ne h_eq.symm
    simp [cachedResultMap, memoWithCachedResult]
    repeat rw [Std.HashMap.getD_eq_getD_getElem?]
    rw [Std.HashMap.getElem?_insert]
    simp [h_entry_ne']
  ·
      have h_tag_ne : n ≠ n' := by
        intro h_eq
        exact h_tag h_eq.symm
      unfold cachedResultMap memoWithCachedResult
      repeat rw [Std.DHashMap.getD_eq_getD_get?]
      rw [Std.DHashMap.get?_insert]
      simp [h_tag_ne]

omit [BEq α] [DecidableEq α] [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
theorem memoWithCachedResult_getElem?_self
  (cfg : @CFG α ν) (memo : MemoData (tag cfg) List)
  (n : ν) (key : MemoKey ν) (start : ℕ)
  (resultMap : ResultMap List (ParseTree cfg)) :
    ((memoWithCachedResult cfg memo n key start resultMap).getD n ⊥)[(key, start)]? =
      some resultMap := by
  simp [memoWithCachedResult, Bot.bot]

omit [BEq α] [DecidableEq α] [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
theorem memoWithCachedResult_getElem?_ne
  (cfg : @CFG α ν) (memo : MemoData (tag cfg) List)
  (n n' : ν) (key key' : MemoKey ν) (start start' : ℕ)
  (resultMap : ResultMap List (ParseTree cfg))
  (h_ne : n' ≠ n ∨ (key', start') ≠ (key, start)) :
    ((memoWithCachedResult cfg memo n key start resultMap).getD n' ⊥)[(key', start')]? =
      (memo.getD n' ⊥)[(key', start')]? := by
  by_cases h_tag : n' = n
  · subst h_tag
    have h_entry_ne : (key', start') ≠ (key, start) := by
      cases h_ne with
      | inl h_tag_ne =>
          exact False.elim (h_tag_ne rfl)
      | inr h_entry_ne =>
          exact h_entry_ne
    have h_entry_ne' : (key, start) ≠ (key', start') := by
      intro h_eq
      exact h_entry_ne h_eq.symm
    simp [memoWithCachedResult, Bot.bot]
    rw [Std.HashMap.getElem?_insert]
    simp [h_entry_ne']
  ·
      have h_tag_ne : n ≠ n' := by
        intro h_eq
        exact h_tag h_eq.symm
      unfold memoWithCachedResult
      repeat rw [Std.DHashMap.getD_eq_getD_get?]
      rw [Std.DHashMap.get?_insert]
      simp [h_tag_ne]

set_option linter.unusedVariables false in
abbrev memo_sound (cfg : @CFG α ν) (input : Array α)
  (memo : MemoData (tag cfg) List) :=
  ∀ (n : ν) (key : MemoKey ν) (start end_ : ℕ),
  ∀ tree ∈ (cachedResultMap cfg memo n key start).getD end_ [],
    tree.Valid ∧ tree.root = Symbol.nonterm n

abbrev memo_bounded (cfg : @CFG α ν) (input : Array α)
  (memo : MemoData (tag cfg) List) :=
  ∀ (n : ν) (key : MemoKey ν) (start end_ : ℕ),
  start ≤ input.size →
  ∀ tree, tree ∈ (cachedResultMap cfg memo n key start).getD end_ [] →
    start ≤ end_ ∧ end_ ≤ input.size

abbrev memo_wellFormed (cfg : @CFG α ν) (input : Array α)
  (memo : MemoData (tag cfg) List) :=
  memo_sound cfg input memo ∧ memo_bounded cfg input memo

omit [BEq α] [DecidableEq α] [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
theorem resultMap_sound_of_memo_sound
  {cfg : @CFG α ν} {input : Array α}
  {memo : MemoData (tag cfg) List}
  (h_memo : memo_sound cfg input memo)
  (n : ν) (key : MemoKey ν) (start : ℕ) :
    resultMap_sound cfg n (cachedResultMap cfg memo n key start) := by
  intro end_ tree h_mem
  exact h_memo n key start end_ tree h_mem

omit [BEq α] [DecidableEq α] [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
theorem resultMap_bounded_of_memo_bounded
  {cfg : @CFG α ν} {input : Array α}
  {memo : MemoData (tag cfg) List}
  (h_memo : memo_bounded cfg input memo)
  (n : ν) (key : MemoKey ν) (start : ℕ) :
    resultMap_bounded cfg input start (cachedResultMap cfg memo n key start) := by
  intro end_ h_start tree h_mem
  exact h_memo n key start end_ h_start tree h_mem

omit [BEq α] [DecidableEq α] [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
theorem positionMap_sound_of_memo_sound
  {cfg : @CFG α ν} {input : Array α}
  {memo : MemoData (tag cfg) List}
  (h_memo : memo_sound cfg input memo)
  (n : ν) :
    positionMap_sound cfg n
      (memo.getD n
        (Std.HashMap.emptyWithCapacity :
          Std.HashMap (MemoEntryKey ν) (ResultMap List (ParseTree cfg)))) := by
  intro key start
  exact resultMap_sound_of_memo_sound h_memo n key start

omit [BEq α] [DecidableEq α] [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
theorem positionMap_bounded_of_memo_bounded
  {cfg : @CFG α ν} {input : Array α}
  {memo : MemoData (tag cfg) List}
  (h_memo : memo_bounded cfg input memo)
  (n : ν) :
    positionMap_bounded cfg input
      (memo.getD n
        (Std.HashMap.emptyWithCapacity :
          Std.HashMap (MemoEntryKey ν) (ResultMap List (ParseTree cfg)))) := by
  intro key start
  exact resultMap_bounded_of_memo_bounded h_memo n key start

set_option linter.unusedSectionVars false in
theorem positionMap_sound_of_memo_sound_sup
  {cfg : @CFG α ν} {input : Array α}
  {left right : MemoData (tag cfg) List}
  (h_left : memo_sound cfg input left)
  (h_right : memo_sound cfg input right)
  (n : ν) :
    positionMap_sound cfg n
      ((left ⊔ right).getD n
        (Std.HashMap.emptyWithCapacity :
          Std.HashMap (MemoEntryKey ν) (ResultMap List (ParseTree cfg)))) := by
  let emptyPositionMap :
      Std.HashMap (MemoEntryKey ν) (ResultMap List (ParseTree cfg)) :=
    Std.HashMap.emptyWithCapacity
  change positionMap_sound cfg n
    ((Std.DHashMap.unionWith
      (fun _ => positionMapUnion cfg)
      (fun _ => emptyPositionMap)
      left right).getD n emptyPositionMap)
  by_cases h_left_n : n ∈ left
  · by_cases h_right_n : n ∈ right
    · rw [Std.DHashMap.getD_eq_getD_get?]
      rw [Std.DHashMap.unionWith_getElem_both
        (m₁ := left) (m₂ := right)
        (f := fun _ => positionMapUnion cfg)
        (z := fun _ => emptyPositionMap)
        h_left_n h_right_n]
      exact positionMap_sound_sup
        (cfg := cfg) (n := n)
        (by
          simpa [Std.DHashMap.get_eq_getD
            (m := left) (a := n) (fallback := emptyPositionMap)
            (h := h_left_n)]
            using positionMap_sound_of_memo_sound h_left n)
        (by
          simpa [Std.DHashMap.get_eq_getD
            (m := right) (a := n) (fallback := emptyPositionMap)
            (h := h_right_n)]
            using positionMap_sound_of_memo_sound h_right n)
    · rw [Std.DHashMap.getD_eq_getD_get?]
      rw [Std.DHashMap.unionWith_getElem_not_contains_right
        (m₁ := left) (m₂ := right)
        (f := fun _ => positionMapUnion cfg)
        (z := fun _ => emptyPositionMap)
        h_right_n]
      rw [Std.DHashMap.get?_eq_some_get h_left_n]
      exact positionMap_sound_sup
        (cfg := cfg) (n := n)
        (by
          simpa [Std.DHashMap.get_eq_getD
            (m := left) (a := n) (fallback := emptyPositionMap)
            (h := h_left_n)]
            using positionMap_sound_of_memo_sound h_left n)
        (positionMap_sound_empty cfg n)
  · by_cases h_right_n : n ∈ right
    · rw [Std.DHashMap.getD_eq_getD_get?]
      rw [Std.DHashMap.unionWith_getElem_not_contains
        (m₁ := left) (m₂ := right)
        (f := fun _ => positionMapUnion cfg)
        (z := fun _ => emptyPositionMap)
        h_left_n]
      rw [Std.DHashMap.get?_eq_some_get h_right_n]
      exact positionMap_sound_sup
        (cfg := cfg) (n := n)
        (positionMap_sound_empty cfg n)
        (by
          simpa [Std.DHashMap.get_eq_getD
            (m := right) (a := n) (fallback := emptyPositionMap)
            (h := h_right_n)]
            using positionMap_sound_of_memo_sound h_right n)
    · have h_union_none :
          (Std.DHashMap.unionWith
            (fun _ => positionMapUnion cfg)
            (fun _ => emptyPositionMap)
            left right).get? n = none := by
        rw [Std.DHashMap.unionWith_getElem_not_contains
          (m₁ := left) (m₂ := right)
          (f := fun _ => positionMapUnion cfg)
          (z := fun _ => emptyPositionMap)
          h_left_n]
        simp [Std.DHashMap.get?_eq_none, h_right_n]
      rw [Std.DHashMap.getD_eq_getD_get?]
      rw [h_union_none]
      exact positionMap_sound_empty cfg n

set_option linter.unusedSectionVars false in
theorem positionMap_bounded_of_memo_bounded_sup
  {cfg : @CFG α ν} {input : Array α}
  {left right : MemoData (tag cfg) List}
  (h_left : memo_bounded cfg input left)
  (h_right : memo_bounded cfg input right)
  (n : ν) :
    positionMap_bounded cfg input
      ((left ⊔ right).getD n
        (Std.HashMap.emptyWithCapacity :
          Std.HashMap (MemoEntryKey ν) (ResultMap List (ParseTree cfg)))) := by
  let emptyPositionMap :
      Std.HashMap (MemoEntryKey ν) (ResultMap List (ParseTree cfg)) :=
    Std.HashMap.emptyWithCapacity
  change positionMap_bounded cfg input
    ((Std.DHashMap.unionWith
      (fun _ => positionMapUnion cfg)
      (fun _ => emptyPositionMap)
      left right).getD n emptyPositionMap)
  by_cases h_left_n : n ∈ left
  · by_cases h_right_n : n ∈ right
    · rw [Std.DHashMap.getD_eq_getD_get?]
      rw [Std.DHashMap.unionWith_getElem_both
        (m₁ := left) (m₂ := right)
        (f := fun _ => positionMapUnion cfg)
        (z := fun _ => emptyPositionMap)
        h_left_n h_right_n]
      exact positionMap_bounded_sup
        (cfg := cfg) (input := input)
        (by
          simpa [Std.DHashMap.get_eq_getD
            (m := left) (a := n) (fallback := emptyPositionMap)
            (h := h_left_n)]
            using positionMap_bounded_of_memo_bounded h_left n)
        (by
          simpa [Std.DHashMap.get_eq_getD
            (m := right) (a := n) (fallback := emptyPositionMap)
            (h := h_right_n)]
            using positionMap_bounded_of_memo_bounded h_right n)
    · rw [Std.DHashMap.getD_eq_getD_get?]
      rw [Std.DHashMap.unionWith_getElem_not_contains_right
        (m₁ := left) (m₂ := right)
        (f := fun _ => positionMapUnion cfg)
        (z := fun _ => emptyPositionMap)
        h_right_n]
      rw [Std.DHashMap.get?_eq_some_get h_left_n]
      exact positionMap_bounded_sup
        (cfg := cfg) (input := input)
        (by
          simpa [Std.DHashMap.get_eq_getD
            (m := left) (a := n) (fallback := emptyPositionMap)
            (h := h_left_n)]
            using positionMap_bounded_of_memo_bounded h_left n)
        (positionMap_bounded_empty cfg input)
  · by_cases h_right_n : n ∈ right
    · rw [Std.DHashMap.getD_eq_getD_get?]
      rw [Std.DHashMap.unionWith_getElem_not_contains
        (m₁ := left) (m₂ := right)
        (f := fun _ => positionMapUnion cfg)
        (z := fun _ => emptyPositionMap)
        h_left_n]
      rw [Std.DHashMap.get?_eq_some_get h_right_n]
      exact positionMap_bounded_sup
        (cfg := cfg) (input := input)
        (positionMap_bounded_empty cfg input)
        (by
          simpa [Std.DHashMap.get_eq_getD
            (m := right) (a := n) (fallback := emptyPositionMap)
            (h := h_right_n)]
            using positionMap_bounded_of_memo_bounded h_right n)
    · have h_union_none :
          (Std.DHashMap.unionWith
            (fun _ => positionMapUnion cfg)
            (fun _ => emptyPositionMap)
            left right).get? n = none := by
        rw [Std.DHashMap.unionWith_getElem_not_contains
          (m₁ := left) (m₂ := right)
          (f := fun _ => positionMapUnion cfg)
          (z := fun _ => emptyPositionMap)
          h_left_n]
        simp [Std.DHashMap.get?_eq_none, h_right_n]
      rw [Std.DHashMap.getD_eq_getD_get?]
      rw [h_union_none]
      exact positionMap_bounded_empty cfg input

theorem memo_sound_sup
  {cfg : @CFG α ν} {input : Array α}
  {left right : MemoData (tag cfg) List}
  (h_left : memo_sound cfg input left)
  (h_right : memo_sound cfg input right) :
    memo_sound cfg input (left ⊔ right) := by
  intro n key start end_ tree h_mem
  have h_position :=
    positionMap_sound_of_memo_sound_sup
      (cfg := cfg) (input := input)
      (left := left) (right := right) h_left h_right n
  exact h_position key start end_ tree (by
    simpa [cachedResultMap, Bot.bot] using h_mem)

theorem memo_bounded_sup
  {cfg : @CFG α ν} {input : Array α}
  {left right : MemoData (tag cfg) List}
  (h_left : memo_bounded cfg input left)
  (h_right : memo_bounded cfg input right) :
    memo_bounded cfg input (left ⊔ right) := by
  intro n key start end_ h_start tree h_mem
  have h_position :=
    positionMap_bounded_of_memo_bounded_sup
      (cfg := cfg) (input := input)
      (left := left) (right := right) h_left h_right n
  exact h_position key start end_ h_start tree (by
    simpa [cachedResultMap, Bot.bot] using h_mem)

theorem memo_wellFormed_sup
  {cfg : @CFG α ν} {input : Array α}
  {left right : MemoData (tag cfg) List}
  (h_left : memo_wellFormed cfg input left)
  (h_right : memo_wellFormed cfg input right) :
    memo_wellFormed cfg input (left ⊔ right) :=
  ⟨memo_sound_sup h_left.1 h_right.1,
    memo_bounded_sup h_left.2 h_right.2⟩

omit [BEq α] [DecidableEq α] [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
theorem cachedResultMap_eq_of_getElem?_eq_some
  {cfg : @CFG α ν} {memo : MemoData (tag cfg) List}
  {n : ν} {key : MemoKey ν} {start : ℕ}
  {resultMap : ResultMap List (ParseTree cfg)}
  (h_cache :
    (memo.getD n
      (Std.HashMap.emptyWithCapacity :
        Std.HashMap (MemoEntryKey ν) (ResultMap List (ParseTree cfg))))[(key, start)]? =
      some resultMap) :
    cachedResultMap cfg memo n key start = resultMap := by
  unfold cachedResultMap
  rw [Std.HashMap.getD_eq_getD_getElem?]
  rw [h_cache]
  rfl

omit [BEq α] [DecidableEq α] [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
theorem resultMap_sound_of_memo_sound_of_getElem?_eq_some
  {cfg : @CFG α ν} {input : Array α}
  {memo : MemoData (tag cfg) List}
  {n : ν} {key : MemoKey ν} {start : ℕ}
  {resultMap : ResultMap List (ParseTree cfg)}
  (h_memo : memo_sound cfg input memo)
  (h_cache :
    (memo.getD n
      (Std.HashMap.emptyWithCapacity :
        Std.HashMap (MemoEntryKey ν) (ResultMap List (ParseTree cfg))))[(key, start)]? =
      some resultMap) :
    resultMap_sound cfg n resultMap := by
  rw [← cachedResultMap_eq_of_getElem?_eq_some
    (cfg := cfg) (memo := memo) (n := n) (key := key)
    (start := start) h_cache]
  exact resultMap_sound_of_memo_sound h_memo n key start

omit [BEq α] [DecidableEq α] [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
theorem resultMap_bounded_of_memo_bounded_of_getElem?_eq_some
  {cfg : @CFG α ν} {input : Array α}
  {memo : MemoData (tag cfg) List}
  {n : ν} {key : MemoKey ν} {start : ℕ}
  {resultMap : ResultMap List (ParseTree cfg)}
  (h_memo : memo_bounded cfg input memo)
  (h_cache :
    (memo.getD n
      (Std.HashMap.emptyWithCapacity :
        Std.HashMap (MemoEntryKey ν) (ResultMap List (ParseTree cfg))))[(key, start)]? =
      some resultMap) :
    resultMap_bounded cfg input start resultMap := by
  rw [← cachedResultMap_eq_of_getElem?_eq_some
    (cfg := cfg) (memo := memo) (n := n) (key := key)
    (start := start) h_cache]
  exact resultMap_bounded_of_memo_bounded h_memo n key start

omit [BEq α] [DecidableEq α] [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
theorem memo_sound_memoWithCachedResult
  {cfg : @CFG α ν} {input : Array α}
  {memo : MemoData (tag cfg) List}
  {n : ν} {key : MemoKey ν} {start : ℕ}
  {resultMap : ResultMap List (ParseTree cfg)}
  (h_memo : memo_sound cfg input memo)
  (h_result : resultMap_sound cfg n resultMap) :
    memo_sound cfg input
      (memoWithCachedResult cfg memo n key start resultMap) := by
  intro n' key' start' end_ tree h_mem
  by_cases h_same : n' = n ∧ (key', start') = (key, start)
  · rcases h_same with ⟨h_n, h_entry⟩
    subst h_n
    cases h_entry
    rw [cachedResultMap_memoWithCachedResult_self] at h_mem
    exact h_result end_ tree h_mem
  · have h_ne : n' ≠ n ∨ (key', start') ≠ (key, start) := by
      by_cases h_n : n' = n
      · right
        intro h_entry
        exact h_same ⟨h_n, h_entry⟩
      · exact Or.inl h_n
    rw [cachedResultMap_memoWithCachedResult_ne
      (cfg := cfg) (memo := memo)
      (n := n) (n' := n') (key := key) (key' := key')
      (start := start) (start' := start') (resultMap := resultMap)
      h_ne] at h_mem
    exact h_memo n' key' start' end_ tree h_mem

omit [BEq α] [DecidableEq α] [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
theorem memo_bounded_memoWithCachedResult
  {cfg : @CFG α ν} {input : Array α}
  {memo : MemoData (tag cfg) List}
  {n : ν} {key : MemoKey ν} {start : ℕ}
  {resultMap : ResultMap List (ParseTree cfg)}
  (h_memo : memo_bounded cfg input memo)
  (h_result : resultMap_bounded cfg input start resultMap) :
    memo_bounded cfg input
      (memoWithCachedResult cfg memo n key start resultMap) := by
  intro n' key' start' end_ h_start tree h_mem
  by_cases h_same : n' = n ∧ (key', start') = (key, start)
  · rcases h_same with ⟨h_n, h_entry⟩
    subst h_n
    cases h_entry
    rw [cachedResultMap_memoWithCachedResult_self] at h_mem
    exact h_result end_ h_start tree h_mem
  · have h_ne : n' ≠ n ∨ (key', start') ≠ (key, start) := by
      by_cases h_n : n' = n
      · right
        intro h_entry
        exact h_same ⟨h_n, h_entry⟩
      · exact Or.inl h_n
    rw [cachedResultMap_memoWithCachedResult_ne
      (cfg := cfg) (memo := memo)
      (n := n) (n' := n') (key := key) (key' := key')
      (start := start) (start' := start') (resultMap := resultMap)
      h_ne] at h_mem
    exact h_memo n' key' start' end_ h_start tree h_mem

omit [BEq α] [DecidableEq α] [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
theorem memo_wellFormed_memoWithCachedResult
  {cfg : @CFG α ν} {input : Array α}
  {memo : MemoData (tag cfg) List}
  {n : ν} {key : MemoKey ν} {start : ℕ}
  {resultMap : ResultMap List (ParseTree cfg)}
  (h_memo : memo_wellFormed cfg input memo)
  (h_sound : resultMap_sound cfg n resultMap)
  (h_bounded : resultMap_bounded cfg input start resultMap) :
    memo_wellFormed cfg input
      (memoWithCachedResult cfg memo n key start resultMap) :=
  ⟨memo_sound_memoWithCachedResult h_memo.1 h_sound,
    memo_bounded_memoWithCachedResult h_memo.2 h_bounded⟩

omit [BEq α] [DecidableEq α] [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
theorem memo_sound_empty (cfg : @CFG α ν) (input : Array α) :
    memo_sound cfg input (startState : MemoData (tag cfg) List) := by
  intro n key start end_ tree h_mem
  simp [cachedResultMap, startState] at h_mem

omit [BEq α] [DecidableEq α] [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
theorem memo_bounded_empty (cfg : @CFG α ν) (input : Array α) :
    memo_bounded cfg input (startState : MemoData (tag cfg) List) := by
  intro n key start end_ h_start tree h_mem
  simp [cachedResultMap, startState] at h_mem

omit [BEq α] [DecidableEq α] [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
theorem memo_wellFormed_empty (cfg : @CFG α ν) (input : Array α) :
    memo_wellFormed cfg input (startState : MemoData (tag cfg) List) :=
  ⟨memo_sound_empty cfg input, memo_bounded_empty cfg input⟩

abbrev lower_sound (cfg : @CFG α ν)
  (n : ν) (p : ParserM (tag := tag cfg) α List (ParseTree cfg)) (input : Array α)
  :=
  ∀ memo : MemoData (tag cfg) List,
  memo_wellFormed cfg input memo →
  ∀ start end_ : ℕ,
  ∀ _h_bound : start ≤ end_ ∧ end_ ≤ input.size,
  ∀ tree ∈ ((p.lower start) memo input).1.getD end_ [],
    tree.Valid ∧ tree.root = Symbol.nonterm n

abbrev lower_result_sound (cfg : @CFG α ν)
  (n : ν) (p : ParserM (tag := tag cfg) α List (ParseTree cfg)) (input : Array α)
  :=
  ∀ memo : MemoData (tag cfg) List,
  memo_wellFormed cfg input memo →
  ∀ start end_ : ℕ,
  ∀ tree ∈ ((p.lower start) memo input).1.getD end_ [],
    tree.Valid ∧ tree.root = Symbol.nonterm n

abbrev lower_result_bounded (cfg : @CFG α ν)
  (p : ParserM (tag := tag cfg) α List (ParseTree cfg)) (input : Array α)
  :=
  ∀ memo : MemoData (tag cfg) List,
  memo_wellFormed cfg input memo →
  ∀ start end_ : ℕ,
  start ≤ input.size →
  ∀ tree, tree ∈ ((p.lower start) memo input).1.getD end_ [] →
    start ≤ end_ ∧ end_ ≤ input.size

abbrev lower_memo_wellFormed (cfg : @CFG α ν)
  {γ : Type u} [DecidableEq γ]
  (p : ParserM (tag := tag cfg) α List γ) (input : Array α)
  :=
  ∀ memo : MemoData (tag cfg) List,
  memo_wellFormed cfg input memo →
  ∀ start : ℕ,
    memo_wellFormed cfg input (((p.lower start) memo input).2.val)

omit [Fintype ν] in
theorem sound_of_lower_sound
  {cfg : @CFG α ν} {n : ν}
  {p : ParserM (tag := tag cfg) α List (ParseTree cfg)} {input : Array α}
  (h : lower_sound cfg n p input) :
    sound cfg n p input := by
  unfold sound at *
  intro start end_ h_bound tree h_mem
  rw [runParser_fst_eq_lower] at h_mem
  exact h (startState : MemoData (tag cfg) List)
    (memo_wellFormed_empty cfg input)
    start end_ h_bound tree (by simpa [Bot.bot] using h_mem)

omit [Fintype ν] in
theorem lower_sound_of_lower_result_sound
  {cfg : @CFG α ν} {n : ν}
  {p : ParserM (tag := tag cfg) α List (ParseTree cfg)} {input : Array α}
  (h : lower_result_sound cfg n p input) :
    lower_sound cfg n p input := by
  intro memo h_memo start end_ _h_bound tree h_mem
  exact h memo h_memo start end_ tree h_mem

omit [Fintype ν] in
theorem sound_of_lower_result_sound
  {cfg : @CFG α ν} {n : ν}
  {p : ParserM (tag := tag cfg) α List (ParseTree cfg)} {input : Array α}
  (h : lower_result_sound cfg n p input) :
    sound cfg n p input :=
  sound_of_lower_sound (lower_sound_of_lower_result_sound h)

omit [Fintype ν] in
theorem resultMap_sound_of_lower_result_sound
  {cfg : @CFG α ν} {n : ν}
  {p : ParserM (tag := tag cfg) α List (ParseTree cfg)} {input : Array α}
  (h : lower_result_sound cfg n p input)
  (memo : MemoData (tag cfg) List)
  (h_memo : memo_wellFormed cfg input memo)
  (start : ℕ) :
    resultMap_sound cfg n (((p.lower start) memo input).1) := by
  intro end_ tree h_mem
  exact h memo h_memo start end_ tree h_mem

omit [Fintype ν] in
theorem result_bounded_of_lower_result_bounded
  {cfg : @CFG α ν}
  {p : ParserM (tag := tag cfg) α List (ParseTree cfg)} {input : Array α}
  (h : lower_result_bounded cfg p input) :
    result_bounded cfg p input := by
  unfold result_bounded at *
  intro start end_ h_start tree h_mem
  rw [runParser_fst_eq_lower] at h_mem
  exact h (startState : MemoData (tag cfg) List)
    (memo_wellFormed_empty cfg input)
    start end_ h_start tree h_mem

omit [Fintype ν] in
theorem resultMap_bounded_of_lower_result_bounded
  {cfg : @CFG α ν}
  {p : ParserM (tag := tag cfg) α List (ParseTree cfg)} {input : Array α}
  (h : lower_result_bounded cfg p input)
  (memo : MemoData (tag cfg) List)
  (h_memo : memo_wellFormed cfg input memo)
  (start : ℕ) :
    resultMap_bounded cfg input start (((p.lower start) memo input).1) := by
  intro end_ h_start tree h_mem
  exact h memo h_memo start end_ h_start tree h_mem

omit [Fintype ν] in
theorem lower_map_memo_wellFormed
  {cfg : @CFG α ν} {γ δ : Type u} [DecidableEq γ] [DecidableEq δ]
  {p : ParserM (tag := tag cfg) α List γ} {f : γ → δ}
  {input : Array α}
  (h : ∀ memo : MemoData (tag cfg) List,
      memo_wellFormed cfg input memo →
      ∀ start : ℕ, memo_wellFormed cfg input (((p.lower start) memo input).2.val)) :
    ∀ memo : MemoData (tag cfg) List,
      memo_wellFormed cfg input memo →
      ∀ start : ℕ,
        memo_wellFormed cfg input
          (((f <$> p).lower start) memo input).2.val := by
  intro memo h_memo start
  rw [lower_map_snd_val_eq
    (tag := tag cfg) (β := α)
    (p := p) (f := f)
    (memo := memo) (input := input) (start := start)]
  exact h memo h_memo start

omit [Fintype ν] in
theorem lower_map_sound_of_forall
  {cfg : @CFG α ν} {γ : Type u} [DecidableEq γ]
  {p : ParserM (tag := tag cfg) α List γ}
  {f : γ → ParseTree cfg}
  {input : Array α} {n : ν}
  (h_p :
    ∀ memo : MemoData (tag cfg) List,
      memo_wellFormed cfg input memo →
      ∀ start end_ : ℕ,
      start ≤ end_ ∧ end_ ≤ input.size →
      ∀ x, x ∈ ((p.lower start) memo input).1.getD end_ [] →
        (f x).Valid ∧ (f x).root = Symbol.nonterm n) :
    lower_sound cfg n (f <$> p) input := by
  intro memo h_memo start end_ h_bound tree h_mem
  obtain ⟨x, h_x, h_tree⟩ :=
    mem_lower_map_exists_of_mem
      (tag := tag cfg) (β := α)
      (p := p) (f := f)
      (memo := memo) (input := input)
      (start := start) (end_pos := end_) (y := tree) h_mem
  rw [← h_tree]
  exact h_p memo h_memo start end_ h_bound x h_x

omit [Fintype ν] in
theorem lower_map_result_sound_of_forall
  {cfg : @CFG α ν} {γ : Type u} [DecidableEq γ]
  {p : ParserM (tag := tag cfg) α List γ}
  {f : γ → ParseTree cfg}
  {input : Array α} {n : ν}
  (h_p :
    ∀ memo : MemoData (tag cfg) List,
      memo_wellFormed cfg input memo →
      ∀ start end_ : ℕ,
      ∀ x, x ∈ ((p.lower start) memo input).1.getD end_ [] →
        (f x).Valid ∧ (f x).root = Symbol.nonterm n) :
    lower_result_sound cfg n (f <$> p) input := by
  intro memo h_memo start end_ tree h_mem
  obtain ⟨x, h_x, h_tree⟩ :=
    mem_lower_map_exists_of_mem
      (tag := tag cfg) (β := α)
      (p := p) (f := f)
      (memo := memo) (input := input)
      (start := start) (end_pos := end_) (y := tree) h_mem
  rw [← h_tree]
  exact h_p memo h_memo start end_ x h_x

omit [Fintype ν] in
theorem lower_map_result_bounded_of_forall
  {cfg : @CFG α ν} {γ : Type u} [DecidableEq γ]
  {p : ParserM (tag := tag cfg) α List γ}
  {f : γ → ParseTree cfg}
  {input : Array α}
  (h_p :
    ∀ memo : MemoData (tag cfg) List,
      memo_wellFormed cfg input memo →
      ∀ start end_ : ℕ,
      start ≤ input.size →
      ∀ x, x ∈ ((p.lower start) memo input).1.getD end_ [] →
        start ≤ end_ ∧ end_ ≤ input.size) :
    lower_result_bounded cfg (f <$> p) input := by
  intro memo h_memo start end_ h_start tree h_mem
  obtain ⟨x, h_x, _h_tree⟩ :=
    mem_lower_map_exists_of_mem
      (tag := tag cfg) (β := α)
      (p := p) (f := f)
      (memo := memo) (input := input)
      (start := start) (end_pos := end_) (y := tree) h_mem
  exact h_p memo h_memo start end_ h_start x h_x

omit [Fintype ν] in
theorem joinUnderCache_memo_wellFormed
  {cfg : @CFG α ν} {γ : Type u} [DecidableEq γ]
  {input : Array α}
  (acc act :
    MStateT (MemoData (tag cfg) List) (ReaderM (Array α))
      (ResultMap List γ))
  (h_acc :
    ∀ memo : MemoData (tag cfg) List,
      memo_wellFormed cfg input memo →
      memo_wellFormed cfg input ((acc memo input).2.val))
  (h_act :
    ∀ memo : MemoData (tag cfg) List,
      memo_wellFormed cfg input memo →
      memo_wellFormed cfg input ((act memo input).2.val)) :
    ∀ memo : MemoData (tag cfg) List,
      memo_wellFormed cfg input memo →
      memo_wellFormed cfg input ((joinUnderCache acc act memo input).2.val) := by
  intro memo h_memo
  rw [joinUnderCache_snd_eq]
  exact h_act _ (h_acc memo h_memo)

omit [Fintype ν] in
theorem traversable_foldl_joinUnderCache_memo_wellFormed
  {cfg : @CFG α ν} {γ : Type u} [DecidableEq γ]
  {input : Array α}
  (actions :
    List (MStateT (MemoData (tag cfg) List) (ReaderM (Array α))
      (ResultMap List γ)))
  (acc :
    MStateT (MemoData (tag cfg) List) (ReaderM (Array α))
      (ResultMap List γ))
  (h_acc :
    ∀ memo : MemoData (tag cfg) List,
      memo_wellFormed cfg input memo →
      memo_wellFormed cfg input ((acc memo input).2.val))
  (h_actions :
    ∀ action ∈ actions,
      ∀ memo : MemoData (tag cfg) List,
        memo_wellFormed cfg input memo →
        memo_wellFormed cfg input ((action memo input).2.val)) :
    ∀ memo : MemoData (tag cfg) List,
      memo_wellFormed cfg input memo →
      memo_wellFormed cfg input
        (((Traversable.foldl joinUnderCache acc actions) memo input).2.val) := by
  induction actions generalizing acc with
  | nil =>
      intro memo h_memo
      simpa [traversable_foldl_nil] using h_acc memo h_memo
  | cons action actions ih =>
      intro memo h_memo
      rw [traversable_foldl_cons]
      exact ih
        (acc := joinUnderCache acc action)
        (by
          exact joinUnderCache_memo_wellFormed
            (cfg := cfg) (input := input)
            (acc := acc) (act := action)
            h_acc
            (fun memo h_memo => h_actions action (by simp) memo h_memo))
        (fun action' h_action' memo h_memo =>
          h_actions action' (by simp [h_action']) memo h_memo)
        memo h_memo

omit [Fintype ν] in
theorem list_foldl_traversable_joinUnderCache_memo_wellFormed
  {cfg : @CFG α ν} {γ : Type u} [DecidableEq γ]
  {input : Array α}
  (groups :
    List (List (MStateT (MemoData (tag cfg) List) (ReaderM (Array α))
      (ResultMap List γ))))
  (acc :
    MStateT (MemoData (tag cfg) List) (ReaderM (Array α))
      (ResultMap List γ))
  (h_acc :
    ∀ memo : MemoData (tag cfg) List,
      memo_wellFormed cfg input memo →
      memo_wellFormed cfg input ((acc memo input).2.val))
  (h_groups :
    ∀ group ∈ groups, ∀ action ∈ group,
      ∀ memo : MemoData (tag cfg) List,
        memo_wellFormed cfg input memo →
        memo_wellFormed cfg input ((action memo input).2.val)) :
    ∀ memo : MemoData (tag cfg) List,
      memo_wellFormed cfg input memo →
      memo_wellFormed cfg input
        (((List.foldl (Traversable.foldl joinUnderCache) acc groups)
          memo input).2.val) := by
  induction groups generalizing acc with
  | nil =>
      intro memo h_memo
      simpa using h_acc memo h_memo
  | cons group groups ih =>
      intro memo h_memo
      simp only [List.foldl_cons]
      exact ih
        (acc := Traversable.foldl joinUnderCache acc group)
        (by
          exact traversable_foldl_joinUnderCache_memo_wellFormed
            (cfg := cfg) (input := input)
            (actions := group) (acc := acc)
            h_acc
            (fun action h_action memo h_memo =>
              h_groups group (by simp) action h_action memo h_memo))
        (fun group' h_group' action h_action memo h_memo =>
          h_groups group' (by simp [h_group']) action h_action memo h_memo)
        memo h_memo

omit [Fintype ν] in
theorem bindContinue_memo_wellFormed
  {cfg : @CFG α ν} {δ γ : Type u} [DecidableEq γ]
  {input : Array α}
  (resultMap : ResultMap List δ)
  (f : δ → Parser (tag := tag cfg) α List γ)
  (h_f :
    ∀ a start,
      ∀ memo : MemoData (tag cfg) List,
        memo_wellFormed cfg input memo →
        memo_wellFormed cfg input (((f a start) memo input).2.val)) :
    ∀ memo : MemoData (tag cfg) List,
      memo_wellFormed cfg input memo →
      memo_wellFormed cfg input
        ((Parser.bindContinue (tag := tag cfg) (β := α)
          resultMap f memo input).2.val) := by
  unfold Parser.bindContinue Parser.bindActions
  exact list_foldl_traversable_joinUnderCache_memo_wellFormed
    (cfg := cfg) (input := input)
    (groups := resultMap.toList.map
      (fun pair : ℕ × List δ =>
        match pair with
        | (j, values) => List.map (fun a => f a j) values))
    (acc := pure Std.HashMap.emptyWithCapacity)
    (by
      intro memo h_memo
      simpa [Pure.pure, instMonadMStateT, ReaderT.pure] using h_memo)
    (by
      intro group h_group action h_action memo h_memo
      rw [List.mem_map] at h_group
      rcases h_group with ⟨pair, _h_pair, rfl⟩
      rcases pair with ⟨j, values⟩
      simp at h_action
      rcases h_action with ⟨a, _h_a, rfl⟩
      exact h_f a j memo h_memo)

omit [Fintype ν] in
theorem parser_bind_memo_wellFormed
  {cfg : @CFG α ν} {δ γ : Type u} [DecidableEq γ]
  {input : Array α}
  (p : Parser (tag := tag cfg) α List δ)
  (f : δ → Parser (tag := tag cfg) α List γ)
  (h_p :
    ∀ start,
      ∀ memo : MemoData (tag cfg) List,
        memo_wellFormed cfg input memo →
        memo_wellFormed cfg input (((p start) memo input).2.val))
  (h_f :
    ∀ a start,
      ∀ memo : MemoData (tag cfg) List,
        memo_wellFormed cfg input memo →
        memo_wellFormed cfg input (((f a start) memo input).2.val)) :
    ∀ start,
      ∀ memo : MemoData (tag cfg) List,
        memo_wellFormed cfg input memo →
        memo_wellFormed cfg input
          (((Parser.bind p f start) memo input).2.val) := by
  intro start memo h_memo
  rw [parser_bind_snd_val_eq_bindRun
    (tag := tag cfg) (β := α)
    (p := p) (f := f)
    (memo := memo) (input := input) (start := start)]
  rw [bindRun_snd_eq_bindContinue
    (tag := tag cfg) (β := α)
    (p := p) (f := f)
    (memo := memo) (input := input) (start := start)]
  exact bindContinue_memo_wellFormed
    (cfg := cfg) (input := input)
    (resultMap := ((p start) memo input).1)
    (f := f)
    h_f
    (↑((p start) memo input).2)
    (h_p start memo h_memo)

omit [Fintype ν] in
theorem parser_pure_memo_wellFormed
  {cfg : @CFG α ν} {γ : Type u}
  {input : Array α} (x : γ) :
    ∀ start,
      ∀ memo : MemoData (tag cfg) List,
        memo_wellFormed cfg input memo →
        memo_wellFormed cfg input
          (((Pure.pure x : Parser (tag := tag cfg) α List γ) start)
            memo input).2.val := by
  intro start memo h_memo
  simpa [Pure.pure, instMonadMStateT, ReaderT.pure] using h_memo

omit [Fintype ν] in
theorem parser_orElse_memo_wellFormed
  {cfg : @CFG α ν} {γ : Type u} [DecidableEq γ]
  {input : Array α}
  (p q : Parser (tag := tag cfg) α List γ)
  (h_p :
    ∀ start,
      ∀ memo : MemoData (tag cfg) List,
        memo_wellFormed cfg input memo →
        memo_wellFormed cfg input (((p start) memo input).2.val))
  (h_q :
    ∀ start,
      ∀ memo : MemoData (tag cfg) List,
        memo_wellFormed cfg input memo →
        memo_wellFormed cfg input (((q start) memo input).2.val)) :
    ∀ start,
      ∀ memo : MemoData (tag cfg) List,
        memo_wellFormed cfg input memo →
        memo_wellFormed cfg input
          (((Parser.orElse p q start) memo input).2.val) := by
  intro start memo h_memo
  unfold Parser.orElse
  exact joinUnderCache_memo_wellFormed
    (cfg := cfg) (input := input)
    (acc := p start) (act := q start)
    (fun memo h_memo => h_p start memo h_memo)
    (fun memo h_memo => h_q start memo h_memo)
    memo h_memo

omit [Fintype ν] in
theorem lower_bind_constructor_memo_wellFormed
  {cfg : @CFG α ν} {δ γ : Type u} [DecidableEq γ]
  {input : Array α}
  (p : Parser (tag := tag cfg) α List δ)
  (k : δ → ParserM (tag := tag cfg) α List γ)
  (h_p :
    ∀ start,
      ∀ memo : MemoData (tag cfg) List,
        memo_wellFormed cfg input memo →
        memo_wellFormed cfg input (((p start) memo input).2.val))
  (h_k :
    ∀ a, lower_memo_wellFormed cfg (k a) input) :
    lower_memo_wellFormed cfg (ParserM.Bind p k) input := by
  intro memo h_memo start
  change memo_wellFormed cfg input
    (((Parser.bind p (fun a => (k a).lower) start) memo input).2.val)
  exact parser_bind_memo_wellFormed
    (cfg := cfg) (input := input)
    (p := p) (f := fun a => (k a).lower)
    h_p
    (fun a start memo h_memo => h_k a memo h_memo start)
    start memo h_memo

omit [Fintype ν] in
theorem lower_lift_memo_wellFormed
  {cfg : @CFG α ν} {γ : Type u} [DecidableEq γ]
  {input : Array α}
  (p : Parser (tag := tag cfg) α List γ)
  (h_p :
    ∀ start,
      ∀ memo : MemoData (tag cfg) List,
        memo_wellFormed cfg input memo →
        memo_wellFormed cfg input (((p start) memo input).2.val)) :
    lower_memo_wellFormed cfg (ParserM.lift p) input := by
  unfold ParserM.lift
  exact lower_bind_constructor_memo_wellFormed
    (cfg := cfg) (input := input)
    (p := p) (k := fun a =>
      ParserM.Return (tag := tag cfg) (β := α) (μ := List) a)
    h_p
    (by
      intro a memo h_memo start
      rw [lower_return_snd_val_eq
        (tag := tag cfg) (β := α)
        (a := a) (memo := memo) (input := input) (start := start)]
      exact h_memo)

omit [Fintype ν] in
theorem bind_action_prefix_memo_wellFormed
  {cfg : @CFG α ν} {δ γ : Type u} [DecidableEq γ]
  {input : Array α}
  (p : Parser (tag := tag cfg) α List δ)
  (k : δ → ParserM (tag := tag cfg) α List γ)
  (prePairs : List (ℕ × List δ)) (preValues : List δ)
  (split start : ℕ) {memo : MemoData (tag cfg) List}
  (h_p :
    ∀ start,
      ∀ memo : MemoData (tag cfg) List,
        memo_wellFormed cfg input memo →
        memo_wellFormed cfg input (((p start) memo input).2.val))
  (h_k : ∀ a, lower_memo_wellFormed cfg (k a) input)
  (h_memo : memo_wellFormed cfg input memo) :
    memo_wellFormed cfg input
      (((Traversable.foldl joinUnderCache
        (List.foldl (Traversable.foldl joinUnderCache)
          (pure Std.HashMap.emptyWithCapacity)
          (List.map
            (fun pair : ℕ × List δ =>
              match pair with
              | (j, values) => List.map (fun a => (k a).lower j) values)
            prePairs))
        (List.map (fun a => (k a).lower split) preValues))
        (↑((p start) memo input).2) input).2.val) := by
  let pairAction :
      ℕ × List δ →
        List (MStateT (MemoData (tag cfg) List) (ReaderM (Array α))
          (ResultMap List γ)) :=
    fun pair =>
      match pair with
      | (j, values) => List.map (fun a => (k a).lower j) values
  have h_after_p : memo_wellFormed cfg input ((p start memo input).2.val) :=
    h_p start memo h_memo
  have h_tail_prefix :
      ∀ action ∈ List.map (fun a => (k a).lower split) preValues,
        ∀ memo : MemoData (tag cfg) List,
          memo_wellFormed cfg input memo →
          memo_wellFormed cfg input ((action memo input).2.val) := by
    intro action h_action memo h_memo
    rw [List.mem_map] at h_action
    rcases h_action with ⟨a, _h_a, rfl⟩
    exact h_k a memo h_memo split
  change memo_wellFormed cfg input
    (((Traversable.foldl joinUnderCache
      (List.foldl (Traversable.foldl joinUnderCache)
        (pure Std.HashMap.emptyWithCapacity)
        (List.map pairAction prePairs))
      (List.map (fun a => (k a).lower split) preValues))
      (↑((p start) memo input).2) input).2.val)
  exact traversable_foldl_joinUnderCache_memo_wellFormed
    (cfg := cfg) (input := input)
    (actions := List.map (fun a => (k a).lower split) preValues)
    (acc := List.foldl (Traversable.foldl joinUnderCache)
      (pure Std.HashMap.emptyWithCapacity)
      (List.map pairAction prePairs))
    (by
      intro memo' h_memo'
      -- The theorem is applied below only at the pivot-produced memo state.
      -- For an arbitrary memo' the same fold preservation argument applies.
      exact list_foldl_traversable_joinUnderCache_memo_wellFormed
        (cfg := cfg) (input := input)
        (groups := List.map pairAction prePairs)
        (acc := pure Std.HashMap.emptyWithCapacity)
        (by
          intro memo h_memo
          simpa [Pure.pure, instMonadMStateT, ReaderT.pure] using h_memo)
        (by
          intro group h_group action h_action memo h_memo
          rw [List.mem_map] at h_group
          rcases h_group with ⟨pair, _h_pair, rfl⟩
          rcases pair with ⟨j, values⟩
          simp [pairAction] at h_action
          rcases h_action with ⟨a, _h_a, rfl⟩
          exact h_k a memo h_memo j)
        memo' h_memo')
    h_tail_prefix
    (↑((p start) memo input).2)
    h_after_p

omit [Fintype ν] in
theorem mem_lower_bind_exists_action_split_wf
  {cfg : @CFG α ν} {δ γ : Type u} [DecidableEq γ]
  {input : Array α}
  (p : Parser (tag := tag cfg) α List δ)
  (k : δ → ParserM (tag := tag cfg) α List γ)
  {memo : MemoData (tag cfg) List} {start end_ : ℕ} {x : γ}
  (h_p :
    ∀ start,
      ∀ memo : MemoData (tag cfg) List,
        memo_wellFormed cfg input memo →
        memo_wellFormed cfg input (((p start) memo input).2.val))
  (h_k : ∀ a, lower_memo_wellFormed cfg (k a) input)
  (h_memo : memo_wellFormed cfg input memo)
  (h :
    x ∈ (((ParserM.Bind p k).lower start) memo input).1.getD end_ []) :
    ∃ split a memoPrefix,
      memo_wellFormed cfg input memoPrefix ∧
      x ∈ (((k a).lower split) memoPrefix input).1.getD end_ [] := by
  obtain ⟨prePairs, _postPairs, split, _values, preValues, _postValues, a,
    _h_toList, _h_values, h_action⟩ :=
    mem_lower_bind_exists_action_split_mem
      (tag := tag cfg) (β := α)
      (p := p) (k := k)
      (memo := memo) (input := input)
      (start := start) (end_pos := end_) (x := x) h
  let memoPrefix : MemoData (tag cfg) List :=
    ((Traversable.foldl joinUnderCache
      (List.foldl (Traversable.foldl joinUnderCache)
        (pure Std.HashMap.emptyWithCapacity)
        (List.map
          (fun pair : ℕ × List δ =>
            match pair with
              | (j, values) => List.map (fun a => (k a).lower j) values)
          prePairs))
      (List.map (fun a => (k a).lower split) preValues))
      (↑((p start) memo input).2) input).2.val
  have h_prefix_wf :
      memo_wellFormed cfg input memoPrefix := by
    simpa [memoPrefix] using
      (bind_action_prefix_memo_wellFormed
        (cfg := cfg) (input := input)
        (p := p) (k := k)
        (prePairs := prePairs) (preValues := preValues)
        (split := split) (start := start)
        (memo := memo) h_p h_k h_memo)
  have h_action' :
      x ∈ (((k a).lower split) memoPrefix input).1.getD end_ [] := by
    simpa [memoPrefix] using h_action
  exact ⟨split, a, memoPrefix, h_prefix_wf, h_action'⟩

omit [Fintype ν] in
theorem lower_bind_constructor_result_sound
  {cfg : @CFG α ν} {δ : Type u}
  {input : Array α} {n : ν}
  (p : Parser (tag := tag cfg) α List δ)
  (k : δ → ParserM (tag := tag cfg) α List (ParseTree cfg))
  (h_p_memo :
    ∀ start,
      ∀ memo : MemoData (tag cfg) List,
        memo_wellFormed cfg input memo →
        memo_wellFormed cfg input (((p start) memo input).2.val))
  (h_k_sound : ∀ a, lower_result_sound cfg n (k a) input)
  (h_k_memo : ∀ a, lower_memo_wellFormed cfg (k a) input) :
    lower_result_sound cfg n (ParserM.Bind p k) input := by
  intro memo h_memo start end_ tree h_mem
  obtain ⟨split, a, memoPrefix, h_prefix_wf, h_action⟩ :=
    mem_lower_bind_exists_action_split_wf
      (cfg := cfg) (input := input)
      (p := p) (k := k)
      (memo := memo) (start := start) (end_ := end_)
      (x := tree) h_p_memo h_k_memo h_memo h_mem
  exact h_k_sound a memoPrefix h_prefix_wf split end_ tree h_action

omit [Fintype ν] in
theorem lower_bind_constructor_result_bounded
  {cfg : @CFG α ν} {δ : Type u}
  {input : Array α}
  (p : Parser (tag := tag cfg) α List δ)
  (k : δ → ParserM (tag := tag cfg) α List (ParseTree cfg))
  (h_p_bounded :
    ∀ memo : MemoData (tag cfg) List,
      memo_wellFormed cfg input memo →
      ∀ start split : ℕ,
      start ≤ input.size →
      ∀ a : δ, a ∈ ((p start) memo input).1.getD split [] →
        start ≤ split ∧ split ≤ input.size)
  (h_p_memo :
    ∀ start,
      ∀ memo : MemoData (tag cfg) List,
        memo_wellFormed cfg input memo →
        memo_wellFormed cfg input (((p start) memo input).2.val))
  (h_k_bounded : ∀ a, lower_result_bounded cfg (k a) input)
  (h_k_memo : ∀ a, lower_memo_wellFormed cfg (k a) input) :
    lower_result_bounded cfg (ParserM.Bind p k) input := by
  intro memo h_memo start end_ h_start tree h_mem
  obtain ⟨prePairs, _postPairs, split, values, preValues, _postValues, a,
    h_toList, h_values, h_action⟩ :=
    mem_lower_bind_exists_action_split_mem
      (tag := tag cfg) (β := α)
      (p := p) (k := k)
      (memo := memo) (input := input)
      (start := start) (end_pos := end_) (x := tree) h_mem
  have h_get : ((p start) memo input).1[split]? = some values := by
    rw [← Std.HashMap.mem_toList_iff_getElem?_eq_some]
    rw [h_toList]
    simp
  have h_a_mem : a ∈ ((p start) memo input).1.getD split [] := by
    rw [Std.HashMap.getD_eq_getD_getElem?]
    simp [h_get, h_values]
  have h_split_bounds :
      start ≤ split ∧ split ≤ input.size :=
    h_p_bounded memo h_memo start split h_start a h_a_mem
  let memoPrefix : MemoData (tag cfg) List :=
    ((Traversable.foldl joinUnderCache
      (List.foldl (Traversable.foldl joinUnderCache)
        (pure Std.HashMap.emptyWithCapacity)
        (List.map
          (fun pair : ℕ × List δ =>
            match pair with
            | (j, values) => List.map (fun a => (k a).lower j) values)
          prePairs))
      (List.map (fun a => (k a).lower split) preValues))
      (↑((p start) memo input).2) input).2.val
  have h_prefix_wf :
      memo_wellFormed cfg input memoPrefix := by
    simpa [memoPrefix] using
      (bind_action_prefix_memo_wellFormed
        (cfg := cfg) (input := input)
        (p := p) (k := k)
        (prePairs := prePairs) (preValues := preValues)
        (split := split) (start := start)
        (memo := memo) h_p_memo h_k_memo h_memo)
  have h_action' :
      tree ∈ (((k a).lower split) memoPrefix input).1.getD end_ [] := by
    simpa [memoPrefix] using h_action
  have h_tail_bounds :
      split ≤ end_ ∧ end_ ≤ input.size :=
    h_k_bounded a memoPrefix h_prefix_wf split end_
      h_split_bounds.2 tree h_action'
  exact ⟨Nat.le_trans h_split_bounds.1 h_tail_bounds.1, h_tail_bounds.2⟩

omit [Fintype ν] in
theorem lower_bind_constructor_sound
  {cfg : @CFG α ν} {δ : Type u}
  {input : Array α} {n : ν}
  (p : Parser (tag := tag cfg) α List δ)
  (k : δ → ParserM (tag := tag cfg) α List (ParseTree cfg))
  (h_p_bounded :
    ∀ memo : MemoData (tag cfg) List,
      memo_wellFormed cfg input memo →
      ∀ start split : ℕ,
      start ≤ input.size →
      ∀ a : δ, a ∈ ((p start) memo input).1.getD split [] →
        start ≤ split ∧ split ≤ input.size)
  (h_p_memo :
    ∀ start,
      ∀ memo : MemoData (tag cfg) List,
        memo_wellFormed cfg input memo →
        memo_wellFormed cfg input (((p start) memo input).2.val))
  (h_k_sound : ∀ a, lower_sound cfg n (k a) input)
  (h_k_bounded : ∀ a, lower_result_bounded cfg (k a) input)
  (h_k_memo : ∀ a, lower_memo_wellFormed cfg (k a) input) :
    lower_sound cfg n (ParserM.Bind p k) input := by
  intro memo h_memo start end_ h_bound tree h_mem
  obtain ⟨prePairs, _postPairs, split, values, preValues, _postValues, a,
    h_toList, h_values, h_action⟩ :=
    mem_lower_bind_exists_action_split_mem
      (tag := tag cfg) (β := α)
      (p := p) (k := k)
      (memo := memo) (input := input)
      (start := start) (end_pos := end_) (x := tree) h_mem
  have h_get : ((p start) memo input).1[split]? = some values := by
    rw [← Std.HashMap.mem_toList_iff_getElem?_eq_some]
    rw [h_toList]
    simp
  have h_a_mem : a ∈ ((p start) memo input).1.getD split [] := by
    rw [Std.HashMap.getD_eq_getD_getElem?]
    simp [h_get, h_values]
  have h_split_bounds :
      start ≤ split ∧ split ≤ input.size :=
    h_p_bounded memo h_memo start split
      (Nat.le_trans h_bound.1 h_bound.2) a h_a_mem
  let memoPrefix : MemoData (tag cfg) List :=
    ((Traversable.foldl joinUnderCache
      (List.foldl (Traversable.foldl joinUnderCache)
        (pure Std.HashMap.emptyWithCapacity)
        (List.map
          (fun pair : ℕ × List δ =>
            match pair with
            | (j, values) => List.map (fun a => (k a).lower j) values)
          prePairs))
      (List.map (fun a => (k a).lower split) preValues))
      (↑((p start) memo input).2) input).2.val
  have h_prefix_wf :
      memo_wellFormed cfg input memoPrefix := by
    simpa [memoPrefix] using
      (bind_action_prefix_memo_wellFormed
        (cfg := cfg) (input := input)
        (p := p) (k := k)
        (prePairs := prePairs) (preValues := preValues)
        (split := split) (start := start)
        (memo := memo) h_p_memo h_k_memo h_memo)
  have h_action' :
      tree ∈ (((k a).lower split) memoPrefix input).1.getD end_ [] := by
    simpa [memoPrefix] using h_action
  have h_tail_bounds :
      split ≤ end_ ∧ end_ ≤ input.size :=
    h_k_bounded a memoPrefix h_prefix_wf split end_
      h_split_bounds.2 tree h_action'
  exact h_k_sound a memoPrefix h_prefix_wf split end_
    h_tail_bounds tree h_action'

omit [Fintype ν] in
theorem lower_sup_memo_wellFormed
  {cfg : @CFG α ν} {γ : Type u} [DecidableEq γ]
  {input : Array α}
  (p q : ParserM (tag := tag cfg) α List γ)
  (h_p : lower_memo_wellFormed cfg p input)
  (h_q : lower_memo_wellFormed cfg q input) :
    lower_memo_wellFormed cfg (p ⊔ q) input := by
  cases p with
  | Return x =>
      cases q with
      | Return y =>
          change lower_memo_wellFormed cfg
            (ParserM.Bind
              (Parser.orElse
                (Pure.pure x : Parser (tag := tag cfg) α List γ)
                (Pure.pure y : Parser (tag := tag cfg) α List γ))
              (ParserM.Return (tag := tag cfg) (β := α) (μ := List)))
            input
          exact lower_bind_constructor_memo_wellFormed
            (cfg := cfg) (input := input)
            (p := Parser.orElse
              (Pure.pure x : Parser (tag := tag cfg) α List γ)
              (Pure.pure y : Parser (tag := tag cfg) α List γ))
            (k := ParserM.Return (tag := tag cfg) (β := α) (μ := List))
            (parser_orElse_memo_wellFormed
              (cfg := cfg) (input := input)
              (p := Pure.pure x)
              (q := Pure.pure y)
              (parser_pure_memo_wellFormed (cfg := cfg) (input := input) x)
              (parser_pure_memo_wellFormed (cfg := cfg) (input := input) y))
            (by
              intro a memo h_memo start
              rw [lower_return_snd_val_eq
                (tag := tag cfg) (β := α)
                (a := a) (memo := memo) (input := input) (start := start)]
              exact h_memo)
      | Bind q kq =>
          change lower_memo_wellFormed cfg
            (ParserM.lift
              (Parser.orElse
                (Pure.pure x : Parser (tag := tag cfg) α List γ)
                (Parser.bind q (fun a => (kq a).lower))))
            input
          exact lower_lift_memo_wellFormed
            (cfg := cfg) (input := input)
            (p := Parser.orElse
              (Pure.pure x : Parser (tag := tag cfg) α List γ)
              (Parser.bind q (fun a => (kq a).lower)))
            (parser_orElse_memo_wellFormed
              (cfg := cfg) (input := input)
              (p := Pure.pure x)
              (q := Parser.bind q (fun a => (kq a).lower))
              (parser_pure_memo_wellFormed (cfg := cfg) (input := input) x)
              (by
                intro start memo h_memo
                exact h_q memo h_memo start))
  | Bind p kp =>
      cases q with
      | Return y =>
          change lower_memo_wellFormed cfg
            (ParserM.lift
              (Parser.orElse
                (Parser.bind p (fun a => (kp a).lower))
                (Pure.pure y : Parser (tag := tag cfg) α List γ)))
            input
          exact lower_lift_memo_wellFormed
            (cfg := cfg) (input := input)
            (p := Parser.orElse
              (Parser.bind p (fun a => (kp a).lower))
              (Pure.pure y : Parser (tag := tag cfg) α List γ))
            (parser_orElse_memo_wellFormed
              (cfg := cfg) (input := input)
              (p := Parser.bind p (fun a => (kp a).lower))
              (q := Pure.pure y)
              (by
                intro start memo h_memo
                exact h_p memo h_memo start)
              (parser_pure_memo_wellFormed (cfg := cfg) (input := input) y))
      | Bind q kq =>
          change lower_memo_wellFormed cfg
            (ParserM.lift
              (Parser.orElse
                (Parser.bind p (fun a => (kp a).lower))
                (Parser.bind q (fun a => (kq a).lower))))
            input
          exact lower_lift_memo_wellFormed
            (cfg := cfg) (input := input)
            (p := Parser.orElse
              (Parser.bind p (fun a => (kp a).lower))
              (Parser.bind q (fun a => (kq a).lower)))
            (parser_orElse_memo_wellFormed
              (cfg := cfg) (input := input)
              (p := Parser.bind p (fun a => (kp a).lower))
              (q := Parser.bind q (fun a => (kq a).lower))
              (by
                intro start memo h_memo
                exact h_p memo h_memo start)
              (by
                intro start memo h_memo
                exact h_q memo h_memo start))

set_option linter.unusedSectionVars false in
theorem resultMap_sound_memoizeStep_cache
  {cfg : @CFG α ν} {input : Array α}
  (counter : Counter ν)
  (g : ((t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg)) →
      (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  (next : ℕ → (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  {n : ν} {memo : MemoData (tag cfg) List} {start : ℕ}
  {cached : ResultMap List (ParseTree cfg)}
  (h_memo : memo_sound cfg input memo)
  (h_cache :
    (memo.getD n ⊥)[(Counter.toKey counter, start)]? = some cached) :
    resultMap_sound cfg n
      (memoizeStep counter g n next start memo input).1 := by
  have h_cache_explicit :
      (memo.getD n
        (Std.HashMap.emptyWithCapacity :
          Std.HashMap (MemoEntryKey ν) (ResultMap List (ParseTree cfg))))[(Counter.toKey counter, start)]? =
        some cached := by
    simpa [Bot.bot] using h_cache
  rw [memoizeStep_cache_fst_eq
    (counter := counter) (g := g) (next := next) (t := n)
    (memo := memo) (input := input) (start := start)
    (cached := cached) h_cache]
  exact resultMap_sound_of_memo_sound_of_getElem?_eq_some
    (cfg := cfg) (input := input) (memo := memo)
    (n := n) (key := Counter.toKey counter) (start := start)
    h_memo h_cache_explicit

set_option linter.unusedSectionVars false in
theorem resultMap_bounded_memoizeStep_cache
  {cfg : @CFG α ν} {input : Array α}
  (counter : Counter ν)
  (g : ((t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg)) →
      (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  (next : ℕ → (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  {n : ν} {memo : MemoData (tag cfg) List} {start : ℕ}
  {cached : ResultMap List (ParseTree cfg)}
  (h_memo : memo_bounded cfg input memo)
  (h_cache :
    (memo.getD n ⊥)[(Counter.toKey counter, start)]? = some cached) :
    resultMap_bounded cfg input start
      (memoizeStep counter g n next start memo input).1 := by
  have h_cache_explicit :
      (memo.getD n
        (Std.HashMap.emptyWithCapacity :
          Std.HashMap (MemoEntryKey ν) (ResultMap List (ParseTree cfg))))[(Counter.toKey counter, start)]? =
        some cached := by
    simpa [Bot.bot] using h_cache
  rw [memoizeStep_cache_fst_eq
    (counter := counter) (g := g) (next := next) (t := n)
    (memo := memo) (input := input) (start := start)
    (cached := cached) h_cache]
  exact resultMap_bounded_of_memo_bounded_of_getElem?_eq_some
    (cfg := cfg) (input := input) (memo := memo)
    (n := n) (key := Counter.toKey counter) (start := start)
    h_memo h_cache_explicit

set_option linter.unusedSectionVars false in
theorem memo_sound_memoizeStep_cache
  {cfg : @CFG α ν} {input : Array α}
  (counter : Counter ν)
  (g : ((t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg)) →
      (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  (next : ℕ → (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  {n : ν} {memo : MemoData (tag cfg) List} {start : ℕ}
  {cached : ResultMap List (ParseTree cfg)}
  (h_memo : memo_sound cfg input memo)
  (h_cache :
    (memo.getD n ⊥)[(Counter.toKey counter, start)]? = some cached) :
    memo_sound cfg input
      (memoizeStep counter g n next start memo input).2.val := by
  rw [memoizeStep_cache_snd_val_eq
    (counter := counter) (g := g) (next := next) (t := n)
    (memo := memo) (input := input) (start := start)
    (cached := cached) h_cache]
  exact h_memo

set_option linter.unusedSectionVars false in
theorem memo_bounded_memoizeStep_cache
  {cfg : @CFG α ν} {input : Array α}
  (counter : Counter ν)
  (g : ((t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg)) →
      (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  (next : ℕ → (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  {n : ν} {memo : MemoData (tag cfg) List} {start : ℕ}
  {cached : ResultMap List (ParseTree cfg)}
  (h_memo : memo_bounded cfg input memo)
  (h_cache :
    (memo.getD n ⊥)[(Counter.toKey counter, start)]? = some cached) :
    memo_bounded cfg input
      (memoizeStep counter g n next start memo input).2.val := by
  rw [memoizeStep_cache_snd_val_eq
    (counter := counter) (g := g) (next := next) (t := n)
    (memo := memo) (input := input) (start := start)
    (cached := cached) h_cache]
  exact h_memo

set_option linter.unusedSectionVars false in
theorem memo_wellFormed_memoizeStep_cache
  {cfg : @CFG α ν} {input : Array α}
  (counter : Counter ν)
  (g : ((t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg)) →
      (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  (next : ℕ → (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  {n : ν} {memo : MemoData (tag cfg) List} {start : ℕ}
  {cached : ResultMap List (ParseTree cfg)}
  (h_memo : memo_wellFormed cfg input memo)
  (h_cache :
    (memo.getD n ⊥)[(Counter.toKey counter, start)]? = some cached) :
    memo_wellFormed cfg input
      (memoizeStep counter g n next start memo input).2.val :=
  ⟨memo_sound_memoizeStep_cache
      (cfg := cfg) (input := input)
      (counter := counter) (g := g) (next := next)
      (n := n) (memo := memo) (start := start)
      (cached := cached) h_memo.1 h_cache,
    memo_bounded_memoizeStep_cache
      (cfg := cfg) (input := input)
      (counter := counter) (g := g) (next := next)
      (n := n) (memo := memo) (start := start)
      (cached := cached) h_memo.2 h_cache⟩

set_option linter.unusedSectionVars false in
theorem resultMap_sound_memoizeStep_compute
  {cfg : @CFG α ν} {input : Array α}
  (counter : Counter ν)
  (g : ((t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg)) →
      (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  (next : ℕ → (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  {n : ν} {memo : MemoData (tag cfg) List} {start : ℕ}
  (h_no_cache :
    (memo.getD n ⊥)[(Counter.toKey counter, start)]? = none)
  (h_body :
    resultMap_sound cfg n
      ((((g (next (input.size - start + 1)) n).lower start)
        memo input).1)) :
    resultMap_sound cfg n
      (memoizeStep counter g n next start memo input).1 := by
  rw [memoizeStep_compute_fst_eq
    (counter := counter) (g := g) (next := next) (t := n)
    (memo := memo) (input := input) (start := start)
    h_no_cache]
  exact h_body

set_option linter.unusedSectionVars false in
theorem resultMap_bounded_memoizeStep_compute
  {cfg : @CFG α ν} {input : Array α}
  (counter : Counter ν)
  (g : ((t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg)) →
      (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  (next : ℕ → (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  {n : ν} {memo : MemoData (tag cfg) List} {start : ℕ}
  (h_no_cache :
    (memo.getD n ⊥)[(Counter.toKey counter, start)]? = none)
  (h_body :
    resultMap_bounded cfg input start
      ((((g (next (input.size - start + 1)) n).lower start)
        memo input).1)) :
    resultMap_bounded cfg input start
      (memoizeStep counter g n next start memo input).1 := by
  rw [memoizeStep_compute_fst_eq
    (counter := counter) (g := g) (next := next) (t := n)
    (memo := memo) (input := input) (start := start)
    h_no_cache]
  exact h_body

set_option linter.unusedSectionVars false in
theorem resultMap_sound_memoizeStep
  {cfg : @CFG α ν} {input : Array α}
  (counter : Counter ν)
  (g : ((t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg)) →
      (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  (next : ℕ → (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  {n : ν} {memo : MemoData (tag cfg) List} {start : ℕ}
  (h_memo : memo_sound cfg input memo)
  (h_compute :
    ∀ _h_no_cache :
      (memo.getD n ⊥)[(Counter.toKey counter, start)]? = none,
      resultMap_sound cfg n
        ((((g (next (input.size - start + 1)) n).lower start)
          memo input).1)) :
    resultMap_sound cfg n
      (memoizeStep counter g n next start memo input).1 := by
  cases h_lookup :
      (memo.getD n ⊥)[(Counter.toKey counter, start)]? with
  | none =>
      exact resultMap_sound_memoizeStep_compute
        (cfg := cfg) (input := input)
        (counter := counter) (g := g) (next := next)
        (n := n) (memo := memo) (start := start)
        h_lookup (h_compute h_lookup)
  | some cached =>
      exact resultMap_sound_memoizeStep_cache
        (cfg := cfg) (input := input)
        (counter := counter) (g := g) (next := next)
        (n := n) (memo := memo) (start := start)
        (cached := cached) h_memo h_lookup

set_option linter.unusedSectionVars false in
theorem resultMap_bounded_memoizeStep
  {cfg : @CFG α ν} {input : Array α}
  (counter : Counter ν)
  (g : ((t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg)) →
      (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  (next : ℕ → (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  {n : ν} {memo : MemoData (tag cfg) List} {start : ℕ}
  (h_memo : memo_bounded cfg input memo)
  (h_compute :
    ∀ _h_no_cache :
      (memo.getD n ⊥)[(Counter.toKey counter, start)]? = none,
      resultMap_bounded cfg input start
        ((((g (next (input.size - start + 1)) n).lower start)
          memo input).1)) :
    resultMap_bounded cfg input start
      (memoizeStep counter g n next start memo input).1 := by
  cases h_lookup :
      (memo.getD n ⊥)[(Counter.toKey counter, start)]? with
  | none =>
      exact resultMap_bounded_memoizeStep_compute
        (cfg := cfg) (input := input)
        (counter := counter) (g := g) (next := next)
        (n := n) (memo := memo) (start := start)
        h_lookup (h_compute h_lookup)
  | some cached =>
      exact resultMap_bounded_memoizeStep_cache
        (cfg := cfg) (input := input)
        (counter := counter) (g := g) (next := next)
        (n := n) (memo := memo) (start := start)
        (cached := cached) h_memo h_lookup

set_option linter.unusedSectionVars false in
theorem memo_wellFormed_memoizeStep_compute
  {cfg : @CFG α ν} {input : Array α}
  (counter : Counter ν)
  (g : ((t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg)) →
      (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  (next : ℕ → (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  {n : ν} {memo : MemoData (tag cfg) List} {start : ℕ}
  (h_no_cache :
    (memo.getD n ⊥)[(Counter.toKey counter, start)]? = none)
  (h_body_memo :
    memo_wellFormed cfg input
      ((((g (next (input.size - start + 1)) n).lower start)
        memo input).2.val))
  (h_body_sound :
    resultMap_sound cfg n
      ((((g (next (input.size - start + 1)) n).lower start)
        memo input).1))
  (h_body_bounded :
    resultMap_bounded cfg input start
      ((((g (next (input.size - start + 1)) n).lower start)
        memo input).1)) :
    memo_wellFormed cfg input
      (memoizeStep counter g n next start memo input).2.val := by
  let body :=
    (((g (next (input.size - start + 1)) n).lower start) memo input)
  have h_insert :
      memo_wellFormed cfg input
        (body.2.val.insert n
          ((body.2.val.getD n ⊥).insert
            (Counter.toKey counter, start) body.1)) := by
    have h_cached :
        memo_wellFormed cfg input
          (memoWithCachedResult cfg body.2.val n
            (Counter.toKey counter) start body.1) :=
      memo_wellFormed_memoWithCachedResult
        (cfg := cfg) (input := input)
        (memo := body.2.val) (n := n)
        (key := Counter.toKey counter) (start := start)
        (resultMap := body.1)
        (by simpa [body] using h_body_memo)
        (by simpa [body] using h_body_sound)
        (by simpa [body] using h_body_bounded)
    simpa [memoWithCachedResult, Bot.bot] using h_cached
  have h_sup :
      memo_wellFormed cfg input
        ((body.2.val.insert n
          ((body.2.val.getD n ⊥).insert
            (Counter.toKey counter, start) body.1)) ⊔ body.2.val) :=
    memo_wellFormed_sup
      (cfg := cfg) (input := input)
      (left := body.2.val.insert n
        ((body.2.val.getD n ⊥).insert
          (Counter.toKey counter, start) body.1))
      (right := body.2.val)
      h_insert (by simpa [body] using h_body_memo)
  rw [memoizeStep_compute_snd_val_eq
    (counter := counter) (g := g) (next := next) (t := n)
    (memo := memo) (input := input) (start := start)
    h_no_cache]
  simpa [body]
    using h_sup

set_option linter.unusedSectionVars false in
theorem memo_wellFormed_memoizeStep
  {cfg : @CFG α ν} {input : Array α}
  (counter : Counter ν)
  (g : ((t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg)) →
      (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  (next : ℕ → (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  {n : ν} {memo : MemoData (tag cfg) List} {start : ℕ}
  (h_memo : memo_wellFormed cfg input memo)
  (h_compute :
    ∀ _h_no_cache :
      (memo.getD n ⊥)[(Counter.toKey counter, start)]? = none,
      memo_wellFormed cfg input
          ((((g (next (input.size - start + 1)) n).lower start)
            memo input).2.val) ∧
        resultMap_sound cfg n
          ((((g (next (input.size - start + 1)) n).lower start)
            memo input).1) ∧
        resultMap_bounded cfg input start
          ((((g (next (input.size - start + 1)) n).lower start)
            memo input).1)) :
    memo_wellFormed cfg input
      (memoizeStep counter g n next start memo input).2.val := by
  cases h_lookup :
      (memo.getD n ⊥)[(Counter.toKey counter, start)]? with
  | none =>
      have h_body := h_compute h_lookup
      exact memo_wellFormed_memoizeStep_compute
        (cfg := cfg) (input := input)
        (counter := counter) (g := g) (next := next)
        (n := n) (memo := memo) (start := start)
        h_lookup h_body.1 h_body.2.1 h_body.2.2
  | some cached =>
      exact memo_wellFormed_memoizeStep_cache
        (cfg := cfg) (input := input)
        (counter := counter) (g := g) (next := next)
        (n := n) (memo := memo) (start := start)
        (cached := cached) h_memo h_lookup

set_option linter.unusedSectionVars false in
theorem lower_sound_memoizeStep_lift
  {cfg : @CFG α ν} {input : Array α}
  (counter : Counter ν)
  (g : ((t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg)) →
      (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  (next : ℕ → (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  {n : ν}
  (h_compute :
    ∀ memo : MemoData (tag cfg) List,
      memo_wellFormed cfg input memo →
      ∀ start : ℕ,
      ∀ _h_no_cache :
        (memo.getD n ⊥)[(Counter.toKey counter, start)]? = none,
        resultMap_sound cfg n
          ((((g (next (input.size - start + 1)) n).lower start)
            memo input).1)) :
    lower_sound cfg n
      (ParserM.lift (memoizeStep counter g n next)) input := by
  intro memo h_memo start end_ _h_bound tree h_mem
  have h_mem_step :
      tree ∈ (memoizeStep counter g n next start memo input).1.getD end_ [] :=
    mem_lower_lift_exists_of_mem
      (tag := tag cfg) (β := α)
      (p := memoizeStep counter g n next)
      (memo := memo) (input := input)
      (start := start) (end_pos := end_) (x := tree) h_mem
  have h_sound :
      resultMap_sound cfg n
        (memoizeStep counter g n next start memo input).1 :=
    resultMap_sound_memoizeStep
      (cfg := cfg) (input := input)
      (counter := counter) (g := g) (next := next)
      (n := n) (memo := memo) (start := start)
      h_memo.1
      (fun h_no_cache => h_compute memo h_memo start h_no_cache)
  exact h_sound end_ tree h_mem_step

set_option linter.unusedSectionVars false in
theorem lower_result_sound_memoizeStep_lift
  {cfg : @CFG α ν} {input : Array α}
  (counter : Counter ν)
  (g : ((t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg)) →
      (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  (next : ℕ → (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  {n : ν}
  (h_compute :
    ∀ memo : MemoData (tag cfg) List,
      memo_wellFormed cfg input memo →
      ∀ start : ℕ,
      ∀ _h_no_cache :
        (memo.getD n ⊥)[(Counter.toKey counter, start)]? = none,
        resultMap_sound cfg n
          ((((g (next (input.size - start + 1)) n).lower start)
            memo input).1)) :
    lower_result_sound cfg n
      (ParserM.lift (memoizeStep counter g n next)) input := by
  intro memo h_memo start end_ tree h_mem
  have h_mem_step :
      tree ∈ (memoizeStep counter g n next start memo input).1.getD end_ [] :=
    mem_lower_lift_exists_of_mem
      (tag := tag cfg) (β := α)
      (p := memoizeStep counter g n next)
      (memo := memo) (input := input)
      (start := start) (end_pos := end_) (x := tree) h_mem
  have h_sound :
      resultMap_sound cfg n
        (memoizeStep counter g n next start memo input).1 :=
    resultMap_sound_memoizeStep
      (cfg := cfg) (input := input)
      (counter := counter) (g := g) (next := next)
      (n := n) (memo := memo) (start := start)
      h_memo.1
      (fun h_no_cache => h_compute memo h_memo start h_no_cache)
  exact h_sound end_ tree h_mem_step

set_option linter.unusedSectionVars false in
theorem lower_result_bounded_memoizeStep_lift
  {cfg : @CFG α ν} {input : Array α}
  (counter : Counter ν)
  (g : ((t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg)) →
      (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  (next : ℕ → (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  {n : ν}
  (h_compute :
    ∀ memo : MemoData (tag cfg) List,
      memo_wellFormed cfg input memo →
      ∀ start : ℕ,
      ∀ _h_no_cache :
        (memo.getD n ⊥)[(Counter.toKey counter, start)]? = none,
        resultMap_bounded cfg input start
          ((((g (next (input.size - start + 1)) n).lower start)
            memo input).1)) :
    lower_result_bounded cfg
      (ParserM.lift (memoizeStep counter g n next)) input := by
  intro memo h_memo start end_ h_start tree h_mem
  have h_mem_step :
      tree ∈ (memoizeStep counter g n next start memo input).1.getD end_ [] :=
    mem_lower_lift_exists_of_mem
      (tag := tag cfg) (β := α)
      (p := memoizeStep counter g n next)
      (memo := memo) (input := input)
      (start := start) (end_pos := end_) (x := tree) h_mem
  have h_bounded :
      resultMap_bounded cfg input start
        (memoizeStep counter g n next start memo input).1 :=
    resultMap_bounded_memoizeStep
      (cfg := cfg) (input := input)
      (counter := counter) (g := g) (next := next)
      (n := n) (memo := memo) (start := start)
      h_memo.2
      (fun h_no_cache => h_compute memo h_memo start h_no_cache)
  exact h_bounded end_ h_start tree h_mem_step

set_option linter.unusedSectionVars false in
theorem lower_memo_wellFormed_memoizeStep_lift
  {cfg : @CFG α ν} {input : Array α}
  (counter : Counter ν)
  (g : ((t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg)) →
      (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  (next : ℕ → (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  {n : ν}
  (h_compute :
    ∀ memo : MemoData (tag cfg) List,
      memo_wellFormed cfg input memo →
      ∀ start : ℕ,
      ∀ _h_no_cache :
        (memo.getD n ⊥)[(Counter.toKey counter, start)]? = none,
        memo_wellFormed cfg input
            ((((g (next (input.size - start + 1)) n).lower start)
              memo input).2.val) ∧
          resultMap_sound cfg n
            ((((g (next (input.size - start + 1)) n).lower start)
              memo input).1) ∧
          resultMap_bounded cfg input start
            ((((g (next (input.size - start + 1)) n).lower start)
              memo input).1)) :
    lower_memo_wellFormed cfg
      (ParserM.lift (memoizeStep counter g n next)) input := by
  exact lower_lift_memo_wellFormed
    (cfg := cfg) (input := input)
    (p := memoizeStep counter g n next)
    (by
      intro start memo h_memo
      exact memo_wellFormed_memoizeStep
        (cfg := cfg) (input := input)
        (counter := counter) (g := g) (next := next)
        (n := n) (memo := memo) (start := start)
        h_memo
        (fun h_no_cache => h_compute memo h_memo start h_no_cache))

omit [BEq α] [DecidableEq α] [DecidableEq ν] in
lemma mem_zip_index_pair
  {xs : List α} {ys : List β}
  (h_len : xs.length = ys.length)
  {x : α} {y : β}
  (h_mem : (x, y) ∈ xs.zip ys)
  : ∃ i : Fin xs.length, xs[i] = x ∧ ys[i] = y := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp h_mem
  have h_len_zip : (xs.zip ys).length = xs.length := by
    simp [List.length_zip, h_len]
  let i' : Fin xs.length := ⟨i.1, by simpa [h_len_zip] using i.2⟩
  refine ⟨i', ?_, ?_⟩
  · have hfst := congrArg Prod.fst hi
    simpa [i', h_len_zip] using hfst
  · have hsnd := congrArg Prod.snd hi
    simpa [i', h_len_zip] using hsnd

-- Traversal and parser-constructor lemmas used by generated-parser soundness.
omit [BEq α] [Hashable ν] [Fintype ν] [DecidableEq α] [DecidableEq ν] in
lemma mem_zip_index
  {rule : List (Symbol α ν)} {subtrees : List (ParseTree (α := α) cfg)}
  (h_len : rule.length = subtrees.length)
  {a : ν} {n : ν} {rule' : { rule // rule ∈ cfg.rules n }} {children' : List (ParseTree cfg)}
  (h_mem : (Symbol.nonterm a, Node n rule' children') ∈ rule.zip subtrees)
  : ∃ i : Fin rule.length, rule[i] = Symbol.nonterm a ∧ subtrees[i] = Node n rule' children' := by
  exact mem_zip_index_pair h_len h_mem

omit [Fintype ν] in
lemma mem_bind_cons_map_exists_of_cons
  {cfg : @CFG α ν}
  {γ : Type u} [DecidableEq γ]
  {tail : List (ParserM (tag := tag cfg) α List γ)}
  {input : Array α} {split end_ : ℕ}
  {s : List γ} {result_head : γ} {result_tail : List γ}
  (h :
    result_head :: result_tail ∈
      s >>= fun a =>
        (runParser (tag := tag cfg)
          (List.cons a <$> List.traverse id tail) input split).1[end_]?.toList.flatten) :
    ∃ head_result,
      head_result ∈ s ∧
      result_head = head_result ∧
      result_tail ∈
        (runParser (tag := tag cfg) (List.traverse id tail) input split).1.getD end_ [] := by
  rw [List.bind_eq_flatMap] at h
  obtain ⟨head_result, h_head_mem, h_mapped⟩ := List.mem_flatMap.mp h
  have h_mapped_getD :
      result_head :: result_tail ∈
        (runParser (tag := tag cfg)
          (List.cons head_result <$> List.traverse id tail) input split).1.getD end_ [] := by
    exact mem_resultMap_getD_of_mem_getElem?_toList_flatten
      ((runParser (tag := tag cfg)
        (List.cons head_result <$> List.traverse id tail) input split).1)
      h_mapped
  obtain ⟨tail_result, h_tail_mem, h_eq⟩ := mem_runParser_map_exists_of_mem
    (tag := tag cfg) (β := α)
    (p := List.traverse id tail)
    (f := List.cons head_result)
    (input := input) (start := split) (end_pos := end_)
    (y := result_head :: result_tail) h_mapped_getD
  cases h_eq
  exact ⟨result_head, h_head_mem, rfl, h_tail_mem⟩

omit [Fintype ν] in
lemma not_mem_bind_cons_map_nil
  {cfg : @CFG α ν}
  {γ : Type u} [DecidableEq γ]
  {tail : List (ParserM (tag := tag cfg) α List γ)}
  {input : Array α} {split end_ : ℕ}
  {s : List γ}
  (h :
    ([] : List γ) ∈
      s >>= fun a =>
        (runParser (tag := tag cfg)
          (List.cons a <$> List.traverse id tail) input split).1[end_]?.toList.flatten) :
    False := by
  rw [List.bind_eq_flatMap] at h
  obtain ⟨head_result, _h_head_mem, h_mapped⟩ := List.mem_flatMap.mp h
  have h_mapped_getD :
      ([] : List γ) ∈
        (runParser (tag := tag cfg)
          (List.cons head_result <$> List.traverse id tail) input split).1.getD end_ [] := by
    exact mem_resultMap_getD_of_mem_getElem?_toList_flatten
      ((runParser (tag := tag cfg)
        (List.cons head_result <$> List.traverse id tail) input split).1)
      h_mapped
  obtain ⟨tail_result, _h_tail_mem, h_eq⟩ := mem_runParser_map_exists_of_mem
    (tag := tag cfg) (β := α)
    (p := List.traverse id tail)
    (f := List.cons head_result)
    (input := input) (start := split) (end_pos := end_)
    (y := ([] : List γ)) h_mapped_getD
  cases h_eq

omit [Fintype ν] in
lemma runParser_map_complete
  {cfg : @CFG α ν}
  {γ δ : Type u} [DecidableEq γ] [DecidableEq δ]
  {p : ParserM (tag := tag cfg) α List γ}
  {f : γ → δ}
  {input : Array α} {start end_ : ℕ} {x : γ}
  (h : x ∈ (runParser (tag := tag cfg) p input start).1.getD end_ [])
  : f x ∈ (runParser (tag := tag cfg) (f <$> p) input start).1.getD end_ [] := by
  exact mem_runParser_map_of_mem
    (tag := tag cfg) (β := α)
    p f input start end_ x h

omit [Fintype ν] in
lemma runParser_traverse_complete_cons
  {cfg : @CFG α ν}
  {γ : Type u} [DecidableEq γ]
  {head : ParserM (tag := tag cfg) α List γ}
  {tail : List (ParserM (tag := tag cfg) α List γ)}
  {input : Array α} {start split end_ : ℕ}
  {x : γ} {xs : List γ}
  (h_head : x ∈ (runParser (tag := tag cfg) head input start).1.getD split [])
  (h_tail : xs ∈ (runParser (tag := tag cfg) (List.traverse id tail) input split).1.getD end_ [])
  : x :: xs ∈
      (runParser (tag := tag cfg) (List.traverse id (head :: tail)) input start).1.getD end_ [] := by
  have h_tail_getD := h_tail
  rw [List.traverse, seq_eq_bind]
  simp
  rw [Std.HashMap.getD_eq_getD_getElem?] at h_head h_tail
  cases h_head_opt : (runParser (tag := tag cfg) head input start).1[split]? with
  | none =>
      simp [h_head_opt] at h_head
  | some headResults =>
      simp [h_head_opt] at h_head
      cases h_tail_opt :
          (runParser (tag := tag cfg) (List.traverse id tail) input split).1[end_]? with
      | none =>
          simp [h_tail_opt] at h_tail
      | some tailResults =>
          simp [h_tail_opt] at h_tail
          let resultMap := (runParser (tag := tag cfg)
            (head >>= fun a => List.cons a <$> List.traverse id tail)
            input start).1
          let r := resultMap.getD end_ []
          have h_bind :
              resultMap[end_]? = some r ∧ x :: xs ∈ r := by
            apply (mem_runParser_bind_iff_eq_bind_mem_runParser input head
              (fun (a : γ) => List.cons a <$> List.traverse id tail)
              (x := x :: xs) (r := r) (start := start) (end_pos := end_)).mpr
            refine ⟨split, headResults, h_head_opt, ?_⟩
            have h_mapped_getD :
                x :: xs ∈
                  (runParser (tag := tag cfg)
                    (List.cons x <$> List.traverse id tail)
                    input split).1.getD end_ [] := by
              exact mem_runParser_map_of_mem
                (tag := tag cfg) (β := α)
                (List.traverse id tail)
                (List.cons x) input split end_ xs h_tail_getD
            have h_mapped_mem :
                x :: xs ∈
                  (runParser (tag := tag cfg)
                    (List.cons x <$> List.traverse id tail)
                    input split).1[end_]?.toList.flatten := by
              exact mem_resultMap_getElem?_toList_flatten_of_mem_getD
                ((runParser (tag := tag cfg)
                  (List.cons x <$> List.traverse id tail) input split).1)
                h_mapped_getD
            rw [List.bind_eq_flatMap]
            exact List.mem_flatMap.mpr ⟨x, h_head, h_mapped_mem⟩
          simpa [resultMap, r] using h_bind.2

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
lemma valid_node_terminal_child
  {cfg : @CFG α ν}
  {n : ν} {rule : {rule // rule ∈ cfg.rules n}} {children : List (ParseTree cfg)}
  (h_valid : (Node (cfg := cfg) n rule children).Valid)
  (i : Fin rule.val.length)
  (j : Fin children.length)
  (h_j : j.1 = i.1)
  {a : α}
  (h_sym : rule.val[i] = Symbol.term a)
  : children[j] = Leaf (cfg := cfg) a := by
  have h_valid' :
      rule.val.length = children.length ∧
      ∀ pair (_h : pair ∈ List.zip rule.val children), match _h_pair : pair, _h with
        | ⟨Symbol.term a, Leaf b⟩, _ => a = b
        | ⟨Symbol.nonterm n, subtree@_h:(Node n' _ _)⟩, _ => n = n' ∧ subtree.Valid
        | _, _ => False := by
    simpa [ParseTree.Valid] using h_valid
  have h_pair_mem : (rule.val[i], children[j]) ∈ rule.val.zip children := by
    have h_zip_len : (rule.val.zip children).length = rule.val.length := by
      simp [List.length_zip, h_valid'.1]
    let k : Fin (rule.val.zip children).length := ⟨i.1, by simp [h_zip_len, i.2]⟩
    have h_mem : (rule.val.zip children)[k] ∈ rule.val.zip children := List.getElem_mem k.2
    simpa [k, h_j] using h_mem
  cases h_children : children[j] with
  | Leaf b =>
      have h_pair_mem' : (Symbol.term a, Leaf (cfg := cfg) b) ∈ rule.val.zip children := by
        simpa [h_sym, h_children] using h_pair_mem
      have h_child := h_valid'.2 (Symbol.term a, Leaf (cfg := cfg) b) h_pair_mem'
      have h_eq : a = b := by
        simp at h_child
        exact h_child
      simp [h_eq]
  | Node n' rule' children' =>
      have h_pair_mem' : (Symbol.term a, Node (cfg := cfg) n' rule' children') ∈ rule.val.zip children := by
        simpa [h_sym, h_children] using h_pair_mem
      have h_child := h_valid'.2 (Symbol.term a, Node (cfg := cfg) n' rule' children') h_pair_mem'
      have h_false : False := by
        simp at h_child
      exact False.elim h_false

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
lemma valid_node_nonterminal_child
  {cfg : @CFG α ν}
  {n : ν} {rule : {rule // rule ∈ cfg.rules n}} {children : List (ParseTree cfg)}
  (h_valid : (Node (cfg := cfg) n rule children).Valid)
  (i : Fin rule.val.length)
  (j : Fin children.length)
  (h_j : j.1 = i.1)
  {childN : ν}
  (h_sym : rule.val[i] = Symbol.nonterm childN)
  : ∃ rule' children',
      children[j] = Node (cfg := cfg) childN rule' children' ∧
      (Node (cfg := cfg) childN rule' children').Valid := by
  have h_valid' :
      rule.val.length = children.length ∧
      ∀ pair (_h : pair ∈ List.zip rule.val children), match _h_pair : pair, _h with
        | ⟨Symbol.term a, Leaf b⟩, _ => a = b
        | ⟨Symbol.nonterm n, subtree@_h:(Node n' _ _)⟩, _ => n = n' ∧ subtree.Valid
        | _, _ => False := by
    simpa [ParseTree.Valid] using h_valid
  have h_pair_mem : (rule.val[i], children[j]) ∈ rule.val.zip children := by
    have h_zip_len : (rule.val.zip children).length = rule.val.length := by
      simp [List.length_zip, h_valid'.1]
    let k : Fin (rule.val.zip children).length := ⟨i.1, by simp [h_zip_len, i.2]⟩
    have h_mem : (rule.val.zip children)[k] ∈ rule.val.zip children := List.getElem_mem k.2
    simpa [k, h_j] using h_mem
  cases h_children : children[j] with
  | Leaf b =>
      have h_pair_mem' : (Symbol.nonterm childN, Leaf (cfg := cfg) b) ∈ rule.val.zip children := by
        simpa [h_sym, h_children] using h_pair_mem
      have h_child := h_valid'.2 (Symbol.nonterm childN, Leaf (cfg := cfg) b) h_pair_mem'
      have h_false : False := by
        simp at h_child
      exact False.elim h_false
  | Node n' rule' children' =>
      have h_pair_mem' : (Symbol.nonterm childN, Node (cfg := cfg) n' rule' children') ∈ rule.val.zip children := by
        simpa [h_sym, h_children] using h_pair_mem
      have h_child := h_valid'.2 (Symbol.nonterm childN, Node (cfg := cfg) n' rule' children') h_pair_mem'
      have h_valid_root : childN = n' ∧ (Node (cfg := cfg) n' rule' children').Valid := by
        simp at h_child
        exact h_child
      obtain ⟨h_eq, h_subvalid⟩ := h_valid_root
      cases h_eq
      exact ⟨rule', children', rfl, h_subvalid⟩

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
lemma valid_node_child_node_valid_of_mem
  {cfg : @CFG α ν}
  {n childN : ν}
  {rule : {rule // rule ∈ cfg.rules n}}
  {children : List (ParseTree cfg)}
  {childRule : {rule // rule ∈ cfg.rules childN}}
  {grandchildren : List (ParseTree cfg)}
  (h_valid : (Node (cfg := cfg) n rule children).Valid)
  (h_mem : Node (cfg := cfg) childN childRule grandchildren ∈ children) :
    (Node (cfg := cfg) childN childRule grandchildren).Valid := by
  have h_valid' :
      rule.val.length = children.length ∧
      ∀ pair (_h : pair ∈ List.zip rule.val children), match _h_pair : pair, _h with
        | ⟨Symbol.term a, Leaf b⟩, _ => a = b
        | ⟨Symbol.nonterm n, subtree@_h:(Node n' _ _)⟩, _ => n = n' ∧ subtree.Valid
        | _, _ => False := by
    simpa [ParseTree.Valid] using h_valid
  obtain ⟨j, h_child_at⟩ := List.mem_iff_get.mp h_mem
  let i : Fin rule.val.length := ⟨j.1, by simp [h_valid'.1, j.2]⟩
  cases h_sym : rule.val[i] with
  | term a =>
      have h_leaf := valid_node_terminal_child
        (cfg := cfg) h_valid i j rfl h_sym
      have h_node : children[j] =
          Node (cfg := cfg) childN childRule grandchildren := h_child_at
      rw [h_leaf] at h_node
      simp at h_node
  | nonterm expected =>
      obtain ⟨actualRule, actualChildren, h_node, h_subvalid⟩ :=
        valid_node_nonterminal_child
          (cfg := cfg) h_valid i j rfl h_sym
      have h_node' : Node (cfg := cfg) expected actualRule actualChildren =
          Node (cfg := cfg) childN childRule grandchildren := by
        exact h_node.symm.trans h_child_at
      cases h_node'
      exact h_subvalid

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
lemma list_sizeOf_replace_lt
  {δ : Type u} [SizeOf δ]
  {before after : List δ} {old new : δ}
  (h_lt : sizeOf new < sizeOf old) :
    sizeOf (before ++ new :: after) < sizeOf (before ++ old :: after) := by
  induction before with
  | nil =>
      simp
      omega
  | cons head tail ih =>
      simp
      omega

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
lemma node_sizeOf_replace_child_lt
  {cfg : @CFG α ν} {n : ν} {rule : {rule // rule ∈ cfg.rules n}}
  {before after : List (ParseTree cfg)} {old new : ParseTree cfg}
  (h_lt : sizeOf new < sizeOf old) :
    sizeOf (Node (cfg := cfg) n rule (before ++ new :: after)) <
      sizeOf (Node (cfg := cfg) n rule (before ++ old :: after)) := by
  simp only [Node.sizeOf_spec]
  have h_list := list_sizeOf_replace_lt
    (before := before) (after := after) (old := old) (new := new) h_lt
  omega

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
lemma list_split_at_of_length_cons
  {δ ε : Type u} {xs : List δ} {before : List ε} {child : ε}
  {after : List ε}
  (h_len : xs.length = (before ++ child :: after).length) :
    ∃ xsBefore x xsAfter,
      xs = xsBefore ++ x :: xsAfter ∧
      xsBefore.length = before.length := by
  induction before generalizing xs with
  | nil =>
      cases xs with
      | nil =>
          simp at h_len
      | cons x xsTail =>
          exact ⟨[], x, xsTail, by simp⟩
  | cons _ beforeTail ih =>
      cases xs with
      | nil =>
          simp at h_len
      | cons x xsTail =>
          have h_tail_len :
              xsTail.length = (beforeTail ++ child :: after).length := by
            simpa using h_len
          obtain ⟨xsBefore, split, xsAfter, h_split, h_before_len⟩ :=
            ih h_tail_len
          refine ⟨x :: xsBefore, split, xsAfter, ?_, ?_⟩
          · simp [h_split]
          · simp [h_before_len]

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
lemma valid_node_child_valid_of_split
  {cfg : @CFG α ν}
  {n : ν} {rule : {rule // rule ∈ cfg.rules n}}
  {before after : List (ParseTree cfg)} {child : ParseTree cfg}
  (h_valid : (Node (cfg := cfg) n rule (before ++ child :: after)).Valid) :
    child.Valid := by
  cases child with
  | Leaf a =>
      simp [ParseTree.Valid]
  | Node childN childRule grandchildren =>
      exact valid_node_child_node_valid_of_mem
        (cfg := cfg) h_valid (by simp)

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
abbrev forestLeaves {cfg : @CFG α ν} (children : List (ParseTree cfg)) : List α :=
  children.flatMap fun node => node.leaves

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
@[simp]
lemma forestLeaves_nil {cfg : @CFG α ν} :
    forestLeaves (cfg := cfg) [] = [] := by
  rfl

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
@[simp]
lemma forestLeaves_cons {cfg : @CFG α ν}
  (tree : ParseTree cfg) (children : List (ParseTree cfg)) :
    forestLeaves (cfg := cfg) (tree :: children) =
      tree.leaves ++ forestLeaves (cfg := cfg) children := by
  simp [forestLeaves]

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
@[simp]
lemma forestLeaves_append {cfg : @CFG α ν}
  (left right : List (ParseTree cfg)) :
    forestLeaves (cfg := cfg) (left ++ right) =
      forestLeaves (cfg := cfg) left ++ forestLeaves (cfg := cfg) right := by
  simp [forestLeaves, List.flatMap_append]

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
lemma input_eq_child_span_of_mem
  {cfg : @CFG α ν} {input : Array α}
  {children : List (ParseTree cfg)} {child : ParseTree cfg}
  {pre post : List α}
  (h_mem : child ∈ children)
  (h_input : input.toList = pre ++ forestLeaves (cfg := cfg) children ++ post) :
    ∃ before after : List (ParseTree cfg),
      children = before ++ child :: after ∧
      input.toList =
        (pre ++ forestLeaves (cfg := cfg) before) ++
          child.leaves ++
          (forestLeaves (cfg := cfg) after ++ post) := by
  obtain ⟨before, after, h_children⟩ := List.mem_iff_append.mp h_mem
  refine ⟨before, after, h_children, ?_⟩
  subst children
  simpa [forestLeaves, List.append_assoc] using h_input

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
lemma child_span_bounds_of_mem
  {cfg : @CFG α ν} {input : Array α}
  {children : List (ParseTree cfg)} {child : ParseTree cfg}
  {pre post : List α}
  (h_mem : child ∈ children)
  (h_input : input.toList = pre ++ forestLeaves (cfg := cfg) children ++ post) :
    ∃ childPre childPost : List α,
      input.toList = childPre ++ child.leaves ++ childPost ∧
      pre.length ≤ childPre.length ∧
      childPre.length + child.leaves.length ≤
        pre.length + (forestLeaves (cfg := cfg) children).length := by
  obtain ⟨before, after, h_children, h_child_input⟩ :=
    input_eq_child_span_of_mem (cfg := cfg) h_mem h_input
  refine ⟨pre ++ forestLeaves (cfg := cfg) before,
    forestLeaves (cfg := cfg) after ++ post, h_child_input, ?_, ?_⟩
  · simp
  · subst children
    simp [forestLeaves, List.length_append]
    omega

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
lemma list_middle_eq_drop_take
  {xs pre mid post : List α}
  (h : xs = pre ++ mid ++ post) :
    mid = (xs.drop pre.length).take mid.length := by
  subst xs
  simp

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
lemma list_middle_eq_of_same_span
  {xs pre₁ mid₁ post₁ pre₂ mid₂ post₂ : List α}
  (h₁ : xs = pre₁ ++ mid₁ ++ post₁)
  (h₂ : xs = pre₂ ++ mid₂ ++ post₂)
  (h_start : pre₁.length = pre₂.length)
  (h_end : pre₁.length + mid₁.length = pre₂.length + mid₂.length) :
    mid₁ = mid₂ := by
  have h_mid₁ := list_middle_eq_drop_take h₁
  have h_mid₂ := list_middle_eq_drop_take h₂
  have h_len : mid₁.length = mid₂.length := by
    omega
  rw [h_mid₁, h_mid₂, h_start, h_len]

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
@[simp]
lemma leaves_node_eq_forestLeaves {cfg : @CFG α ν}
  (n : ν) (rule : {rule // rule ∈ cfg.rules n})
  (children : List (ParseTree cfg)) :
    (Node (cfg := cfg) n rule children).leaves =
      forestLeaves (cfg := cfg) children := by
  simp [ParseTree.leaves, forestLeaves]

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
abbrev SpanVisit (ν : Type u) := ν × ℕ × ℕ

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
abbrev nodeSpanVisit {cfg : @CFG α ν}
  (n : ν) (start : ℕ) (tree : ParseTree cfg) : SpanVisit ν :=
  (n, start, start + tree.leaves.length)

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
@[simp]
theorem nodeSpanVisit_fst {cfg : @CFG α ν}
  (n : ν) (start : ℕ) (tree : ParseTree cfg) :
    (nodeSpanVisit n start tree).1 = n := by
  rfl

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
@[simp]
theorem nodeSpanVisit_start {cfg : @CFG α ν}
  (n : ν) (start : ℕ) (tree : ParseTree cfg) :
    (nodeSpanVisit n start tree).2.1 = start := by
  rfl

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
@[simp]
theorem nodeSpanVisit_end {cfg : @CFG α ν}
  (n : ν) (start : ℕ) (tree : ParseTree cfg) :
    (nodeSpanVisit n start tree).2.2 = start + tree.leaves.length := by
  rfl

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
theorem nodeSpanVisit_budget_default_eq
  {cfg : @CFG α ν} {input : Array α}
  (n : ν) (start : ℕ) (tree : ParseTree cfg) :
    input.size - (nodeSpanVisit n start tree).2.1 + 1 =
      input.size - start + 1 := by
  rfl

mutual
  inductive AdmissibleTreeWith
    (cfg : @CFG α ν) (input : Array α)
    : List (SpanVisit ν) → Counter ν → ParseTree cfg → ℕ → Prop where
    | leaf
        (seen : List (SpanVisit ν)) (counter : Counter ν)
        (a : α) (start : ℕ) :
        AdmissibleTreeWith cfg input seen counter (Leaf a) start
    | node
        (seen : List (SpanVisit ν)) (counter : Counter ν)
        {n : ν} {rule : {rule // rule ∈ cfg.rules n}}
        {children : List (ParseTree cfg)} {start : ℕ}
        (h_no_cycle :
          nodeSpanVisit n start (Node (cfg := cfg) n rule children) ∉ seen)
        (h_budget : counter[n]? ≠ some 0)
        (h_children :
          AdmissibleForestWith cfg input
            (nodeSpanVisit n start (Node (cfg := cfg) n rule children) :: seen)
            (counter.dec n (input.size - start + 1))
            children start) :
        AdmissibleTreeWith cfg input seen counter
          (Node n rule children) start

  inductive AdmissibleForestWith
    (cfg : @CFG α ν) (input : Array α)
    : List (SpanVisit ν) → Counter ν → List (ParseTree cfg) → ℕ → Prop where
    | nil
        (seen : List (SpanVisit ν)) (counter : Counter ν) (start : ℕ) :
        AdmissibleForestWith cfg input seen counter [] start
    | cons
        (seen : List (SpanVisit ν)) (counter : Counter ν)
        {child : ParseTree cfg} {children : List (ParseTree cfg)} {start : ℕ}
        (h_child : AdmissibleTreeWith cfg input seen counter child start)
        (h_tail :
          AdmissibleForestWith cfg input seen counter children
            (start + child.leaves.length)) :
        AdmissibleForestWith cfg input seen counter (child :: children) start
end

abbrev AdmissibleTree
  (cfg : @CFG α ν) (input : Array α) (tree : ParseTree cfg) (start : ℕ) : Prop :=
  AdmissibleTreeWith cfg input [] (Counter.empty : Counter ν) tree start

abbrev resultMap_complete (cfg : @CFG α ν) (input : Array α)
  (n : ν) (key : MemoKey ν) (start : ℕ)
  (resultMap : ResultMap List (ParseTree cfg)) :=
  ∀ {counter : Counter ν}
    {pre post : List α} {seen : List (SpanVisit ν)}
    {tree : ParseTree cfg},
    Counter.toKey counter = key →
    pre.length = start →
    tree.root = Symbol.nonterm n →
    AdmissibleTreeWith cfg input seen counter tree pre.length →
    tree.Valid →
    input.toList = pre ++ tree.leaves ++ post →
    tree ∈ resultMap.getD (pre.length + tree.leaves.length) []

abbrev memo_complete (cfg : @CFG α ν) (input : Array α)
  (memo : MemoData (tag cfg) List) :=
  ∀ {n : ν} {counter : Counter ν}
    {pre post : List α} {seen : List (SpanVisit ν)}
    {tree : ParseTree cfg}
    {resultMap : ResultMap List (ParseTree cfg)},
    (memo.getD n ⊥)[(Counter.toKey counter, pre.length)]? =
      some resultMap →
    tree.root = Symbol.nonterm n →
    AdmissibleTreeWith cfg input seen counter tree pre.length →
    tree.Valid →
    input.toList = pre ++ tree.leaves ++ post →
    tree ∈ resultMap.getD (pre.length + tree.leaves.length) []

omit [BEq α] [DecidableEq α] [Monad μ] [SemilatticeAlt μ] [Traversable μ]
  [Fintype ν] in
theorem memo_complete_empty (cfg : @CFG α ν) (input : Array α) :
    memo_complete cfg input (startState : MemoData (tag cfg) List) := by
  intro n counter pre post seen tree resultMap h_cache _h_root _h_adm _h_valid _h_input
  simp [startState, Bot.bot] at h_cache

omit [BEq α] [DecidableEq α] [Fintype ν] in
theorem resultMap_complete_of_memo_complete_getElem?
  {cfg : @CFG α ν} {input : Array α}
  {memo : MemoData (tag cfg) List}
  {n : ν} {key : MemoKey ν} {start : ℕ}
  {resultMap : ResultMap List (ParseTree cfg)}
  (h_memo : memo_complete cfg input memo)
  (h_cache : (memo.getD n ⊥)[(key, start)]? = some resultMap) :
    resultMap_complete cfg input n key start resultMap := by
  intro counter pre post seen tree h_key h_start h_root h_adm h_valid h_input
  exact h_memo
    (by simpa [h_key, h_start] using h_cache)
    h_root h_adm h_valid h_input

omit [BEq α] [DecidableEq α] [Fintype ν] in
theorem resultMap_complete_of_quot_eq
  {cfg : @CFG α ν} {input : Array α}
  {n : ν} {key : MemoKey ν} {start : ℕ}
  {left right : ResultMap List (ParseTree cfg)}
  (h_eq :
    Quotient.mk (Std.HashMap.isSetoid (s := List.memSetoid (ParseTree cfg))) left =
      Quotient.mk (Std.HashMap.isSetoid (s := List.memSetoid (ParseTree cfg))) right)
  (h_right : resultMap_complete cfg input n key start right) :
    resultMap_complete cfg input n key start left := by
  intro counter pre post seen tree h_key h_start h_root h_adm h_valid h_input
  have h_mem := h_right h_key h_start h_root h_adm h_valid h_input
  have h_equiv :
      Std.HashMap.EquivQuot
        (s := List.memSetoid (ParseTree cfg)) left right :=
    Quotient.exact h_eq
  have h_getD := Std.HashMap.EquivQuot.getD_eq
    (s := List.memSetoid (ParseTree cfg))
    (k := pre.length + tree.leaves.length) (fallback := []) h_equiv
  simp [List.memSetoid, Subset, List.Subset] at h_getD
  exact (@h_getD.2 tree h_mem)

set_option linter.unusedSectionVars false in
theorem resultMap_complete_unionSup_left
  {cfg : @CFG α ν} {input : Array α}
  {n : ν} {key : MemoKey ν} {start : ℕ}
  {left right : ResultMap List (ParseTree cfg)}
  (h_left : resultMap_complete cfg input n key start left) :
    resultMap_complete cfg input n key start (left.unionSup right) := by
  intro counter pre post seen tree h_key h_start h_root h_adm h_valid h_input
  exact resultMap_mem_unionSup_left
    (cfg := cfg) (left := left) (right := right)
    (end_ := pre.length + tree.leaves.length) (tree := tree)
    (h_left h_key h_start h_root h_adm h_valid h_input)

set_option linter.unusedSectionVars false in
theorem resultMap_complete_unionSup_right
  {cfg : @CFG α ν} {input : Array α}
  {n : ν} {key : MemoKey ν} {start : ℕ}
  {left right : ResultMap List (ParseTree cfg)}
  (h_right : resultMap_complete cfg input n key start right) :
    resultMap_complete cfg input n key start (left.unionSup right) := by
  intro counter pre post seen tree h_key h_start h_root h_adm h_valid h_input
  exact resultMap_mem_unionSup_right
    (cfg := cfg) (left := left) (right := right)
    (end_ := pre.length + tree.leaves.length) (tree := tree)
    (h_right h_key h_start h_root h_adm h_valid h_input)

abbrev positionMap_complete (cfg : @CFG α ν) (input : Array α)
  (n : ν)
  (positionMap :
    Std.HashMap (MemoEntryKey ν) (ResultMap List (ParseTree cfg))) :=
  ∀ {counter : Counter ν}
    {pre post : List α} {seen : List (SpanVisit ν)}
    {tree : ParseTree cfg},
    (Counter.toKey counter, pre.length) ∈ positionMap →
    tree.root = Symbol.nonterm n →
    AdmissibleTreeWith cfg input seen counter tree pre.length →
    tree.Valid →
    input.toList = pre ++ tree.leaves ++ post →
    tree ∈
      (positionMap.getD (Counter.toKey counter, pre.length)
        (Std.HashMap.emptyWithCapacity :
          ResultMap List (ParseTree cfg))).getD
        (pre.length + tree.leaves.length) []

set_option linter.unusedSectionVars false in
theorem positionMap_complete_empty
  (cfg : @CFG α ν) (input : Array α) (n : ν) :
    positionMap_complete cfg input n
      (Std.HashMap.emptyWithCapacity :
        Std.HashMap (MemoEntryKey ν) (ResultMap List (ParseTree cfg))) := by
  intro counter pre post seen tree h_entry _h_root _h_adm _h_valid _h_input
  simp at h_entry

set_option linter.unusedSectionVars false in
theorem positionMap_getElem?_eq_some_getD_of_mem
  {cfg : @CFG α ν}
  {positionMap :
    Std.HashMap (MemoEntryKey ν) (ResultMap List (ParseTree cfg))}
  {entry : MemoEntryKey ν}
  (h_entry : entry ∈ positionMap) :
    positionMap[entry]? =
      some (positionMap.getD entry
        (Std.HashMap.emptyWithCapacity :
          ResultMap List (ParseTree cfg))) := by
  have h_some : positionMap[entry]? = some positionMap[entry] := by
    simp [h_entry]
  simpa [Std.HashMap.getElem_eq_getD
      (m := positionMap) (a := entry)
      (fallback :=
        (Std.HashMap.emptyWithCapacity :
          ResultMap List (ParseTree cfg)))]
    using h_some

set_option linter.unusedSectionVars false in
theorem positionMap_complete_of_eq
  {cfg : @CFG α ν} {input : Array α} {n : ν}
  {left right :
    Std.HashMap (MemoEntryKey ν) (ResultMap List (ParseTree cfg))}
  (h_eq : left = right)
  (h_right : positionMap_complete cfg input n right) :
    positionMap_complete cfg input n left := by
  cases h_eq
  exact h_right

set_option linter.unusedSectionVars false in
theorem positionMap_complete_of_memo_complete
  {cfg : @CFG α ν} {input : Array α}
  {memo : MemoData (tag cfg) List}
  (h_memo : memo_complete cfg input memo)
  (n : ν) :
    positionMap_complete cfg input n
      (memo.getD n
        (Std.HashMap.emptyWithCapacity :
          Std.HashMap (MemoEntryKey ν) (ResultMap List (ParseTree cfg)))) := by
  intro counter pre post seen tree h_entry h_root h_adm h_valid h_input
  let positionMap :=
    memo.getD n
      (Std.HashMap.emptyWithCapacity :
        Std.HashMap (MemoEntryKey ν) (ResultMap List (ParseTree cfg)))
  let entry : MemoEntryKey ν := (Counter.toKey counter, pre.length)
  let emptyResultMap : ResultMap List (ParseTree cfg) :=
    Std.HashMap.emptyWithCapacity
  have h_cache :
      positionMap[entry]? =
        some (positionMap.getD entry emptyResultMap) := by
    simpa [positionMap, entry, emptyResultMap]
      using positionMap_getElem?_eq_some_getD_of_mem
        (cfg := cfg) (positionMap := positionMap) (entry := entry) h_entry
  exact h_memo
    (by simpa [positionMap, entry, emptyResultMap, Bot.bot] using h_cache)
    h_root h_adm h_valid h_input

set_option linter.unusedSectionVars false in
theorem positionMap_complete_sup
  {cfg : @CFG α ν} {input : Array α} {n : ν}
  {left right :
    Std.HashMap (MemoEntryKey ν) (ResultMap List (ParseTree cfg))}
  (h_left : positionMap_complete cfg input n left)
  (h_right : positionMap_complete cfg input n right) :
    positionMap_complete cfg input n (positionMapUnion cfg left right) := by
  intro counter pre post seen tree h_entry h_root h_adm h_valid h_input
  let entry : MemoEntryKey ν := (Counter.toKey counter, pre.length)
  let emptyResultMap : ResultMap List (ParseTree cfg) :=
    Std.HashMap.emptyWithCapacity
  let end_ := pre.length + tree.leaves.length
  have h_entry' : entry ∈ positionMapUnion cfg left right := by
    simpa [entry] using h_entry
  by_cases h_left_key : entry ∈ left
  · by_cases h_right_key : entry ∈ right
    · have h_left_mem :
          tree ∈ (left.getD entry emptyResultMap).getD end_ [] := by
        simpa [entry, emptyResultMap, end_] using
          (h_left (counter := counter) (pre := pre) (post := post)
            (seen := seen) (tree := tree) h_left_key
            h_root h_adm h_valid h_input)
      have h_union_mem :
          tree ∈
            ((left.getD entry emptyResultMap).unionSup
              (right.getD entry emptyResultMap)).getD end_ [] :=
        resultMap_mem_unionSup_left
          (cfg := cfg)
          (left := left.getD entry emptyResultMap)
          (right := right.getD entry emptyResultMap)
          (end_ := end_) (tree := tree) h_left_mem
      have h_union := Std.HashMap.unionSup_getD_both
        (s := Std.HashMap.isSetoid
          (s := List.memSetoid (ParseTree cfg)))
        (semi := Std.HashMap.instSemilatticeoidIsSetoid
          (s := List.memSetoid (ParseTree cfg))
          (semi := List.instSemilatticeAlt.instSemilatticeoidInstSetoid))
        (m₁ := left) (m₂ := right) h_left_key h_right_key
      have h_eq :
          Quotient.mk
              (Std.HashMap.isSetoid (s := List.memSetoid (ParseTree cfg)))
              ((positionMapUnion cfg left right).getD entry emptyResultMap) =
            Quotient.mk
              (Std.HashMap.isSetoid (s := List.memSetoid (ParseTree cfg)))
              ((left.getD entry emptyResultMap).unionSup
                (right.getD entry emptyResultMap)) := by
        simpa [positionMapUnion, emptyResultMap, Max.max,
          Std.HashMap.getElem_eq_getD
            (m := left) (a := entry) (fallback := emptyResultMap),
          Std.HashMap.getElem_eq_getD
            (m := right) (a := entry) (fallback := emptyResultMap)]
          using h_union
      have h_equiv :
          Std.HashMap.EquivQuot
            (s := List.memSetoid (ParseTree cfg))
            ((positionMapUnion cfg left right).getD entry emptyResultMap)
            ((left.getD entry emptyResultMap).unionSup
              (right.getD entry emptyResultMap)) :=
        Quotient.exact h_eq
      have h_getD := Std.HashMap.EquivQuot.getD_eq
        (s := List.memSetoid (ParseTree cfg))
        (k := end_) (fallback := []) h_equiv
      simp [List.memSetoid, Subset, List.Subset] at h_getD
      exact (@h_getD.2 tree h_union_mem)
    · have h_left_mem :
          tree ∈ (left.getD entry emptyResultMap).getD end_ [] := by
        simpa [entry, emptyResultMap, end_] using
          (h_left (counter := counter) (pre := pre) (post := post)
            (seen := seen) (tree := tree) h_left_key
            h_root h_adm h_valid h_input)
      have h_union := Std.HashMap.unionSup_getD_of_right_not_contains
        (s := Std.HashMap.isSetoid
          (s := List.memSetoid (ParseTree cfg)))
        (semi := Std.HashMap.instSemilatticeoidIsSetoid
          (s := List.memSetoid (ParseTree cfg))
          (semi := List.instSemilatticeAlt.instSemilatticeoidInstSetoid))
        (fallback := emptyResultMap) left right h_right_key
      have h_eq :
          Quotient.mk
              (Std.HashMap.isSetoid (s := List.memSetoid (ParseTree cfg)))
              ((positionMapUnion cfg left right).getD entry emptyResultMap) =
            Quotient.mk
              (Std.HashMap.isSetoid (s := List.memSetoid (ParseTree cfg)))
              (left.getD entry emptyResultMap) := by
        simpa [positionMapUnion, emptyResultMap] using h_union
      have h_equiv :
          Std.HashMap.EquivQuot
            (s := List.memSetoid (ParseTree cfg))
            ((positionMapUnion cfg left right).getD entry emptyResultMap)
            (left.getD entry emptyResultMap) :=
        Quotient.exact h_eq
      have h_getD := Std.HashMap.EquivQuot.getD_eq
        (s := List.memSetoid (ParseTree cfg))
        (k := end_) (fallback := []) h_equiv
      simp [List.memSetoid, Subset, List.Subset] at h_getD
      exact (@h_getD.2 tree h_left_mem)
  · by_cases h_right_key : entry ∈ right
    · have h_right_mem :
          tree ∈ (right.getD entry emptyResultMap).getD end_ [] := by
        simpa [entry, emptyResultMap, end_] using
          (h_right (counter := counter) (pre := pre) (post := post)
            (seen := seen) (tree := tree) h_right_key
            h_root h_adm h_valid h_input)
      have h_union := Std.HashMap.unionSup_getD_of_not_contains
        (s := Std.HashMap.isSetoid
          (s := List.memSetoid (ParseTree cfg)))
        (semi := Std.HashMap.instSemilatticeoidIsSetoid
          (s := List.memSetoid (ParseTree cfg))
          (semi := List.instSemilatticeAlt.instSemilatticeoidInstSetoid))
        (fallback := emptyResultMap) left right h_left_key
      have h_eq :
          Quotient.mk
              (Std.HashMap.isSetoid (s := List.memSetoid (ParseTree cfg)))
              ((positionMapUnion cfg left right).getD entry emptyResultMap) =
            Quotient.mk
              (Std.HashMap.isSetoid (s := List.memSetoid (ParseTree cfg)))
              (right.getD entry emptyResultMap) := by
        simpa [positionMapUnion, emptyResultMap] using h_union
      have h_equiv :
          Std.HashMap.EquivQuot
            (s := List.memSetoid (ParseTree cfg))
            ((positionMapUnion cfg left right).getD entry emptyResultMap)
            (right.getD entry emptyResultMap) :=
        Quotient.exact h_eq
      have h_getD := Std.HashMap.EquivQuot.getD_eq
        (s := List.memSetoid (ParseTree cfg))
        (k := end_) (fallback := []) h_equiv
      simp [List.memSetoid, Subset, List.Subset] at h_getD
      exact (@h_getD.2 tree h_right_mem)
    · have h_mem_or : entry ∈ left ∨ entry ∈ right := by
        have h := (Std.HashMap.mem_of_unionSup_mem
          (s := Std.HashMap.isSetoid
            (s := List.memSetoid (ParseTree cfg)))
          (semi := Std.HashMap.instSemilatticeoidIsSetoid
            (s := List.memSetoid (ParseTree cfg))
            (semi := List.instSemilatticeAlt.instSemilatticeoidInstSetoid))
          (m₁ := left) (m₂ := right)
          (k := entry)).mp (by simpa [positionMapUnion] using h_entry')
        exact h
      cases h_mem_or with
      | inl h_mem => exact False.elim (h_left_key h_mem)
      | inr h_mem => exact False.elim (h_right_key h_mem)

set_option linter.unusedSectionVars false in
theorem positionMap_complete_of_memo_complete_sup
  {cfg : @CFG α ν} {input : Array α}
  {left right : MemoData (tag cfg) List}
  (h_left : memo_complete cfg input left)
  (h_right : memo_complete cfg input right)
  (n : ν) :
    positionMap_complete cfg input n
      ((left ⊔ right).getD n
        (Std.HashMap.emptyWithCapacity :
          Std.HashMap (MemoEntryKey ν) (ResultMap List (ParseTree cfg)))) := by
  let emptyPositionMap :
      Std.HashMap (MemoEntryKey ν) (ResultMap List (ParseTree cfg)) :=
    Std.HashMap.emptyWithCapacity
  change positionMap_complete cfg input n
    ((Std.DHashMap.unionWith
      (fun _ => positionMapUnion cfg)
      (fun _ => emptyPositionMap)
      left right).getD n emptyPositionMap)
  by_cases h_left_n : n ∈ left
  · by_cases h_right_n : n ∈ right
    · rw [Std.DHashMap.getD_eq_getD_get?]
      rw [Std.DHashMap.unionWith_getElem_both
        (m₁ := left) (m₂ := right)
        (f := fun _ => positionMapUnion cfg)
        (z := fun _ => emptyPositionMap)
        h_left_n h_right_n]
      exact positionMap_complete_sup
        (cfg := cfg) (input := input) (n := n)
        (by
          intro counter pre post seen tree h_entry h_root h_adm h_valid h_input
          have h_pos :
              positionMap_complete cfg input n
                (left.getD n emptyPositionMap) :=
            positionMap_complete_of_memo_complete
              (cfg := cfg) (input := input) (memo := left) h_left n
          have h_eq :
              left.get n h_left_n = left.getD n emptyPositionMap :=
            Std.DHashMap.get_eq_getD
              (m := left) (a := n) (fallback := emptyPositionMap)
              (h := h_left_n)
          have h_entry_getD :
              (Counter.toKey counter, pre.length) ∈
                left.getD n emptyPositionMap := by
            simpa [← h_eq] using h_entry
          have h_mem :=
            h_pos (counter := counter) (pre := pre) (post := post)
              (seen := seen) (tree := tree)
              h_entry_getD h_root h_adm h_valid h_input
          simpa [← h_eq] using h_mem)
        (by
          intro counter pre post seen tree h_entry h_root h_adm h_valid h_input
          have h_pos :
              positionMap_complete cfg input n
                (right.getD n emptyPositionMap) :=
            positionMap_complete_of_memo_complete
              (cfg := cfg) (input := input) (memo := right) h_right n
          have h_eq :
              right.get n h_right_n = right.getD n emptyPositionMap :=
            Std.DHashMap.get_eq_getD
              (m := right) (a := n) (fallback := emptyPositionMap)
              (h := h_right_n)
          have h_entry_getD :
              (Counter.toKey counter, pre.length) ∈
                right.getD n emptyPositionMap := by
            simpa [← h_eq] using h_entry
          have h_mem :=
            h_pos (counter := counter) (pre := pre) (post := post)
              (seen := seen) (tree := tree)
              h_entry_getD h_root h_adm h_valid h_input
          simpa [← h_eq] using h_mem)
    · rw [Std.DHashMap.getD_eq_getD_get?]
      rw [Std.DHashMap.unionWith_getElem_not_contains_right
        (m₁ := left) (m₂ := right)
        (f := fun _ => positionMapUnion cfg)
        (z := fun _ => emptyPositionMap)
        h_right_n]
      rw [Std.DHashMap.get?_eq_some_get h_left_n]
      exact positionMap_complete_sup
        (cfg := cfg) (input := input) (n := n)
        (by
          intro counter pre post seen tree h_entry h_root h_adm h_valid h_input
          have h_pos :
              positionMap_complete cfg input n
                (left.getD n emptyPositionMap) :=
            positionMap_complete_of_memo_complete
              (cfg := cfg) (input := input) (memo := left) h_left n
          have h_eq :
              left.get n h_left_n = left.getD n emptyPositionMap :=
            Std.DHashMap.get_eq_getD
              (m := left) (a := n) (fallback := emptyPositionMap)
              (h := h_left_n)
          have h_entry_getD :
              (Counter.toKey counter, pre.length) ∈
                left.getD n emptyPositionMap := by
            simpa [← h_eq] using h_entry
          have h_mem :=
            h_pos (counter := counter) (pre := pre) (post := post)
              (seen := seen) (tree := tree)
              h_entry_getD h_root h_adm h_valid h_input
          simpa [← h_eq] using h_mem)
        (positionMap_complete_empty cfg input n)
  · by_cases h_right_n : n ∈ right
    · rw [Std.DHashMap.getD_eq_getD_get?]
      rw [Std.DHashMap.unionWith_getElem_not_contains
        (m₁ := left) (m₂ := right)
        (f := fun _ => positionMapUnion cfg)
        (z := fun _ => emptyPositionMap)
        h_left_n]
      rw [Std.DHashMap.get?_eq_some_get h_right_n]
      exact positionMap_complete_sup
        (cfg := cfg) (input := input) (n := n)
        (positionMap_complete_empty cfg input n)
        (by
          intro counter pre post seen tree h_entry h_root h_adm h_valid h_input
          have h_pos :
              positionMap_complete cfg input n
                (right.getD n emptyPositionMap) :=
            positionMap_complete_of_memo_complete
              (cfg := cfg) (input := input) (memo := right) h_right n
          have h_eq :
              right.get n h_right_n = right.getD n emptyPositionMap :=
            Std.DHashMap.get_eq_getD
              (m := right) (a := n) (fallback := emptyPositionMap)
              (h := h_right_n)
          have h_entry_getD :
              (Counter.toKey counter, pre.length) ∈
                right.getD n emptyPositionMap := by
            simpa [← h_eq] using h_entry
          have h_mem :=
            h_pos (counter := counter) (pre := pre) (post := post)
              (seen := seen) (tree := tree)
              h_entry_getD h_root h_adm h_valid h_input
          simpa [← h_eq] using h_mem)
    · have h_union_none :
          (Std.DHashMap.unionWith
            (fun _ => positionMapUnion cfg)
            (fun _ => emptyPositionMap)
            left right).get? n = none := by
        rw [Std.DHashMap.unionWith_getElem_not_contains
          (m₁ := left) (m₂ := right)
          (f := fun _ => positionMapUnion cfg)
          (z := fun _ => emptyPositionMap)
          h_left_n]
        simp [Std.DHashMap.get?_eq_none, h_right_n]
      rw [Std.DHashMap.getD_eq_getD_get?]
      rw [h_union_none]
      exact positionMap_complete_empty cfg input n

theorem memo_complete_sup
  {cfg : @CFG α ν} {input : Array α}
  {left right : MemoData (tag cfg) List}
  (h_left : memo_complete cfg input left)
  (h_right : memo_complete cfg input right) :
    memo_complete cfg input (left ⊔ right) := by
  intro n counter pre post seen tree resultMap h_cache h_root h_adm h_valid h_input
  let emptyPositionMap :
      Std.HashMap (MemoEntryKey ν) (ResultMap List (ParseTree cfg)) :=
    Std.HashMap.emptyWithCapacity
  let entry : MemoEntryKey ν := (Counter.toKey counter, pre.length)
  let positionMap := (left ⊔ right).getD n emptyPositionMap
  have h_cache_explicit : positionMap[entry]? = some resultMap := by
    simpa [positionMap, entry, emptyPositionMap, Bot.bot] using h_cache
  have h_entry : entry ∈ positionMap := by
    by_contra h_not_mem
    have h_none := Std.HashMap.getElem?_eq_none
      (m := positionMap) (a := entry) h_not_mem
    rw [h_cache_explicit] at h_none
    simp at h_none
  have h_getD_eq :
      positionMap.getD entry
          (Std.HashMap.emptyWithCapacity : ResultMap List (ParseTree cfg)) =
        resultMap := by
    rw [Std.HashMap.getD_eq_getD_getElem?]
    rw [h_cache_explicit]
    rfl
  have h_position :
      positionMap_complete cfg input n
        ((left ⊔ right).getD n emptyPositionMap) :=
    positionMap_complete_of_memo_complete_sup
      (cfg := cfg) (input := input)
      (left := left) (right := right) h_left h_right n
  have h_mem :=
    h_position (counter := counter) (pre := pre) (post := post)
      (seen := seen) (tree := tree)
      (by simpa [positionMap, entry, emptyPositionMap] using h_entry)
      h_root h_adm h_valid h_input
  rw [← h_getD_eq]
  simpa [positionMap, entry, emptyPositionMap] using h_mem

omit [BEq α] [DecidableEq α] [Fintype ν] in
theorem memo_complete_memoWithCachedResult
  {cfg : @CFG α ν} {input : Array α}
  {memo : MemoData (tag cfg) List}
  {n : ν} {key : MemoKey ν} {start : ℕ}
  {resultMap : ResultMap List (ParseTree cfg)}
  (h_memo : memo_complete cfg input memo)
  (h_result : resultMap_complete cfg input n key start resultMap) :
    memo_complete cfg input
      (memoWithCachedResult cfg memo n key start resultMap) := by
  intro n' counter pre post seen tree resultMap' h_cache h_root h_adm
    h_valid h_input
  by_cases h_same : n' = n ∧ (Counter.toKey counter, pre.length) = (key, start)
  · rcases h_same with ⟨h_n, h_entry⟩
    have h_key : Counter.toKey counter = key := congrArg Prod.fst h_entry
    have h_start : pre.length = start := congrArg Prod.snd h_entry
    cases h_n
    have h_cache_self :
        ((memoWithCachedResult cfg memo n key start resultMap).getD n ⊥)[(key, start)]? =
          some resultMap' := by
      simpa [h_key, h_start] using h_cache
    rw [memoWithCachedResult_getElem?_self
      (cfg := cfg) (memo := memo)
      (n := n) (key := key) (start := start)
      (resultMap := resultMap)] at h_cache_self
    cases h_cache_self
    exact h_result h_key h_start h_root h_adm h_valid h_input
  · have h_ne :
        n' ≠ n ∨ (Counter.toKey counter, pre.length) ≠ (key, start) := by
      by_cases h_n : n' = n
      · right
        intro h_entry
        exact h_same ⟨h_n, h_entry⟩
      · exact Or.inl h_n
    have h_cache_old :
        (memo.getD n' ⊥)[(Counter.toKey counter, pre.length)]? =
          some resultMap' := by
      rw [memoWithCachedResult_getElem?_ne
        (cfg := cfg) (memo := memo)
        (n := n) (n' := n')
        (key := key) (key' := Counter.toKey counter)
        (start := start) (start' := pre.length)
        (resultMap := resultMap) h_ne] at h_cache
      exact h_cache
    exact h_memo h_cache_old h_root h_adm h_valid h_input

theorem mem_lower_memoize_of_cache_complete
  {cfg : @CFG α ν} {input : Array α}
  (counter : Counter ν)
  (g : ((t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg)) →
      (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  {n : ν} {memo : MemoData (tag cfg) List}
  {pre post : List α} {seen : List (SpanVisit ν)}
  {tree : ParseTree cfg}
  {resultMap : ResultMap List (ParseTree cfg)}
  (h_counter : counter[n]? ≠ some 0)
  (h_complete : memo_complete cfg input memo)
  (h_cache :
    (memo.getD n ⊥)[(Counter.toKey counter, pre.length)]? =
      some resultMap)
  (h_root : tree.root = Symbol.nonterm n)
  (h_adm : AdmissibleTreeWith cfg input seen counter tree pre.length)
  (h_valid : tree.Valid)
  (h_input : input.toList = pre ++ tree.leaves ++ post) :
    tree ∈
      (((memoize counter g n).lower pre.length) memo input).1.getD
        (pre.length + tree.leaves.length) [] := by
  have h_cached :
      tree ∈ resultMap.getD (pre.length + tree.leaves.length) [] :=
    h_complete h_cache h_root h_adm h_valid h_input
  rw [memoize]
  simp only [h_counter, ↓reduceDIte]
  apply mem_lower_lift_of_mem
  exact mem_memoizeStep_of_cache_mem
    (tag := tag cfg) (β := α)
    (counter := counter) (g := g)
    (next := fun fuel => memoize (counter.dec n fuel) g)
    (t := n) (memo := memo) (input := input)
    (start := pre.length)
    (end_pos := pre.length + tree.leaves.length)
    (x := tree) (cached := resultMap)
    h_cache h_cached

theorem mem_lower_memoize_of_body_mem
  {cfg : @CFG α ν} {input : Array α}
  (counter : Counter ν)
  (g : ((t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg)) →
      (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  {n : ν} {memo : MemoData (tag cfg) List}
  {start end_ : ℕ} {tree : ParseTree cfg}
  (h_counter : counter[n]? ≠ some 0)
  (h_no_cache :
    (memo.getD n ⊥)[(Counter.toKey counter, start)]? = none)
  (h_body :
    tree ∈
      (((g (memoize (counter.dec n (input.size - start + 1)) g) n).lower start)
        memo input).1.getD end_ []) :
    tree ∈
      (((memoize counter g n).lower start) memo input).1.getD end_ [] := by
  rw [memoize]
  simp only [h_counter, ↓reduceDIte]
  apply mem_lower_lift_of_mem
  exact mem_memoizeStep_of_compute_mem
    (tag := tag cfg) (β := α)
    (counter := counter) (g := g)
    (next := fun fuel => memoize (counter.dec n fuel) g)
    (t := n) (memo := memo) (input := input)
    (start := start) (end_pos := end_)
    (x := tree) h_no_cache
    (by simpa using h_body)

theorem mem_lower_memoize_of_body_or_cache_complete
  {cfg : @CFG α ν} {input : Array α}
  (counter : Counter ν)
  (g : ((t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg)) →
      (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  {n : ν} {memo : MemoData (tag cfg) List}
  {pre post : List α} {seen : List (SpanVisit ν)}
  {tree : ParseTree cfg}
  (h_counter : counter[n]? ≠ some 0)
  (h_complete : memo_complete cfg input memo)
  (h_root : tree.root = Symbol.nonterm n)
  (h_adm : AdmissibleTreeWith cfg input seen counter tree pre.length)
  (h_valid : tree.Valid)
  (h_input : input.toList = pre ++ tree.leaves ++ post)
  (h_body :
    ∀ _h_no_cache :
      (memo.getD n ⊥)[(Counter.toKey counter, pre.length)]? = none,
      tree ∈
        (((g (memoize (counter.dec n (input.size - pre.length + 1)) g) n).lower
          pre.length) memo input).1.getD
          (pre.length + tree.leaves.length) []) :
    tree ∈
      (((memoize counter g n).lower pre.length) memo input).1.getD
        (pre.length + tree.leaves.length) [] := by
  cases h_lookup :
      (memo.getD n ⊥)[(Counter.toKey counter, pre.length)]? with
  | none =>
      exact mem_lower_memoize_of_body_mem
        (cfg := cfg) (input := input)
        counter g
        (n := n) (memo := memo)
        (start := pre.length)
        (end_ := pre.length + tree.leaves.length)
        (tree := tree)
        h_counter h_lookup (h_body h_lookup)
  | some resultMap =>
      exact mem_lower_memoize_of_cache_complete
        (cfg := cfg) (input := input)
        counter g
        (n := n) (memo := memo)
        (pre := pre) (post := post) (seen := seen)
        (tree := tree) (resultMap := resultMap)
        h_counter h_complete h_lookup h_root h_adm h_valid h_input

theorem memo_complete_memoizeStep_cache
  {cfg : @CFG α ν} {input : Array α}
  (counter : Counter ν)
  (g : ((t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg)) →
      (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  (next : ℕ → (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  {n : ν} {memo : MemoData (tag cfg) List} {start : ℕ}
  {cached : ResultMap List (ParseTree cfg)}
  (h_memo : memo_complete cfg input memo)
  (h_cache :
    (memo.getD n ⊥)[(Counter.toKey counter, start)]? = some cached) :
    memo_complete cfg input
      (memoizeStep counter g n next start memo input).2.val := by
  rw [memoizeStep_cache_snd_val_eq
    (counter := counter) (g := g) (next := next) (t := n)
    (memo := memo) (input := input) (start := start)
    (cached := cached) h_cache]
  exact h_memo

set_option linter.unusedSectionVars false in
theorem memo_complete_memoizeStep_compute
  {cfg : @CFG α ν} {input : Array α}
  (counter : Counter ν)
  (g : ((t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg)) →
      (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  (next : ℕ → (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  {n : ν} {memo : MemoData (tag cfg) List} {start : ℕ}
  (h_no_cache :
    (memo.getD n ⊥)[(Counter.toKey counter, start)]? = none)
  (h_body_memo :
    memo_complete cfg input
      ((((g (next (input.size - start + 1)) n).lower start)
        memo input).2.val))
  (h_body_result :
    resultMap_complete cfg input n (Counter.toKey counter) start
      ((((g (next (input.size - start + 1)) n).lower start)
        memo input).1)) :
    memo_complete cfg input
      (memoizeStep counter g n next start memo input).2.val := by
  let body :=
    (((g (next (input.size - start + 1)) n).lower start) memo input)
  have h_body_memo_body : memo_complete cfg input body.2.val := by
    dsimp [body]
    exact h_body_memo
  have h_body_result_body :
      resultMap_complete cfg input n (Counter.toKey counter) start body.1 := by
    dsimp [body]
    exact h_body_result
  have h_insert :
      memo_complete cfg input
        (body.2.val.insert n
          ((body.2.val.getD n ⊥).insert
            (Counter.toKey counter, start) body.1)) := by
    have h_cached :
        memo_complete cfg input
          (memoWithCachedResult cfg body.2.val n
            (Counter.toKey counter) start body.1) :=
      memo_complete_memoWithCachedResult
        (cfg := cfg) (input := input)
        (memo := body.2.val) (n := n)
        (key := Counter.toKey counter) (start := start)
        (resultMap := body.1)
        h_body_memo_body
        h_body_result_body
    intro n' counter' pre' post' seen' tree' resultMap' h_cache h_root
      h_adm h_valid h_input
    exact h_cached
      (by simpa [memoWithCachedResult, Bot.bot] using h_cache)
      h_root h_adm h_valid h_input
  have h_sup :
      memo_complete cfg input
        ((body.2.val.insert n
          ((body.2.val.getD n ⊥).insert
            (Counter.toKey counter, start) body.1)) ⊔ body.2.val) :=
    memo_complete_sup
      (cfg := cfg) (input := input)
      (left := body.2.val.insert n
        ((body.2.val.getD n ⊥).insert
          (Counter.toKey counter, start) body.1))
      (right := body.2.val)
      h_insert h_body_memo_body
  rw [memoizeStep_compute_snd_val_eq
    (counter := counter) (g := g) (next := next) (t := n)
    (memo := memo) (input := input) (start := start)
    h_no_cache]
  change memo_complete cfg input
    ((body.2.val.insert n
      ((body.2.val.getD n ⊥).insert
        (Counter.toKey counter, start) body.1)) ⊔ body.2.val)
  exact h_sup

set_option linter.unusedSectionVars false in
theorem memo_complete_memoizeStep
  {cfg : @CFG α ν} {input : Array α}
  (counter : Counter ν)
  (g : ((t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg)) →
      (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  (next : ℕ → (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  {n : ν} {memo : MemoData (tag cfg) List} {start : ℕ}
  (h_memo : memo_complete cfg input memo)
  (h_compute :
    ∀ _h_no_cache :
      (memo.getD n ⊥)[(Counter.toKey counter, start)]? = none,
      memo_complete cfg input
          ((((g (next (input.size - start + 1)) n).lower start)
            memo input).2.val) ∧
        resultMap_complete cfg input n (Counter.toKey counter) start
          ((((g (next (input.size - start + 1)) n).lower start)
            memo input).1)) :
    memo_complete cfg input
      (memoizeStep counter g n next start memo input).2.val := by
  cases h_lookup :
      (memo.getD n ⊥)[(Counter.toKey counter, start)]? with
  | none =>
      have h_body := h_compute h_lookup
      have h_complete :
          memo_complete cfg input
            (memoizeStep counter g n next start memo input).2.val :=
        memo_complete_memoizeStep_compute
        (cfg := cfg) (input := input)
        (counter := counter) (g := g) (next := next)
        (n := n) (memo := memo) (start := start)
        h_lookup h_body.1 h_body.2
      intro n' counter' pre' post' seen' tree' resultMap' h_cache h_root
        h_adm h_valid h_input
      exact h_complete h_cache h_root h_adm h_valid h_input
  | some cached =>
      have h_complete :
          memo_complete cfg input
            (memoizeStep counter g n next start memo input).2.val :=
        memo_complete_memoizeStep_cache
        (cfg := cfg) (input := input)
        (counter := counter) (g := g) (next := next)
        (n := n) (memo := memo) (start := start)
        (cached := cached) h_memo h_lookup
      intro n' counter' pre' post' seen' tree' resultMap' h_cache h_root
        h_adm h_valid h_input
      exact h_complete h_cache h_root h_adm h_valid h_input

omit [BEq α] [DecidableEq α] [Fintype ν] in
theorem admissible_node_inv
  {cfg : @CFG α ν} {input : Array α}
  {seen : List (SpanVisit ν)} {counter : Counter ν}
  {n : ν} {rule : {rule // rule ∈ cfg.rules n}}
  {children : List (ParseTree cfg)} {start : ℕ}
  (h :
    AdmissibleTreeWith cfg input seen counter
      (Node (cfg := cfg) n rule children) start) :
    nodeSpanVisit n start (Node (cfg := cfg) n rule children) ∉ seen ∧
    counter[n]? ≠ some 0 ∧
    AdmissibleForestWith cfg input
      (nodeSpanVisit n start (Node (cfg := cfg) n rule children) :: seen)
      (counter.dec n (input.size - start + 1))
      children start := by
  cases h with
  | node _ _ h_no_cycle h_budget h_children =>
      exact ⟨h_no_cycle, h_budget, h_children⟩

omit [BEq α] [DecidableEq α] [Fintype ν] in
theorem admissible_forest_cons_inv
  {cfg : @CFG α ν} {input : Array α}
  {seen : List (SpanVisit ν)} {counter : Counter ν}
  {child : ParseTree cfg} {children : List (ParseTree cfg)} {start : ℕ}
  (h :
    AdmissibleForestWith cfg input seen counter
      (child :: children) start) :
    AdmissibleTreeWith cfg input seen counter child start ∧
    AdmissibleForestWith cfg input seen counter children
      (start + child.leaves.length) := by
  cases h with
  | cons _ _ h_child h_tail =>
      exact ⟨h_child, h_tail⟩

omit [BEq α] [DecidableEq α] [Fintype ν] in
theorem counter_empty_getElem?_ne_zero (t : ν) :
    (Counter.empty : Counter ν)[t]? ≠ some 0 := by
  change (∅ : Std.HashMap ν ℕ)[t]? ≠ some 0
  rw [Std.HashMap.getElem?_empty]
  simp

omit [BEq α] [DecidableEq α] [Fintype ν] in
theorem counter_dec_self_getElem?
  (counter : Counter ν) (t : ν) (fuel : ℕ) :
    (counter.dec t fuel)[t]? = some (counter.getD t fuel - 1) := by
  change ((counter : Std.HashMap ν ℕ).insert t (counter.getD t fuel - 1))[t]? =
    some (counter.getD t fuel - 1)
  rw [Std.HashMap.getElem?_insert]
  simp

omit [BEq α] [DecidableEq α] [Fintype ν] in
theorem counter_dec_self_getD
  (counter : Counter ν) (t : ν) (fuel fallback : ℕ) :
    (counter.dec t fuel).getD t fallback = counter.getD t fuel - 1 := by
  rw [Std.HashMap.getD_eq_getD_getElem?]
  change (((counter : Std.HashMap ν ℕ).insert t
    (counter.getD t fuel - 1))[t]?).getD fallback =
      counter.getD t fuel - 1
  rw [Std.HashMap.getElem?_insert]
  simp

omit [BEq α] [DecidableEq α] [Fintype ν] in
theorem counter_dec_other_getElem?
  (counter : Counter ν) {t u : ν} (fuel : ℕ)
  (h_ne : t ≠ u) :
    (counter.dec t fuel)[u]? = counter[u]? := by
  change ((counter : Std.HashMap ν ℕ).insert t (counter.getD t fuel - 1))[u]? =
    counter[u]?
  rw [Std.HashMap.getElem?_insert]
  simp [h_ne]
  rfl

omit [BEq α] [DecidableEq α] [Fintype ν] in
theorem counter_dec_other_getElem?_ne_zero
  (counter : Counter ν) {t u : ν} (fuel : ℕ)
  (h_ne : t ≠ u)
  (h_nonzero : counter[u]? ≠ some 0) :
    (counter.dec t fuel)[u]? ≠ some 0 := by
  rw [counter_dec_other_getElem? (counter := counter) (t := t) (u := u)
    (fuel := fuel) h_ne]
  exact h_nonzero

omit [BEq α] [DecidableEq α] [Fintype ν] in
theorem counter_dec_self_getElem?_ne_zero_of_two_le
  (counter : Counter ν) (t : ν) (fuel : ℕ)
  (h : 2 ≤ counter.getD t fuel) :
    (counter.dec t fuel)[t]? ≠ some 0 := by
  rw [counter_dec_self_getElem?]
  intro h_zero
  simp at h_zero
  omega

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
def counterForSeen (input : Array α) : List (SpanVisit ν) → Counter ν
  | [] => Counter.empty
  | visit :: seen =>
      (counterForSeen input seen).dec visit.1 (input.size - visit.2.1 + 1)

omit [BEq α] [DecidableEq α] [Fintype ν] in
@[simp]
theorem counterForSeen_nil (input : Array α) :
    counterForSeen (ν := ν) input [] = (Counter.empty : Counter ν) := by
  rfl

omit [BEq α] [DecidableEq α] [Fintype ν] in
@[simp]
theorem counterForSeen_cons
  (input : Array α) (visit : SpanVisit ν) (seen : List (SpanVisit ν)) :
    counterForSeen input (visit :: seen) =
      (counterForSeen input seen).dec visit.1
        (input.size - visit.2.1 + 1) := by
  rfl

omit [BEq α] [DecidableEq α] [Fintype ν] in
theorem counterForSeen_cons_self_getElem?
  (input : Array α) (visit : SpanVisit ν) (seen : List (SpanVisit ν)) :
    (counterForSeen input (visit :: seen))[visit.1]? =
      some ((counterForSeen input seen).getD visit.1
        (input.size - visit.2.1 + 1) - 1) := by
  simp [counterForSeen, counter_dec_self_getElem?]

omit [BEq α] [DecidableEq α] [Fintype ν] in
theorem counterForSeen_cons_other_getElem?
  (input : Array α) (visit : SpanVisit ν) (seen : List (SpanVisit ν))
  {t : ν} (h_ne : visit.1 ≠ t) :
    (counterForSeen input (visit :: seen))[t]? =
      (counterForSeen input seen)[t]? := by
  simp [counterForSeen]
  exact counter_dec_other_getElem?
    (counter := counterForSeen input seen)
    (t := visit.1) (u := t)
    (fuel := input.size - visit.2.1 + 1) h_ne

omit [BEq α] [DecidableEq α] [Fintype ν] in
theorem counterForSeen_cons_other_getElem?_ne_zero
  (input : Array α) (visit : SpanVisit ν) (seen : List (SpanVisit ν))
  {t : ν} (h_ne : visit.1 ≠ t)
  (h_nonzero : (counterForSeen input seen)[t]? ≠ some 0) :
    (counterForSeen input (visit :: seen))[t]? ≠ some 0 := by
  rw [counterForSeen_cons_other_getElem? (input := input)
    (visit := visit) (seen := seen) (t := t) h_ne]
  exact h_nonzero

omit [BEq α] [DecidableEq α] [Fintype ν] in
theorem counterForSeen_cons_self_getElem?_ne_zero_of_two_le
  (input : Array α) (visit : SpanVisit ν) (seen : List (SpanVisit ν))
  (h :
    2 ≤ (counterForSeen input seen).getD visit.1
      (input.size - visit.2.1 + 1)) :
    (counterForSeen input (visit :: seen))[visit.1]? ≠ some 0 := by
  rw [counterForSeen_cons]
  exact counter_dec_self_getElem?_ne_zero_of_two_le
    (counter := counterForSeen input seen)
    (t := visit.1)
    (fuel := input.size - visit.2.1 + 1) h

omit [BEq α] [DecidableEq α] [Fintype ν] in
def spanVisitCount (t : ν) : List (SpanVisit ν) → ℕ
  | [] => 0
  | visit :: seen =>
      (if visit.1 = t then 1 else 0) + spanVisitCount t seen

omit [BEq α] [DecidableEq α] [Hashable ν] [Fintype ν] in
@[simp]
theorem spanVisitCount_nil (t : ν) :
    spanVisitCount t ([] : List (SpanVisit ν)) = 0 := by
  rfl

omit [BEq α] [DecidableEq α] [Hashable ν] [Fintype ν] in
@[simp]
theorem spanVisitCount_cons (t : ν) (visit : SpanVisit ν)
  (seen : List (SpanVisit ν)) :
    spanVisitCount t (visit :: seen) =
      (if visit.1 = t then 1 else 0) + spanVisitCount t seen := by
  rfl

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
def spanVisitInitialFuel (input : Array α) (t : ν) :
    List (SpanVisit ν) → Option ℕ
  | [] => none
  | visit :: seen =>
      match spanVisitInitialFuel input t seen with
      | some fuel => some fuel
      | none =>
          if visit.1 = t then
            some (input.size - visit.2.1 + 1)
          else
            none

omit [BEq α] [DecidableEq α] [Hashable ν] [Fintype ν] in
theorem spanVisitCount_eq_zero_of_initialFuel_none
  (input : Array α) (seen : List (SpanVisit ν)) (t : ν)
  (h_initial : spanVisitInitialFuel input t seen = none) :
    spanVisitCount t seen = 0 := by
  induction seen with
  | nil =>
      rfl
  | cons visit tail ih =>
      cases h_tail : spanVisitInitialFuel input t tail with
      | none =>
          by_cases h_tag : visit.1 = t
          · simp [spanVisitInitialFuel, h_tail, h_tag] at h_initial
          · have h_tail_count := ih h_tail
            simp [spanVisitCount, h_tag, h_tail_count]
      | some fuel =>
          simp [spanVisitInitialFuel, h_tail] at h_initial

omit [BEq α] [DecidableEq α] [Hashable ν] [Fintype ν] in
theorem spanVisitInitialFuel_some_mem
  (input : Array α) (seen : List (SpanVisit ν)) (t : ν) {fuel : ℕ}
  (h_initial : spanVisitInitialFuel input t seen = some fuel) :
    ∃ visit, visit ∈ seen ∧ visit.1 = t ∧
      fuel = input.size - visit.2.1 + 1 := by
  induction seen generalizing fuel with
  | nil =>
      simp [spanVisitInitialFuel] at h_initial
  | cons visit tail ih =>
      cases h_tail : spanVisitInitialFuel input t tail with
      | some tailFuel =>
          simp [spanVisitInitialFuel, h_tail] at h_initial
          subst fuel
          obtain ⟨witness, h_mem, h_tag, h_fuel⟩ := ih h_tail
          exact ⟨witness, by simp [h_mem], h_tag, h_fuel⟩
      | none =>
          by_cases h_tag : visit.1 = t
          · simp [spanVisitInitialFuel, h_tail, h_tag] at h_initial
            subst fuel
            exact ⟨visit, by simp, h_tag, rfl⟩
          · simp [spanVisitInitialFuel, h_tail, h_tag] at h_initial

omit [BEq α] [DecidableEq α] [Fintype ν] in
theorem counterForSeen_getElem?_eq_initialFuel_sub_count
  (input : Array α) (seen : List (SpanVisit ν)) (t : ν) :
    (counterForSeen input seen)[t]? =
      (spanVisitInitialFuel input t seen).map
        (fun fuel => fuel - spanVisitCount t seen) := by
  induction seen with
  | nil =>
      change (∅ : Std.HashMap ν ℕ)[t]? = none
      rw [Std.HashMap.getElem?_empty]
  | cons visit tail ih =>
      cases h_initial : spanVisitInitialFuel input t tail with
      | none =>
          by_cases h_tag : visit.1 = t
          · subst t
            have h_tail : (counterForSeen input tail)[visit.1]? = none := by
              simpa [h_initial] using ih
            have h_getD :
                (counterForSeen input tail).getD visit.1
                    (input.size - visit.2.1 + 1) =
                  input.size - visit.2.1 + 1 := by
              rw [Std.HashMap.getD_eq_getD_getElem?]
              change ((counterForSeen input tail)[visit.1]?).getD
                (input.size - visit.2.1 + 1) =
                  input.size - visit.2.1 + 1
              rw [h_tail]
              rfl
            have h_count_tail :
                spanVisitCount visit.1 tail = 0 :=
              spanVisitCount_eq_zero_of_initialFuel_none
                (input := input) (seen := tail) (t := visit.1) h_initial
            rw [counterForSeen_cons_self_getElem?]
            simp [spanVisitInitialFuel, h_initial, spanVisitCount, h_getD,
              h_count_tail]
          · rw [counterForSeen_cons_other_getElem?
              (input := input) (visit := visit) (seen := tail)
              (t := t) h_tag]
            simpa [spanVisitInitialFuel, h_initial, h_tag, spanVisitCount] using ih
      | some fuel =>
          by_cases h_tag : visit.1 = t
          · subst t
            have h_tail :
                (counterForSeen input tail)[visit.1]? =
                  some (fuel - spanVisitCount visit.1 tail) := by
              simpa [h_initial] using ih
            have h_getD :
                (counterForSeen input tail).getD visit.1
                    (input.size - visit.2.1 + 1) =
                  fuel - spanVisitCount visit.1 tail := by
              rw [Std.HashMap.getD_eq_getD_getElem?]
              change ((counterForSeen input tail)[visit.1]?).getD
                (input.size - visit.2.1 + 1) =
                  fuel - spanVisitCount visit.1 tail
              rw [h_tail]
              rfl
            rw [counterForSeen_cons_self_getElem?]
            simp [spanVisitInitialFuel, h_initial, spanVisitCount, h_getD]
            omega
          · rw [counterForSeen_cons_other_getElem?
              (input := input) (visit := visit) (seen := tail)
              (t := t) h_tag]
            simpa [spanVisitInitialFuel, h_initial, h_tag, spanVisitCount] using ih

omit [BEq α] [DecidableEq α] [Fintype ν] in
theorem counterForSeen_getElem?_ne_zero_of_initialFuel_none
  (input : Array α) (seen : List (SpanVisit ν)) (t : ν)
  (h_initial : spanVisitInitialFuel input t seen = none) :
    (counterForSeen input seen)[t]? ≠ some 0 := by
  rw [counterForSeen_getElem?_eq_initialFuel_sub_count]
  simp [h_initial]

omit [BEq α] [DecidableEq α] [Fintype ν] in
theorem counterForSeen_getElem?_ne_zero_of_initialFuel_count_lt
  (input : Array α) (seen : List (SpanVisit ν)) (t : ν) {fuel : ℕ}
  (h_initial : spanVisitInitialFuel input t seen = some fuel)
  (h_count : spanVisitCount t seen < fuel) :
    (counterForSeen input seen)[t]? ≠ some 0 := by
  rw [counterForSeen_getElem?_eq_initialFuel_sub_count]
  simp [h_initial]
  omega

omit [BEq α] [DecidableEq α] [Fintype ν] in
theorem counter_getD_mono_default
  (counter : Counter ν) (t : ν) {fuel₁ fuel₂ : ℕ}
  (h_le : fuel₁ ≤ fuel₂) :
    counter.getD t fuel₁ ≤ counter.getD t fuel₂ := by
  repeat rw [Std.HashMap.getD_eq_getD_getElem?]
  change counter[t]?.getD fuel₁ ≤ counter[t]?.getD fuel₂
  cases counter[t]? with
  | none =>
      exact h_le
  | some value =>
      rfl

omit [BEq α] [DecidableEq α] [Fintype ν] in
theorem counter_getElem?_ne_zero_of_one_le_getD
  (counter : Counter ν) (t : ν) (fuel : ℕ)
  (h : 1 ≤ counter.getD t fuel) :
    counter[t]? ≠ some 0 := by
  rw [Std.HashMap.getD_eq_getD_getElem?] at h
  change 1 ≤ counter[t]?.getD fuel at h
  intro h_zero
  rw [h_zero] at h
  simp at h

omit [BEq α] [DecidableEq α] [Fintype ν] in
theorem counterForSeen_getD_lower_bound
  (input : Array α) (seen : List (SpanVisit ν)) (t : ν) (fuel : ℕ)
  (h_defaults :
    ∀ visit, visit ∈ seen → visit.1 = t →
      fuel ≤ input.size - visit.2.1 + 1) :
    fuel - spanVisitCount t seen ≤
      (counterForSeen input seen).getD t fuel := by
  induction seen with
  | nil =>
      simp [counterForSeen, Counter.empty]
  | cons visit tail ih =>
      by_cases h_tag : visit.1 = t
      · have h_default :
            fuel ≤ input.size - visit.2.1 + 1 :=
          h_defaults visit (by simp) h_tag
        have h_tail_defaults :
            ∀ visit', visit' ∈ tail → visit'.1 = t →
              fuel ≤ input.size - visit'.2.1 + 1 := by
          intro visit' h_mem h_eq
          exact h_defaults visit' (by simp [h_mem]) h_eq
        have h_tail_lb := ih h_tail_defaults
        have h_getD_mono :
            (counterForSeen input tail).getD t fuel ≤
              (counterForSeen input tail).getD t
                (input.size - visit.2.1 + 1) :=
          counter_getD_mono_default
            (counter := counterForSeen input tail) (t := t) h_default
        rw [counterForSeen_cons]
        rw [h_tag]
        rw [counter_dec_self_getD]
        simp [spanVisitCount, h_tag]
        omega
      · have h_tail_defaults :
            ∀ visit', visit' ∈ tail → visit'.1 = t →
              fuel ≤ input.size - visit'.2.1 + 1 := by
          intro visit' h_mem h_eq
          exact h_defaults visit' (by simp [h_mem]) h_eq
        have h_tail_lb := ih h_tail_defaults
        rw [counterForSeen_cons]
        have h_other := counter_dec_other_getElem?
          (counter := counterForSeen input tail)
          (t := visit.1) (u := t)
          (fuel := input.size - visit.2.1 + 1) h_tag
        rw [Std.HashMap.getD_eq_getD_getElem?]
        change fuel - spanVisitCount t (visit :: tail) ≤
          (((counterForSeen input tail).dec visit.1
            (input.size - visit.2.1 + 1))[t]?).getD fuel
        rw [h_other]
        simp [spanVisitCount, h_tag]
        rw [Std.HashMap.getD_eq_getD_getElem?] at h_tail_lb
        exact Nat.le_add_of_sub_le h_tail_lb

omit [BEq α] [DecidableEq α] [Fintype ν] in
theorem counterForSeen_getElem?_ne_zero_of_count_lt
  (input : Array α) (seen : List (SpanVisit ν)) (t : ν) (fuel : ℕ)
  (h_defaults :
    ∀ visit, visit ∈ seen → visit.1 = t →
      fuel ≤ input.size - visit.2.1 + 1)
  (h_count : spanVisitCount t seen < fuel) :
    (counterForSeen input seen)[t]? ≠ some 0 := by
  have h_lower :=
    counterForSeen_getD_lower_bound
      (input := input) (seen := seen) (t := t) (fuel := fuel)
      h_defaults
  have h_one : 1 ≤ (counterForSeen input seen).getD t fuel := by
    omega
  exact counter_getElem?_ne_zero_of_one_le_getD
    (counter := counterForSeen input seen) (t := t) (fuel := fuel) h_one

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
abbrev CounterMatchesSeen
  (input : Array α) (seen : List (SpanVisit ν)) (counter : Counter ν) : Prop :=
  counter = counterForSeen input seen

omit [BEq α] [DecidableEq α] [Fintype ν] in
theorem counterMatchesSeen_nil (input : Array α) :
    CounterMatchesSeen (ν := ν) input [] (Counter.empty : Counter ν) := by
  rfl

omit [BEq α] [DecidableEq α] [Fintype ν] in
theorem counterMatchesSeen_cons
  (input : Array α) (visit : SpanVisit ν) (seen : List (SpanVisit ν))
  {counter : Counter ν}
  (h_counter : CounterMatchesSeen input seen counter) :
    CounterMatchesSeen input (visit :: seen)
      (counter.dec visit.1 (input.size - visit.2.1 + 1)) := by
  subst counter
  rfl

omit [BEq α] [DecidableEq α] [Fintype ν] in
theorem counterMatchesSeen_cons_nodeSpan
  {cfg : @CFG α ν}
  (input : Array α) (seen : List (SpanVisit ν))
  {counter : Counter ν}
  (h_counter : CounterMatchesSeen input seen counter)
  (n : ν) (start : ℕ) (tree : ParseTree cfg) :
    CounterMatchesSeen input (nodeSpanVisit n start tree :: seen)
      (counter.dec n (input.size - start + 1)) := by
  subst counter
  rfl

omit [BEq α] [DecidableEq α] [Fintype ν] in
theorem counterMatchesSeen_getElem?_ne_zero
  (input : Array α) (seen : List (SpanVisit ν)) {counter : Counter ν}
  (h_counter : CounterMatchesSeen input seen counter)
  {t : ν}
  (h_nonzero : (counterForSeen input seen)[t]? ≠ some 0) :
    counter[t]? ≠ some 0 := by
  subst counter
  exact h_nonzero

omit [BEq α] [DecidableEq α] [Fintype ν] in
theorem counterMatchesSeen_getElem?_ne_zero_of_count_lt
  (input : Array α) (seen : List (SpanVisit ν)) {counter : Counter ν}
  (h_counter : CounterMatchesSeen input seen counter)
  (t : ν) (fuel : ℕ)
  (h_defaults :
    ∀ visit, visit ∈ seen → visit.1 = t →
      fuel ≤ input.size - visit.2.1 + 1)
  (h_count : spanVisitCount t seen < fuel) :
    counter[t]? ≠ some 0 := by
  subst counter
  exact counterForSeen_getElem?_ne_zero_of_count_lt
    (input := input) (seen := seen) (t := t) (fuel := fuel)
    h_defaults h_count

omit [BEq α] [DecidableEq α] [Fintype ν] in
theorem counterMatchesSeen_getElem?_ne_zero_of_initialFuel_none
  (input : Array α) (seen : List (SpanVisit ν)) {counter : Counter ν}
  (h_counter : CounterMatchesSeen input seen counter)
  (t : ν)
  (h_initial : spanVisitInitialFuel input t seen = none) :
    counter[t]? ≠ some 0 := by
  subst counter
  exact counterForSeen_getElem?_ne_zero_of_initialFuel_none
    (input := input) (seen := seen) (t := t) h_initial

omit [BEq α] [DecidableEq α] [Fintype ν] in
theorem counterMatchesSeen_getElem?_ne_zero_of_initialFuel_count_lt
  (input : Array α) (seen : List (SpanVisit ν)) {counter : Counter ν}
  (h_counter : CounterMatchesSeen input seen counter)
  (t : ν) {fuel : ℕ}
  (h_initial : spanVisitInitialFuel input t seen = some fuel)
  (h_count : spanVisitCount t seen < fuel) :
    counter[t]? ≠ some 0 := by
  subst counter
  exact counterForSeen_getElem?_ne_zero_of_initialFuel_count_lt
    (input := input) (seen := seen) (t := t)
    h_initial h_count

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
lemma array_getElem?_of_toList_eq_append_singleton
  {input : Array α} {pre post : List α} {a : α}
  (h_input : input.toList = pre ++ a :: post) :
    input[pre.length]? = some a := by
  have h_list : input.toList[pre.length]? = some a := by
    rw [h_input]
    simp
  simpa using h_list

omit [Fintype ν] in
lemma terminal'_complete
  {cfg : @CFG α ν}
  {a : α} {input : Array α} {start : ℕ}
  (h : input[start]? = some a)
  : Leaf (cfg := cfg) a ∈
      (runParser (tag := tag cfg) (Leaf <$> terminal' (tag := tag cfg) a) input start).1.getD (start + 1) [] := by
  have h_terminal : a ∈
      (runParser (tag := tag cfg) (terminal' (tag := tag cfg) (μ := List) a) input start).1.getD (start + 1) [] := by
    exact (mem_runParser_terminal_iff (tag := tag cfg)
      (a := a) (x := a) (input := input) (start := start) (end_pos := start + 1)).mpr
      ⟨h.symm, rfl, rfl⟩
  exact mem_runParser_map_of_mem
    (tag := tag cfg) (β := α)
    (terminal' (tag := tag cfg) (μ := List) a)
    Leaf input start (start + 1) a h_terminal

omit [Fintype ν] in
inductive TraverseCompleteWitness
  (cfg : @CFG α ν)
  {γ : Type u} [DecidableEq γ]
  (input : Array α)
  : List (ParserM (tag := tag cfg) α List γ) → ℕ → List γ → ℕ → Prop where
  | nil (pos : ℕ) :
      TraverseCompleteWitness cfg input [] pos [] pos
  | cons
      {head : ParserM (tag := tag cfg) α List γ}
      {tail : List (ParserM (tag := tag cfg) α List γ)}
      {start split end_ : ℕ} {x : γ} {xs : List γ}
      (h_head : x ∈ (runParser (tag := tag cfg) head input start).1.getD split [])
      (h_tail : TraverseCompleteWitness cfg input tail split xs end_) :
      TraverseCompleteWitness cfg input (head :: tail) start (x :: xs) end_

omit [Fintype ν] in
inductive GeneratedChildWitness
  (cfg : @CFG α ν)
  (recur : ν → ParserM (tag := tag cfg) α List (ParseTree cfg))
  (input : Array α)
  : List (Symbol α ν) → List (ParseTree cfg) → ℕ → ℕ → Prop where
  | nil (pos : ℕ) :
      GeneratedChildWitness cfg recur input [] [] pos pos
  | term
      {a : α} {rest : List (Symbol α ν)} {children : List (ParseTree cfg)}
      {start end_ : ℕ}
      (h_term : input[start]? = some a)
      (h_tail : GeneratedChildWitness cfg recur input rest children (start + 1) end_) :
      GeneratedChildWitness cfg recur input
        (Symbol.term a :: rest) (Leaf (cfg := cfg) a :: children) start end_
  | nonterm
      {n : ν} {tree : ParseTree cfg}
      {rest : List (Symbol α ν)} {children : List (ParseTree cfg)}
      {start split end_ : ℕ}
      (h_child : tree ∈ (runParser (tag := tag cfg) (recur n) input start).1.getD split [])
      (h_tail : GeneratedChildWitness cfg recur input rest children split end_) :
      GeneratedChildWitness cfg recur input
        (Symbol.nonterm n :: rest) (tree :: children) start end_

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
abbrev validChildPair {cfg : @CFG α ν} :
    Symbol α ν × ParseTree cfg → Prop
  | (Symbol.term a, Leaf b) => a = b
  | (Symbol.nonterm n, subtree@(Node n' _ _)) => n = n' ∧ subtree.Valid
  | _ => False

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
lemma valid_node_of_validChildPairs
  {cfg : @CFG α ν}
  {n : ν} {rule : {rule // rule ∈ cfg.rules n}}
  {children : List (ParseTree cfg)}
  (h_len : rule.val.length = children.length)
  (h_pairs :
    ∀ pair, pair ∈ List.zip rule.val children →
      validChildPair (cfg := cfg) pair) :
    (Node (cfg := cfg) n rule children).Valid := by
  simp [ParseTree.Valid]
  constructor
  · exact h_len
  · intro sym subtree h_mem
    have h_pair := h_pairs (sym, subtree) h_mem
    cases sym <;> cases subtree <;>
      simp [validChildPair] at h_pair ⊢ <;> assumption

omit [Fintype ν] in
theorem lower_rule_branch_sound_of_traverse_pairs
  {cfg : @CFG α ν}
  {n : ν} {rule : {rule // rule ∈ cfg.rules n}}
  {mkParser : Symbol α ν → ParserM (tag := tag cfg) α List (ParseTree cfg)}
  {input : Array α}
  (h_children :
    ∀ memo : MemoData (tag cfg) List,
      memo_wellFormed cfg input memo →
      ∀ start end_ : ℕ,
      start ≤ end_ ∧ end_ ≤ input.size →
      ∀ subtrees,
        subtrees ∈
          (((List.traverse id (rule.val.map mkParser)).lower start)
            memo input).1.getD end_ [] →
        rule.val.length = subtrees.length ∧
          ∀ pair, pair ∈ List.zip rule.val subtrees →
            validChildPair (cfg := cfg) pair) :
    lower_sound cfg n
      (Node n rule <$> List.traverse id (rule.val.map mkParser)) input := by
  apply lower_map_sound_of_forall
  intro memo h_memo start end_ h_bound subtrees h_subtrees
  obtain ⟨h_len, h_pairs⟩ :=
    h_children memo h_memo start end_ h_bound subtrees h_subtrees
  constructor
  · exact valid_node_of_validChildPairs
      (cfg := cfg) (n := n) (rule := rule)
      (children := subtrees) h_len h_pairs
  · simp [ParseTree.root]

omit [Fintype ν] in
theorem lower_rule_branch_result_sound_of_traverse_pairs
  {cfg : @CFG α ν}
  {n : ν} {rule : {rule // rule ∈ cfg.rules n}}
  {mkParser : Symbol α ν → ParserM (tag := tag cfg) α List (ParseTree cfg)}
  {input : Array α}
  (h_children :
    ∀ memo : MemoData (tag cfg) List,
      memo_wellFormed cfg input memo →
      ∀ start end_ : ℕ,
      ∀ subtrees,
        subtrees ∈
          (((List.traverse id (rule.val.map mkParser)).lower start)
            memo input).1.getD end_ [] →
        rule.val.length = subtrees.length ∧
          ∀ pair, pair ∈ List.zip rule.val subtrees →
            validChildPair (cfg := cfg) pair) :
    lower_result_sound cfg n
      (Node n rule <$> List.traverse id (rule.val.map mkParser)) input := by
  apply lower_map_result_sound_of_forall
  intro memo h_memo start end_ subtrees h_subtrees
  obtain ⟨h_len, h_pairs⟩ :=
    h_children memo h_memo start end_ subtrees h_subtrees
  constructor
  · exact valid_node_of_validChildPairs
      (cfg := cfg) (n := n) (rule := rule)
      (children := subtrees) h_len h_pairs
  · simp [ParseTree.root]

omit [Fintype ν] in
theorem lower_rule_branch_result_bounded_of_traverse
  {cfg : @CFG α ν}
  {n : ν} {rule : {rule // rule ∈ cfg.rules n}}
  {mkParser : Symbol α ν → ParserM (tag := tag cfg) α List (ParseTree cfg)}
  {input : Array α}
  (h_children :
    ∀ memo : MemoData (tag cfg) List,
      memo_wellFormed cfg input memo →
      ∀ start end_ : ℕ,
      start ≤ input.size →
      ∀ subtrees,
        subtrees ∈
          (((List.traverse id (rule.val.map mkParser)).lower start)
            memo input).1.getD end_ [] →
        start ≤ end_ ∧ end_ ≤ input.size) :
    lower_result_bounded cfg
      (Node n rule <$> List.traverse id (rule.val.map mkParser)) input := by
  apply lower_map_result_bounded_of_forall
  intro memo h_memo start end_ h_start subtrees h_subtrees
  exact h_children memo h_memo start end_ h_start subtrees h_subtrees

omit [Fintype ν] in
theorem lower_rule_branch_memo_wellFormed_of_traverse
  {cfg : @CFG α ν}
  {n : ν} {rule : {rule // rule ∈ cfg.rules n}}
  {mkParser : Symbol α ν → ParserM (tag := tag cfg) α List (ParseTree cfg)}
  {input : Array α}
  (h_children :
    lower_memo_wellFormed cfg
      (List.traverse id (rule.val.map mkParser)) input) :
    lower_memo_wellFormed cfg
      (Node n rule <$> List.traverse id (rule.val.map mkParser)) input := by
  exact lower_map_memo_wellFormed
    (cfg := cfg)
    (p := List.traverse id (rule.val.map mkParser))
    (f := Node n rule)
    h_children

omit [Fintype ν] in
theorem lower_memo_wellFormed_traverse_cons_terminal
  {cfg : @CFG α ν}
  {a : α}
  {tail : List (ParserM (tag := tag cfg) α List (ParseTree cfg))}
  {input : Array α}
  (h_tail :
    lower_memo_wellFormed cfg (List.traverse id tail) input) :
    lower_memo_wellFormed cfg
      (List.traverse id
        ((Leaf (cfg := cfg) <$> terminal' (tag := tag cfg) a) :: tail))
      input := by
  rw [List.traverse, seq_eq_bind]
  simp
  change lower_memo_wellFormed cfg
    (ParserM.Bind (terminalPrimitive (tag := tag cfg) a)
      (fun x =>
        (ParserM.Return (tag := tag cfg) (β := α) (μ := List)
          (Leaf (cfg := cfg) x) >>= fun tree =>
            List.cons tree <$> List.traverse id tail)))
    input
  exact lower_bind_constructor_memo_wellFormed
    (cfg := cfg) (input := input)
    (p := terminalPrimitive (tag := tag cfg) a)
    (k := fun x =>
      (ParserM.Return (tag := tag cfg) (β := α) (μ := List)
        (Leaf (cfg := cfg) x) >>= fun tree =>
          List.cons tree <$> List.traverse id tail))
    (by
      intro start memo h_memo
      rw [terminalPrimitive_snd_val_eq
        (tag := tag cfg) (a := a)
        (input := input) (start := start) (memo := memo)]
      exact h_memo)
    (by
      intro x
      change lower_memo_wellFormed cfg
        (List.cons (Leaf (cfg := cfg) x) <$> List.traverse id tail) input
      exact lower_map_memo_wellFormed
        (cfg := cfg)
        (p := List.traverse id tail)
        (f := List.cons (Leaf (cfg := cfg) x))
        h_tail)

omit [Fintype ν] in
theorem lower_memo_wellFormed_traverse_cons_lift
  {cfg : @CFG α ν}
  {p : Parser (tag := tag cfg) α List (ParseTree cfg)}
  {tail : List (ParserM (tag := tag cfg) α List (ParseTree cfg))}
  {input : Array α}
  (h_p :
    ∀ start,
      ∀ memo : MemoData (tag cfg) List,
        memo_wellFormed cfg input memo →
        memo_wellFormed cfg input (((p start) memo input).2.val))
  (h_tail :
    lower_memo_wellFormed cfg (List.traverse id tail) input) :
    lower_memo_wellFormed cfg
      (List.traverse id ((ParserM.lift p) :: tail)) input := by
  rw [List.traverse, seq_eq_bind]
  simp
  change lower_memo_wellFormed cfg
    (ParserM.Bind p (fun x => List.cons x <$> List.traverse id tail)) input
  exact lower_bind_constructor_memo_wellFormed
    (cfg := cfg) (input := input)
    (p := p)
    (k := fun x => List.cons x <$> List.traverse id tail)
    h_p
    (by
      intro x
      exact lower_map_memo_wellFormed
        (cfg := cfg)
        (p := List.traverse id tail)
        (f := List.cons x)
        h_tail)

omit [Fintype ν] in
theorem lower_memo_wellFormed_traverse_cons_failure
  {cfg : @CFG α ν}
  {tail : List (ParserM (tag := tag cfg) α List (ParseTree cfg))}
  {input : Array α}
  (h_tail :
    lower_memo_wellFormed cfg (List.traverse id tail) input) :
    lower_memo_wellFormed cfg
      (List.traverse id
        ((⊥ : ParserM (tag := tag cfg) α List (ParseTree cfg)) :: tail))
      input := by
  simpa [Bot.bot] using
    lower_memo_wellFormed_traverse_cons_lift
      (cfg := cfg)
      (p := (Parser.failure :
        Parser (tag := tag cfg) α List (ParseTree cfg)))
      (tail := tail) (input := input)
      (by
        intro start memo h_memo
        simpa [Parser.failure, ReaderT.pure, Pure.pure] using h_memo)
      h_tail

set_option linter.unusedSectionVars false in
theorem lower_memo_wellFormed_traverse_cons_memoize
  {cfg : @CFG α ν}
  (counter : Counter ν)
  (g : ((t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg)) →
      (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  (n : ν)
  {tail : List (ParserM (tag := tag cfg) α List (ParseTree cfg))}
  {input : Array α}
  (h_step :
    ∀ start,
      ∀ memo : MemoData (tag cfg) List,
        memo_wellFormed cfg input memo →
        memo_wellFormed cfg input
          (((memoizeStep counter g n
            (fun fuel => memoize (counter.dec n fuel) g) start)
            memo input).2.val))
  (h_tail :
    lower_memo_wellFormed cfg (List.traverse id tail) input) :
    lower_memo_wellFormed cfg
      (List.traverse id ((memoize counter g n) :: tail)) input := by
  by_cases h_counter : counter[n]? = some 0
  · simpa [memoize, h_counter] using
      lower_memo_wellFormed_traverse_cons_failure
        (cfg := cfg) (tail := tail) (input := input) h_tail
  · simpa [memoize, h_counter] using
      lower_memo_wellFormed_traverse_cons_lift
        (cfg := cfg)
        (p := memoizeStep counter g n
          (fun fuel => memoize (counter.dec n fuel) g))
        (tail := tail) (input := input)
        h_step h_tail

set_option linter.unusedSectionVars false in
theorem lower_memo_wellFormed_generated_traverse_memoize
  {cfg : @CFG α ν}
  (counter : Counter ν)
  (g : ((t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg)) →
      (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  (rule : List (Symbol α ν)) (input : Array α)
  (h_step :
    ∀ n start,
      ∀ memo : MemoData (tag cfg) List,
        memo_wellFormed cfg input memo →
        memo_wellFormed cfg input
          (((memoizeStep counter g n
            (fun fuel => memoize (counter.dec n fuel) g) start)
            memo input).2.val)) :
    lower_memo_wellFormed cfg
      (List.traverse id
        (rule.map (generatedListSymbolParser cfg counter g)))
      input := by
  induction rule with
  | nil =>
      intro memo h_memo start
      simpa [List.traverse, lower_return_snd_val_eq] using h_memo
  | cons sym rest ih =>
      cases sym with
      | term a =>
          change lower_memo_wellFormed cfg
            (List.traverse id
              ((Leaf (cfg := cfg) <$> terminal' (tag := tag cfg) a) ::
                rest.map (generatedListSymbolParser cfg counter g)))
            input
          exact lower_memo_wellFormed_traverse_cons_terminal
            (cfg := cfg) (a := a)
            (tail := rest.map (generatedListSymbolParser cfg counter g))
            (input := input) ih
      | nonterm n =>
          change lower_memo_wellFormed cfg
            (List.traverse id
              ((memoize counter g n) ::
                rest.map (generatedListSymbolParser cfg counter g)))
            input
          exact lower_memo_wellFormed_traverse_cons_memoize
            (cfg := cfg) (counter := counter) (g := g) (n := n)
            (tail := rest.map (generatedListSymbolParser cfg counter g))
            (input := input)
            (h_step n) ih

set_option linter.unusedSectionVars false in
theorem lower_memo_wellFormed_generated_traverse_memoize_guarded
  {cfg : @CFG α ν}
  (counter : Counter ν)
  (g : ((t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg)) →
      (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  (rule : List (Symbol α ν)) (input : Array α)
  (h_step :
    ∀ n,
      counter[n]? ≠ some 0 →
      ∀ start,
      ∀ memo : MemoData (tag cfg) List,
        memo_wellFormed cfg input memo →
        memo_wellFormed cfg input
          (((memoizeStep counter g n
            (fun fuel => memoize (counter.dec n fuel) g) start)
            memo input).2.val)) :
    lower_memo_wellFormed cfg
      (List.traverse id
        (rule.map (generatedListSymbolParser cfg counter g)))
      input := by
  induction rule with
  | nil =>
      intro memo h_memo start
      simpa [List.traverse, lower_return_snd_val_eq] using h_memo
  | cons sym rest ih =>
      cases sym with
      | term a =>
          change lower_memo_wellFormed cfg
            (List.traverse id
              ((Leaf (cfg := cfg) <$> terminal' (tag := tag cfg) a) ::
                rest.map (generatedListSymbolParser cfg counter g)))
            input
          exact lower_memo_wellFormed_traverse_cons_terminal
            (cfg := cfg) (a := a)
            (tail := rest.map (generatedListSymbolParser cfg counter g))
            (input := input) ih
      | nonterm n =>
          by_cases h_counter : counter[n]? = some 0
          · change lower_memo_wellFormed cfg
              (List.traverse id
                ((memoize counter g n) ::
                  rest.map (generatedListSymbolParser cfg counter g)))
              input
            simpa [memoize, h_counter] using
              lower_memo_wellFormed_traverse_cons_failure
                (cfg := cfg)
                (tail := rest.map (generatedListSymbolParser cfg counter g))
                (input := input) ih
          · change lower_memo_wellFormed cfg
              (List.traverse id
                ((memoize counter g n) ::
                  rest.map (generatedListSymbolParser cfg counter g)))
              input
            simpa [memoize, h_counter] using
              lower_memo_wellFormed_traverse_cons_lift
                (cfg := cfg)
                (p := memoizeStep counter g n
                  (fun fuel => memoize (counter.dec n fuel) g))
                (tail := rest.map (generatedListSymbolParser cfg counter g))
                (input := input)
                (h_step n h_counter) ih

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
lemma validChildPair_replace_same_root
  {cfg : @CFG α ν}
  {sym : Symbol α ν} {old new : ParseTree cfg}
  (h_pair : validChildPair (cfg := cfg) (sym, old))
  (h_new_valid : new.Valid)
  (h_root : new.root = old.root) :
    validChildPair (cfg := cfg) (sym, new) := by
  cases sym with
  | term a =>
      cases old with
      | Leaf b =>
          have h_ab : a = b := by
            simpa [validChildPair] using h_pair
          cases new with
          | Leaf c =>
              have h_bc : c = b := by
                simpa [ParseTree.root] using h_root
              subst b
              subst c
              simp [validChildPair]
          | Node n rule children =>
              simp [ParseTree.root] at h_root
      | Node n rule children =>
          simp [validChildPair] at h_pair
  | nonterm expected =>
      cases old with
      | Leaf b =>
          simp [validChildPair] at h_pair
      | Node oldN oldRule oldChildren =>
          have h_old : expected = oldN ∧
              (Node (cfg := cfg) oldN oldRule oldChildren).Valid := by
            simpa [validChildPair] using h_pair
          obtain ⟨h_expected, _h_old_valid⟩ := h_old
          cases new with
          | Leaf c =>
              simp [ParseTree.root] at h_root
          | Node newN newRule newChildren =>
              have h_newN : newN = oldN := by
                simpa [ParseTree.root] using h_root
              cases h_newN
              exact ⟨h_expected, h_new_valid⟩

omit [Monad μ] [SemilatticeAlt μ] [Traversable μ] [BEq α] [DecidableEq α]
  [DecidableEq ν] [Hashable ν] [Fintype ν] in
lemma valid_node_replace_child_split
  {cfg : @CFG α ν}
  {n : ν} {rule : {rule // rule ∈ cfg.rules n}}
  {ruleBefore ruleAfter : List (Symbol α ν)} {sym : Symbol α ν}
  {before after : List (ParseTree cfg)} {old new : ParseTree cfg}
  (h_rule : rule.val = ruleBefore ++ sym :: ruleAfter)
  (h_before_len : ruleBefore.length = before.length)
  (h_valid : (Node (cfg := cfg) n rule (before ++ old :: after)).Valid)
  (h_new_valid : new.Valid)
  (h_root : new.root = old.root)
  (h_leaves : new.leaves = old.leaves)
  (h_size : sizeOf new < sizeOf old) :
    (Node (cfg := cfg) n rule (before ++ new :: after)).Valid ∧
    (Node (cfg := cfg) n rule (before ++ new :: after)).root =
      (Node (cfg := cfg) n rule (before ++ old :: after)).root ∧
    (Node (cfg := cfg) n rule (before ++ new :: after)).leaves =
      (Node (cfg := cfg) n rule (before ++ old :: after)).leaves ∧
    sizeOf (Node (cfg := cfg) n rule (before ++ new :: after)) <
      sizeOf (Node (cfg := cfg) n rule (before ++ old :: after)) := by
  have h_valid' := by
    simpa [ParseTree.Valid] using h_valid
  have h_pairs_old :
      ∀ pair, pair ∈ List.zip rule.val (before ++ old :: after) →
        validChildPair (cfg := cfg) pair := by
    intro pair h_pair
    cases pair with
    | mk pairSym pairChild =>
        have h := h_valid'.2 pairSym pairChild h_pair
        cases pairSym <;> cases pairChild <;>
          simp [validChildPair] at h ⊢ <;> assumption
  have h_pairs_new :
      ∀ pair, pair ∈ List.zip rule.val (before ++ new :: after) →
        validChildPair (cfg := cfg) pair := by
    intro pair h_pair
    have h_pair' :
        pair ∈ List.zip (ruleBefore ++ sym :: ruleAfter)
          (before ++ new :: after) := by
      simpa [h_rule] using h_pair
    rw [List.zip_append h_before_len] at h_pair'
    simp at h_pair'
    cases h_pair' with
    | inl h_prefix =>
        exact h_pairs_old pair (by
          rw [h_rule, List.zip_append h_before_len]
          simp [h_prefix])
    | inr h_rest =>
        cases h_rest with
        | inl h_mid =>
            subst pair
            have h_old_pair : validChildPair (cfg := cfg) (sym, old) := by
              exact h_pairs_old (sym, old) (by
                rw [h_rule, List.zip_append h_before_len]
                simp)
            exact validChildPair_replace_same_root
              (cfg := cfg) h_old_pair h_new_valid h_root
        | inr h_suffix =>
            exact h_pairs_old pair (by
              rw [h_rule, List.zip_append h_before_len]
              simp [h_suffix])
  have h_len_new : rule.val.length = (before ++ new :: after).length := by
    simpa [List.length_append] using h_valid'.1
  refine ⟨?_, rfl, ?_, node_sizeOf_replace_child_lt (cfg := cfg) h_size⟩
  · unfold ParseTree.Valid
    constructor
    · exact h_len_new
    · intro pair h_pair
      cases pair with
      | mk pairSym pairChild =>
          have h_vcp := h_pairs_new (pairSym, pairChild) h_pair
          cases pairSym <;> cases pairChild <;>
            simp [validChildPair] at h_vcp ⊢ <;> assumption
  · simp [forestLeaves, h_leaves]

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
inductive ReplaceSubtree
  {cfg : @CFG α ν}
  (old new : ParseTree cfg) :
    ParseTree cfg → ParseTree cfg → Prop where
  | here :
      ReplaceSubtree old new old new
  | child
      {n : ν} {rule : {rule // rule ∈ cfg.rules n}}
      {before after : List (ParseTree cfg)}
      {child child' : ParseTree cfg}
      (h_child : ReplaceSubtree old new child child') :
      ReplaceSubtree old new
        (Node (cfg := cfg) n rule (before ++ child :: after))
        (Node (cfg := cfg) n rule (before ++ child' :: after))

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
inductive TreeSubtree
  {cfg : @CFG α ν}
  (target : ParseTree cfg) : ParseTree cfg → Prop where
  | here :
      TreeSubtree target target
  | child
      {n : ν} {rule : {rule // rule ∈ cfg.rules n}}
      {before after : List (ParseTree cfg)}
      {child : ParseTree cfg}
      (h_child : TreeSubtree target child) :
      TreeSubtree target
        (Node (cfg := cfg) n rule (before ++ child :: after))

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
inductive ProperTreeSubtree
  {cfg : @CFG α ν}
  (target : ParseTree cfg) : ParseTree cfg → Prop where
  | child
      {n : ν} {rule : {rule // rule ∈ cfg.rules n}}
      {before after : List (ParseTree cfg)}
      {child : ParseTree cfg}
      (h_child : TreeSubtree target child) :
      ProperTreeSubtree target
        (Node (cfg := cfg) n rule (before ++ child :: after))

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
theorem treeSubtree_trans
  {cfg : @CFG α ν} {target middle tree : ParseTree cfg}
  (h_target_middle : TreeSubtree (cfg := cfg) target middle)
  (h_middle_tree : TreeSubtree (cfg := cfg) middle tree) :
    TreeSubtree (cfg := cfg) target tree := by
  induction h_middle_tree with
  | here =>
      exact h_target_middle
  | child h_child ih =>
      exact TreeSubtree.child ih

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
theorem treeSubtree_of_properTreeSubtree
  {cfg : @CFG α ν} {target tree : ParseTree cfg}
  (h_subtree : ProperTreeSubtree (cfg := cfg) target tree) :
    TreeSubtree (cfg := cfg) target tree := by
  cases h_subtree with
  | child h_child =>
      exact TreeSubtree.child h_child

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
theorem properTreeSubtree_of_treeSubtree_of_proper
  {cfg : @CFG α ν} {target middle tree : ParseTree cfg}
  (h_target_middle : TreeSubtree (cfg := cfg) target middle)
  (h_middle_tree : ProperTreeSubtree (cfg := cfg) middle tree) :
    ProperTreeSubtree (cfg := cfg) target tree := by
  cases h_middle_tree with
  | child h_child =>
      exact ProperTreeSubtree.child
        (treeSubtree_trans
          (cfg := cfg) h_target_middle h_child)

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
inductive SeenPath
  {cfg : @CFG α ν} (input : Array α) (root : ParseTree cfg) :
    List (SpanVisit ν) → ParseTree cfg → List α → Prop where
  | root :
      SeenPath input root [] root []
  | child
      {seen : List (SpanVisit ν)}
      {parentPre parentPost : List α}
      {parentN : ν} {parentRule : {rule // rule ∈ cfg.rules parentN}}
      {before after : List (ParseTree cfg)} {child : ParseTree cfg}
      (h_parent_path :
        SeenPath input root seen
          (Node (cfg := cfg) parentN parentRule
            (before ++ child :: after))
          parentPre)
      (h_parent_input :
        input.toList =
          parentPre ++
            (Node (cfg := cfg) parentN parentRule
              (before ++ child :: after)).leaves ++
            parentPost) :
      SeenPath input root
        (nodeSpanVisit parentN parentPre.length
          (Node (cfg := cfg) parentN parentRule
            (before ++ child :: after)) :: seen)
        child
        (parentPre ++ forestLeaves (cfg := cfg) before)

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
inductive SubtreeSpan
  {cfg : @CFG α ν} :
    ParseTree cfg → List α → ParseTree cfg → List α → Prop where
  | here
      (tree : ParseTree cfg) (pre : List α) :
      SubtreeSpan tree pre tree pre
  | child
      {n : ν} {rule : {rule // rule ∈ cfg.rules n}}
      {before after : List (ParseTree cfg)}
      {child target : ParseTree cfg}
      {pre targetPre : List α}
      (h_child :
        SubtreeSpan child (pre ++ forestLeaves (cfg := cfg) before)
          target targetPre) :
      SubtreeSpan
        (Node (cfg := cfg) n rule (before ++ child :: after))
        pre target targetPre

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
theorem seenPath_treeSubtree
  {cfg : @CFG α ν} {input : Array α} {root current : ParseTree cfg}
  {seen : List (SpanVisit ν)} {pre : List α}
  (h_path : SeenPath (cfg := cfg) input root seen current pre) :
    TreeSubtree (cfg := cfg) current root := by
  induction h_path with
  | root =>
      exact TreeSubtree.here
  | child h_parent_path _h_parent_input ih =>
      rename_i seen parentPre parentPost parentN parentRule before after child
      have h_child_parent :
          TreeSubtree (cfg := cfg) child
            (Node (cfg := cfg) parentN parentRule
              (before ++ child :: after)) :=
        TreeSubtree.child TreeSubtree.here
      exact treeSubtree_trans (cfg := cfg) h_child_parent ih

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
theorem seenPath_visit_mem_ancestor
  {cfg : @CFG α ν} {input : Array α} {root current : ParseTree cfg}
  {seen : List (SpanVisit ν)} {pre : List α} {visit : SpanVisit ν}
  (h_path : SeenPath (cfg := cfg) input root seen current pre)
  (h_mem : visit ∈ seen) :
    ∃ ancestorN ancestorRule ancestorChildren ancestorPre ancestorPost,
      visit =
        nodeSpanVisit ancestorN ancestorPre.length
          (Node (cfg := cfg) ancestorN ancestorRule ancestorChildren) ∧
      TreeSubtree (cfg := cfg)
        (Node (cfg := cfg) ancestorN ancestorRule ancestorChildren) root ∧
      ProperTreeSubtree (cfg := cfg) current
        (Node (cfg := cfg) ancestorN ancestorRule ancestorChildren) ∧
      input.toList =
        ancestorPre ++
          (Node (cfg := cfg) ancestorN ancestorRule ancestorChildren).leaves ++
          ancestorPost := by
  induction h_path with
  | root =>
      simp at h_mem
  | child h_parent_path h_parent_input ih =>
      rename_i seen parentPre parentPost parentN parentRule before after child
      simp at h_mem
      cases h_mem with
      | inl h_head =>
          subst visit
          refine ⟨parentN, parentRule, before ++ child :: after,
            parentPre, parentPost, rfl, ?_, ?_, h_parent_input⟩
          · exact seenPath_treeSubtree (cfg := cfg) h_parent_path
          · exact ProperTreeSubtree.child TreeSubtree.here
      | inr h_tail =>
          obtain ⟨ancestorN, ancestorRule, ancestorChildren,
            ancestorPre, ancestorPost, h_visit, h_ancestor_root,
            h_parent_ancestor, h_ancestor_input⟩ := ih h_tail
          refine ⟨ancestorN, ancestorRule, ancestorChildren,
            ancestorPre, ancestorPost, h_visit, h_ancestor_root, ?_,
            h_ancestor_input⟩
          have h_child_parent :
              TreeSubtree (cfg := cfg) child
                (Node (cfg := cfg) parentN parentRule
                  (before ++ child :: after)) :=
            TreeSubtree.child TreeSubtree.here
          exact properTreeSubtree_of_treeSubtree_of_proper
            (cfg := cfg) h_child_parent h_parent_ancestor

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
theorem subtreeSpan_treeSubtree
  {cfg : @CFG α ν} {tree target : ParseTree cfg}
  {pre targetPre : List α}
  (h_span : SubtreeSpan (cfg := cfg) tree pre target targetPre) :
    TreeSubtree (cfg := cfg) target tree := by
  induction h_span with
  | here =>
      exact TreeSubtree.here
  | child h_child ih =>
      exact TreeSubtree.child ih

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
lemma direct_child_leaves_length_le_parent
  {cfg : @CFG α ν}
  {n : ν} {rule : {rule // rule ∈ cfg.rules n}}
  {before after : List (ParseTree cfg)} {child : ParseTree cfg} :
    child.leaves.length ≤
      (Node (cfg := cfg) n rule (before ++ child :: after)).leaves.length := by
  simp [leaves_node_eq_forestLeaves, forestLeaves, List.length_append]
  omega

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
lemma direct_child_span_bounds
  {cfg : @CFG α ν}
  {n : ν} {rule : {rule // rule ∈ cfg.rules n}}
  {before after : List (ParseTree cfg)} {child : ParseTree cfg}
  (parentPre : List α) :
    parentPre.length ≤ (parentPre ++ forestLeaves (cfg := cfg) before).length ∧
    (parentPre ++ forestLeaves (cfg := cfg) before).length +
        child.leaves.length ≤
      parentPre.length +
        (Node (cfg := cfg) n rule (before ++ child :: after)).leaves.length := by
  constructor
  · simp
  · simp [leaves_node_eq_forestLeaves, forestLeaves, List.length_append]
    omega

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
theorem subtreeSpan_bounds
  {cfg : @CFG α ν} {tree target : ParseTree cfg}
  {pre targetPre : List α}
  (h_span : SubtreeSpan (cfg := cfg) tree pre target targetPre) :
    pre.length ≤ targetPre.length ∧
    targetPre.length + target.leaves.length ≤
      pre.length + tree.leaves.length := by
  induction h_span with
  | here =>
      constructor <;> omega
  | child h_child ih =>
      rename_i n rule before after child target pre targetPre
      have h_direct :=
        direct_child_span_bounds
          (cfg := cfg) (n := n) (rule := rule)
          (before := before) (after := after)
          (child := child) pre
      constructor
      · exact Nat.le_trans h_direct.1 ih.1
      · omega

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
theorem subtreeSpan_input
  {cfg : @CFG α ν} {input : Array α}
  {tree target : ParseTree cfg}
  {pre post targetPre : List α}
  (h_span : SubtreeSpan (cfg := cfg) tree pre target targetPre)
  (h_input : input.toList = pre ++ tree.leaves ++ post) :
    ∃ targetPost,
      input.toList = targetPre ++ target.leaves ++ targetPost := by
  induction h_span generalizing post with
  | here =>
      exact ⟨post, h_input⟩
  | child h_child ih =>
      rename_i n rule before after child target pre targetPre
      have h_child_input :
          input.toList =
            (pre ++ forestLeaves (cfg := cfg) before) ++
              child.leaves ++
              (forestLeaves (cfg := cfg) after ++ post) := by
        simpa [leaves_node_eq_forestLeaves, forestLeaves, List.append_assoc]
          using h_input
      exact ih h_child_input

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
lemma direct_same_tag_child_leaves_length_lt_parent_of_span_ne
  {cfg : @CFG α ν}
  {n : ν}
  {parentRule : {rule // rule ∈ cfg.rules n}}
  {childRule : {rule // rule ∈ cfg.rules n}}
  {before after childChildren : List (ParseTree cfg)}
  {parentPre : List α}
  (h_span_ne :
    nodeSpanVisit n parentPre.length
        (Node (cfg := cfg) n parentRule
          (before ++ Node (cfg := cfg) n childRule childChildren :: after)) ≠
      nodeSpanVisit n
        (parentPre ++ forestLeaves (cfg := cfg) before).length
        (Node (cfg := cfg) n childRule childChildren)) :
    (Node (cfg := cfg) n childRule childChildren).leaves.length <
      (Node (cfg := cfg) n parentRule
        (before ++ Node (cfg := cfg) n childRule childChildren :: after)).leaves.length := by
  have h_le :
      (Node (cfg := cfg) n childRule childChildren).leaves.length ≤
        (Node (cfg := cfg) n parentRule
          (before ++ Node (cfg := cfg) n childRule childChildren :: after)).leaves.length :=
    direct_child_leaves_length_le_parent
      (cfg := cfg) (n := n) (rule := parentRule)
      (before := before) (after := after)
      (child := Node (cfg := cfg) n childRule childChildren)
  by_contra h_not_lt
  have h_len_eq :
      (Node (cfg := cfg) n childRule childChildren).leaves.length =
        (Node (cfg := cfg) n parentRule
          (before ++ Node (cfg := cfg) n childRule childChildren :: after)).leaves.length := by
    omega
  have h_parent_len :
      (Node (cfg := cfg) n parentRule
        (before ++ Node (cfg := cfg) n childRule childChildren :: after)).leaves.length =
        (forestLeaves (cfg := cfg) before).length +
          (Node (cfg := cfg) n childRule childChildren).leaves.length +
          (forestLeaves (cfg := cfg) after).length := by
    simp [leaves_node_eq_forestLeaves, forestLeaves, List.length_append,
      Nat.add_assoc]
  have h_before_zero :
      (forestLeaves (cfg := cfg) before).length = 0 := by
    omega
  have h_after_zero :
      (forestLeaves (cfg := cfg) after).length = 0 := by
    omega
  apply h_span_ne
  simp [nodeSpanVisit, h_before_zero, h_after_zero,
    leaves_node_eq_forestLeaves, forestLeaves]

omit [Monad μ] [SemilatticeAlt μ] [Traversable μ] [BEq α] [DecidableEq α]
  [DecidableEq ν] [Hashable ν] [Fintype ν] in
theorem treeSubtree_valid_of_valid
  {cfg : @CFG α ν} {target tree : ParseTree cfg}
  (h_subtree : TreeSubtree (cfg := cfg) target tree)
  (h_valid : tree.Valid) :
    target.Valid := by
  induction h_subtree with
  | here =>
      exact h_valid
  | child h_child ih =>
      rename_i n rule before after child
      have h_child_valid :
          child.Valid := valid_node_child_valid_of_split
            (cfg := cfg) (n := n) (rule := rule)
            (before := before) (after := after)
            (child := child) h_valid
      exact ih h_child_valid

omit [Monad μ] [SemilatticeAlt μ] [Traversable μ] [BEq α] [DecidableEq α]
  [DecidableEq ν] [Hashable ν] [Fintype ν] in
theorem treeSubtree_size_le
  {cfg : @CFG α ν} {target tree : ParseTree cfg}
  (h_subtree : TreeSubtree (cfg := cfg) target tree) :
    sizeOf target ≤ sizeOf tree := by
  induction h_subtree with
  | here =>
      rfl
  | child h_child ih =>
      rename_i n rule before after child
      have h_child_size :
          sizeOf child <
            sizeOf (Node (cfg := cfg) n rule (before ++ child :: after)) := by
        exact ParseTree.sizeOf_lt_of_child
          (parent := Node (cfg := cfg) n rule (before ++ child :: after))
          (child := child)
          (by simp)
      omega

omit [Monad μ] [SemilatticeAlt μ] [Traversable μ] [BEq α] [DecidableEq α]
  [DecidableEq ν] [Hashable ν] [Fintype ν] in
theorem properTreeSubtree_size_lt
  {cfg : @CFG α ν} {target tree : ParseTree cfg}
  (h_subtree : ProperTreeSubtree (cfg := cfg) target tree) :
    sizeOf target < sizeOf tree := by
  cases h_subtree with
  | child h_child =>
      rename_i n rule before after child
      have h_target_child := treeSubtree_size_le (cfg := cfg) h_child
      have h_child_tree :
          sizeOf child <
            sizeOf (Node (cfg := cfg) n rule (before ++ child :: after)) := by
        exact ParseTree.sizeOf_lt_of_child
          (parent := Node (cfg := cfg) n rule (before ++ child :: after))
          (child := child)
          (by simp)
      omega

omit [Monad μ] [SemilatticeAlt μ] [Traversable μ] [BEq α] [DecidableEq α]
  [DecidableEq ν] [Hashable ν] [Fintype ν] in
theorem properTreeSubtree_valid_of_valid
  {cfg : @CFG α ν} {target tree : ParseTree cfg}
  (h_subtree : ProperTreeSubtree (cfg := cfg) target tree)
  (h_valid : tree.Valid) :
    target.Valid := by
  cases h_subtree with
  | child h_child =>
      rename_i n rule before after child
      have h_child_valid :
          child.Valid := valid_node_child_valid_of_split
            (cfg := cfg) (n := n) (rule := rule)
            (before := before) (after := after)
            (child := child) h_valid
      exact treeSubtree_valid_of_valid (cfg := cfg) h_child h_child_valid

omit [Monad μ] [SemilatticeAlt μ] [Traversable μ] [BEq α] [DecidableEq α]
  [DecidableEq ν] [Hashable ν] [Fintype ν] in
theorem replaceSubtree_preserves_valid_root_leaves_size
  {cfg : @CFG α ν}
  {old new tree tree' : ParseTree cfg}
  (h_replace : ReplaceSubtree (cfg := cfg) old new tree tree')
  (h_valid : tree.Valid)
  (h_new_valid : new.Valid)
  (h_root : new.root = old.root)
  (h_leaves : new.leaves = old.leaves)
  (h_size : sizeOf new < sizeOf old) :
    tree'.Valid ∧
    tree'.root = tree.root ∧
    tree'.leaves = tree.leaves ∧
    sizeOf tree' < sizeOf tree := by
  induction h_replace with
  | here =>
      exact ⟨h_new_valid, h_root, h_leaves, h_size⟩
  | child h_child ih =>
      rename_i n rule before after child child'
      have h_child_valid :
          child.Valid := valid_node_child_valid_of_split
            (cfg := cfg) (n := n) (rule := rule)
            (before := before) (after := after)
            (child := child) h_valid
      have h_child_result :=
        ih h_child_valid
      have h_valid' := by
        simpa [ParseTree.Valid] using h_valid
      obtain ⟨ruleBefore, sym, ruleAfter, h_rule, h_before_len⟩ :=
        list_split_at_of_length_cons
          (xs := rule.val) (before := before)
          (child := child) (after := after)
          (by simpa [List.length_append] using h_valid'.1)
      exact valid_node_replace_child_split
        (cfg := cfg) (n := n) (rule := rule)
        (ruleBefore := ruleBefore) (ruleAfter := ruleAfter)
        (sym := sym) (before := before) (after := after)
        (old := child) (new := child')
        h_rule h_before_len h_valid
        h_child_result.1 h_child_result.2.1 h_child_result.2.2.1
        h_child_result.2.2.2

omit [Monad μ] [SemilatticeAlt μ] [Traversable μ] [BEq α] [DecidableEq α]
  [DecidableEq ν] [Hashable ν] [Fintype ν] in
theorem replaceSubtree_of_subtree
  {cfg : @CFG α ν}
  {target tree replacement : ParseTree cfg}
  (h_subtree : TreeSubtree (cfg := cfg) target tree) :
    ∃ tree',
      ReplaceSubtree (cfg := cfg) target replacement tree tree' := by
  induction h_subtree with
  | here =>
      exact ⟨replacement, ReplaceSubtree.here⟩
  | child h_child ih =>
      rename_i n rule before after child
      obtain ⟨child', h_replace_child⟩ := ih
      exact ⟨Node (cfg := cfg) n rule (before ++ child' :: after),
        ReplaceSubtree.child h_replace_child⟩

omit [Fintype ν] in
lemma generatedChildWitness_of_valid_pairs
  {cfg : @CFG α ν}
  {recur : ν → ParserM (tag := tag cfg) α List (ParseTree cfg)}
  {input : Array α}
  {rule : List (Symbol α ν)} {children : List (ParseTree cfg)}
  {pre post : List α}
  (h_len : rule.length = children.length)
  (h_valid :
    ∀ pair, pair ∈ List.zip rule children → validChildPair (cfg := cfg) pair)
  (h_input : input.toList = pre ++ forestLeaves (cfg := cfg) children ++ post)
  (h_recur :
    ∀ {childN : ν} {rule' : {rule // rule ∈ cfg.rules childN}}
      {grandchildren : List (ParseTree cfg)} {pre' post' : List α},
      (Node (cfg := cfg) childN rule' grandchildren).Valid →
      input.toList = pre' ++ (Node (cfg := cfg) childN rule' grandchildren).leaves ++ post' →
      Node (cfg := cfg) childN rule' grandchildren ∈
        (runParser (tag := tag cfg) (recur childN) input pre'.length).1.getD
          (pre'.length + (Node (cfg := cfg) childN rule' grandchildren).leaves.length) []) :
    GeneratedChildWitness cfg recur input rule children pre.length
      (pre.length + (forestLeaves (cfg := cfg) children).length) := by
  induction rule generalizing children pre with
  | nil =>
      cases children with
      | nil =>
          simpa using GeneratedChildWitness.nil (cfg := cfg) (recur := recur)
            (input := input) pre.length
      | cons child tail =>
          simp at h_len
  | cons sym rest ih =>
      cases children with
      | nil =>
          simp at h_len
      | cons child tail =>
          have h_len_tail : rest.length = tail.length := by
            simpa using h_len
          have h_tail_valid :
              ∀ pair, pair ∈ List.zip rest tail → validChildPair (cfg := cfg) pair := by
            intro pair h_pair
            exact h_valid pair (by simp [h_pair])
          have h_input_tail :
              input.toList =
                (pre ++ child.leaves) ++ forestLeaves (cfg := cfg) tail ++ post := by
            simpa [forestLeaves, List.append_assoc] using h_input
          cases sym with
          | term a =>
              cases child with
              | Leaf b =>
                  have h_ab : a = b := by
                    have h_head := h_valid (Symbol.term a, Leaf (cfg := cfg) b) (by simp)
                    simpa [validChildPair] using h_head
                  cases h_ab
                  have h_term : input[pre.length]? = some a := by
                    apply array_getElem?_of_toList_eq_append_singleton
                    simpa [forestLeaves, ParseTree.leaves, List.append_assoc] using h_input
                  have h_tail := ih h_len_tail h_tail_valid h_input_tail
                  exact GeneratedChildWitness.term h_term
                    (by
                      simpa [forestLeaves, ParseTree.leaves, List.length_append,
                        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
                        using h_tail)
              | Node n' rule' grandchildren =>
                  have h_false : False := by
                    have h_head := h_valid
                      (Symbol.term a, Node (cfg := cfg) n' rule' grandchildren) (by simp)
                    simp [validChildPair] at h_head
                  exact False.elim h_false
          | nonterm childN =>
              cases child with
              | Leaf b =>
                  have h_false : False := by
                    have h_head := h_valid (Symbol.nonterm childN, Leaf (cfg := cfg) b) (by simp)
                    simp [validChildPair] at h_head
                  exact False.elim h_false
              | Node n' rule' grandchildren =>
                  have h_child_valid_root :
                      childN = n' ∧ (Node (cfg := cfg) n' rule' grandchildren).Valid := by
                    have h_head := h_valid
                      (Symbol.nonterm childN, Node (cfg := cfg) n' rule' grandchildren) (by simp)
                    simpa [validChildPair] using h_head
                  obtain ⟨h_eq, h_child_valid⟩ := h_child_valid_root
                  cases h_eq
                  have h_child_mem :
                      Node (cfg := cfg) childN rule' grandchildren ∈
                        (runParser (tag := tag cfg) (recur childN) input pre.length).1.getD
                          (pre.length +
                            (Node (cfg := cfg) childN rule' grandchildren).leaves.length) [] := by
                    apply h_recur h_child_valid
                    simpa [forestLeaves, ParseTree.leaves, List.append_assoc] using h_input
                  have h_tail := ih h_len_tail h_tail_valid h_input_tail
                  exact GeneratedChildWitness.nonterm h_child_mem
                    (by
                      simpa [forestLeaves, ParseTree.leaves, List.length_append, Nat.add_assoc]
                        using h_tail)

omit [Fintype ν] in
lemma generatedChildWitness_of_valid_node_span
  {cfg : @CFG α ν}
  {recur : ν → ParserM (tag := tag cfg) α List (ParseTree cfg)}
  {input : Array α}
  {n : ν} {rule : {rule // rule ∈ cfg.rules n}} {children : List (ParseTree cfg)}
  {pre post : List α}
  (h_valid : (Node (cfg := cfg) n rule children).Valid)
  (h_input : input.toList = pre ++ (Node (cfg := cfg) n rule children).leaves ++ post)
  (h_recur :
    ∀ {childN : ν} {rule' : {rule // rule ∈ cfg.rules childN}}
      {grandchildren : List (ParseTree cfg)} {pre' post' : List α},
      (Node (cfg := cfg) childN rule' grandchildren).Valid →
      input.toList = pre' ++ (Node (cfg := cfg) childN rule' grandchildren).leaves ++ post' →
      Node (cfg := cfg) childN rule' grandchildren ∈
        (runParser (tag := tag cfg) (recur childN) input pre'.length).1.getD
          (pre'.length + (Node (cfg := cfg) childN rule' grandchildren).leaves.length) []) :
    GeneratedChildWitness cfg recur input rule.val children pre.length
      (pre.length + (Node (cfg := cfg) n rule children).leaves.length) := by
  have h_valid' :
      rule.val.length = children.length ∧
      ∀ pair (_h : pair ∈ List.zip rule.val children), match _h_pair : pair, _h with
        | ⟨Symbol.term a, Leaf b⟩, _ => a = b
        | ⟨Symbol.nonterm n, subtree@_h:(Node n' _ _)⟩, _ => n = n' ∧ subtree.Valid
        | _, _ => False := by
    simpa [ParseTree.Valid] using h_valid
  have h_pairs :
      ∀ pair, pair ∈ List.zip rule.val children → validChildPair (cfg := cfg) pair := by
    intro pair h_pair
    have h := h_valid'.2 pair h_pair
    cases pair with
    | mk sym subtree =>
        cases sym <;> cases subtree <;> simp [validChildPair] at h ⊢ <;> assumption
  have h_witness := generatedChildWitness_of_valid_pairs
    (cfg := cfg) (recur := recur) (input := input)
    (rule := rule.val) (children := children) (pre := pre) (post := post)
    h_valid'.1 h_pairs (by simpa using h_input) h_recur
  simpa using h_witness

omit [Fintype ν] in
lemma generatedChildWitness_to_traverse
  {cfg : @CFG α ν}
  {recur : ν → ParserM (tag := tag cfg) α List (ParseTree cfg)}
  {input : Array α}
  {rule : List (Symbol α ν)} {children : List (ParseTree cfg)}
  {start end_ : ℕ}
  (h : GeneratedChildWitness cfg recur input rule children start end_) :
    TraverseCompleteWitness cfg input
      (rule.map fun sym =>
        match sym with
        | Symbol.term a => Leaf <$> terminal' (tag := tag cfg) a
        | Symbol.nonterm n => recur n)
      start children end_ := by
  induction h with
  | nil pos =>
      exact TraverseCompleteWitness.nil (cfg := cfg) (input := input) pos
  | term h_term _h_tail ih =>
      exact TraverseCompleteWitness.cons
        (cfg := cfg) (input := input)
        (h_head := terminal'_complete (cfg := cfg) h_term)
        ih
  | nonterm h_child _h_tail ih =>
      exact TraverseCompleteWitness.cons
        (cfg := cfg) (input := input)
        (h_head := h_child)
        ih

omit [Fintype ν] in
lemma runParser_traverse_complete_of_witness
  {cfg : @CFG α ν}
  {γ : Type u} [DecidableEq γ]
  {input : Array α}
  {parsers : List (ParserM (tag := tag cfg) α List γ)}
  {start end_ : ℕ} {result : List γ}
  (h : TraverseCompleteWitness cfg input parsers start result end_)
  : result ∈ (runParser (tag := tag cfg) (List.traverse id parsers) input start).1.getD end_ [] := by
  induction h with
  | nil pos =>
      rw [Std.HashMap.getD_eq_getD_getElem?, List.traverse, runParser_pure]
      simp
  | cons h_head _h_tail ih =>
      exact runParser_traverse_complete_cons (cfg := cfg) h_head ih

omit [Fintype ν] in
lemma runParser_rule_branch_complete
  {cfg : @CFG α ν}
  {n : ν} {rule : List (Symbol α ν)}
  (h_rule : rule ∈ cfg.rules n)
  {mkParser : Symbol α ν → ParserM (tag := tag cfg) α List (ParseTree cfg)}
  {input : Array α} {start end_ : ℕ} {subtrees : List (ParseTree cfg)}
  (h_children :
    TraverseCompleteWitness cfg input (rule.map mkParser) start subtrees end_)
  : Node (cfg := cfg) n ⟨rule, h_rule⟩ subtrees ∈
      (runParser (tag := tag cfg)
        (Node n ⟨rule, h_rule⟩ <$>
          List.traverse id (rule.map mkParser))
        input start).1.getD end_ [] := by
  apply runParser_map_complete (cfg := cfg)
    (p := List.traverse id (rule.map mkParser))
    (f := Node n ⟨rule, h_rule⟩)
    (x := subtrees)
  exact runParser_traverse_complete_of_witness (cfg := cfg) h_children

omit [Fintype ν] in
lemma lower_terminal'_sound
  {cfg : @CFG α ν}
  {a : α} {input : Array α} {start end_ : ℕ}
  {memo : MemoData (tag cfg) List} {tree : ParseTree cfg}
  (h : tree ∈ (((Leaf <$> terminal' (tag := tag cfg) a).lower start)
      memo input).1.getD end_ []) :
    tree = Leaf a := by
  obtain ⟨x, h_x, h_tree⟩ := mem_lower_map_exists_of_mem
    (tag := tag cfg) (β := α)
    (p := terminal' (tag := tag cfg) (μ := List) a)
    (f := Leaf (cfg := cfg))
    (memo := memo) (input := input)
    (start := start) (end_pos := end_) (y := tree) h
  have h_x' := (mem_lower_terminal_iff
    (tag := tag cfg) (a := a) (x := x)
    (input := input) (start := start) (end_pos := end_)
    (memo := memo)).mp h_x
  exact h_tree.symm.trans (congrArg Leaf h_x'.2.2)

omit [Fintype ν] in
lemma lower_terminal'_bounded
  {cfg : @CFG α ν}
  {a : α} {input : Array α} {start end_ : ℕ}
  {memo : MemoData (tag cfg) List} {tree : ParseTree cfg}
  (_h_start : start ≤ input.size)
  (h : tree ∈ (((Leaf <$> terminal' (tag := tag cfg) a).lower start)
      memo input).1.getD end_ []) :
    start ≤ end_ ∧ end_ ≤ input.size := by
  obtain ⟨x, h_x, _h_tree⟩ := mem_lower_map_exists_of_mem
    (tag := tag cfg) (β := α)
    (p := terminal' (tag := tag cfg) (μ := List) a)
    (f := Leaf (cfg := cfg))
    (memo := memo) (input := input)
    (start := start) (end_pos := end_) (y := tree) h
  have h_x' := (mem_lower_terminal_iff
    (tag := tag cfg) (a := a) (x := x)
    (input := input) (start := start) (end_pos := end_)
    (memo := memo)).mp h_x
  obtain ⟨h_match, h_end, _h_x_eq⟩ := h_x'
  have h_start_lt : start < input.size := by
    exact (Array.getElem?_eq_some_iff.mp h_match.symm).1
  constructor
  · omega
  · omega

omit [Fintype ν] in
lemma lower_terminal'_result_bounded
  {cfg : @CFG α ν}
  {a : α} {input : Array α} :
    lower_result_bounded cfg (Leaf <$> terminal' (tag := tag cfg) a) input := by
  intro memo _h_memo start end_ h_start tree h_mem
  exact lower_terminal'_bounded
    (cfg := cfg) (a := a) (input := input)
    (start := start) (end_ := end_)
    (memo := memo) (tree := tree)
    h_start h_mem

omit [Fintype ν] in
lemma lower_terminal'_memo_wellFormed
  {cfg : @CFG α ν}
  {a : α} {input : Array α} :
    lower_memo_wellFormed cfg
      (Leaf (cfg := cfg) <$> terminal' (tag := tag cfg) a) input := by
  apply lower_map_memo_wellFormed
    (cfg := cfg)
    (p := terminal' (tag := tag cfg) (μ := List) a)
    (f := Leaf (cfg := cfg))
  intro memo h_memo start
  have h_state :
      (((terminal' (tag := tag cfg) (μ := List) a).lower start)
        memo input).2.val = memo := by
    rw [terminal'_eq_lift_terminalPrimitive (tag := tag cfg) (a := a)]
    rw [lower_lift_snd_val_eq
      (tag := tag cfg) (β := α)
      (p := terminalPrimitive (tag := tag cfg) a)
      (memo := memo) (input := input) (start := start)]
    exact terminalPrimitive_snd_val_eq
      (tag := tag cfg) (a := a)
      (input := input) (start := start) (memo := memo)
  rw [h_state]
  exact h_memo

omit [Fintype ν] in
lemma mem_lower_traverse_cons_terminal_exists_tail
  {cfg : @CFG α ν}
  {a : α}
  {tail : List (ParserM (tag := tag cfg) α List (ParseTree cfg))}
  {memo : MemoData (tag cfg) List} {input : Array α}
  {start end_ : ℕ} {result_head : ParseTree cfg}
  {result_tail : List (ParseTree cfg)}
  (h :
      result_head :: result_tail ∈
        (((List.traverse id
          ((Leaf (cfg := cfg) <$> terminal' (tag := tag cfg) a) :: tail)).lower start)
          memo input).1.getD end_ []) :
      result_head = Leaf (cfg := cfg) a ∧
        result_head ∈
          (((Leaf (cfg := cfg) <$> terminal' (tag := tag cfg) a).lower start)
            memo input).1.getD (start + 1) [] ∧
        start + 1 ≤ input.size ∧
        ∃ memo_tail,
          result_tail ∈
            (((List.traverse id tail).lower (start + 1))
              memo_tail input).1.getD end_ [] := by
  have h_bind :
      result_head :: result_tail ∈
        (((List.traverse id
          ((ParserM.Bind
            (terminalPrimitive (tag := tag cfg) a)
            (fun x =>
              ParserM.Return (tag := tag cfg) (β := α) (μ := List)
                (Leaf (cfg := cfg) x)) :
              ParserM (tag := tag cfg) α List (ParseTree cfg)) :: tail)).lower start)
          memo input).1.getD end_ [] := by
    simpa [terminal'_eq_lift_terminalPrimitive (tag := tag cfg) (a := a)]
      using h
  obtain ⟨split, x, memo_tail, h_x, h_leaf_eq, h_tail⟩ :=
    mem_lower_traverse_cons_bind_return_exists_head_tail
      (tag := tag cfg) (β := α)
      (p := terminalPrimitive (tag := tag cfg) a)
      (f := Leaf (cfg := cfg))
      (tail := tail)
      (memo := memo) (input := input)
      (start := start) (end_pos := end_)
      h_bind
  have h_x' := (mem_terminalPrimitive_iff
    (tag := tag cfg) (a := a) (x := x)
    (input := input) (start := start) (end_pos := split)
    (memo := memo)).mp h_x
  obtain ⟨h_match, h_split, h_x_eq⟩ := h_x'
  cases h_x_eq
  cases h_split
  have h_term :
      a ∈
        (((terminal' (tag := tag cfg) (μ := List) a).lower start)
          memo input).1.getD (start + 1) [] := by
    exact (mem_lower_terminal_iff
      (tag := tag cfg) (a := a) (x := a)
      (input := input) (start := start) (end_pos := start + 1)
      (memo := memo)).mpr
      ⟨h_match, rfl, rfl⟩
  have h_head_mem_leaf :
      Leaf (cfg := cfg) a ∈
        (((Leaf (cfg := cfg) <$> terminal' (tag := tag cfg) a).lower start)
          memo input).1.getD (start + 1) [] := by
    exact mem_lower_map_of_mem
      (tag := tag cfg) (β := α)
      (p := terminal' (tag := tag cfg) (μ := List) a)
      (f := Leaf (cfg := cfg))
      (memo := memo) (input := input)
      (start := start) (end_pos := start + 1)
      (x := a) h_term
  have h_head_mem :
      result_head ∈
        (((Leaf (cfg := cfg) <$> terminal' (tag := tag cfg) a).lower start)
          memo input).1.getD (start + 1) [] := by
    simpa [h_leaf_eq] using h_head_mem_leaf
  have h_start_succ : start + 1 ≤ input.size := by
    have h_lt : start < input.size :=
      (Array.getElem?_eq_some_iff.mp h_match.symm).1
    omega
  exact ⟨h_leaf_eq.symm, h_head_mem, h_start_succ, memo_tail, h_tail⟩

omit [Fintype ν] in
lemma mem_lower_traverse_cons_terminal_exists_tail_wf
  {cfg : @CFG α ν}
  {a : α}
  {tail : List (ParserM (tag := tag cfg) α List (ParseTree cfg))}
  {memo : MemoData (tag cfg) List} {input : Array α}
  {start end_ : ℕ} {result_head : ParseTree cfg}
  {result_tail : List (ParseTree cfg)}
  (h_tail_memo :
    lower_memo_wellFormed cfg (List.traverse id tail) input)
  (h_memo : memo_wellFormed cfg input memo)
  (h :
      result_head :: result_tail ∈
        (((List.traverse id
          ((Leaf (cfg := cfg) <$> terminal' (tag := tag cfg) a) :: tail)).lower start)
          memo input).1.getD end_ []) :
      result_head = Leaf (cfg := cfg) a ∧
        result_head ∈
          (((Leaf (cfg := cfg) <$> terminal' (tag := tag cfg) a).lower start)
            memo input).1.getD (start + 1) [] ∧
        start + 1 ≤ input.size ∧
        ∃ memo_tail,
          memo_wellFormed cfg input memo_tail ∧
          result_tail ∈
            (((List.traverse id tail).lower (start + 1))
              memo_tail input).1.getD end_ [] := by
  have h_bind :
      result_head :: result_tail ∈
        (((List.traverse id
          ((ParserM.Bind
            (terminalPrimitive (tag := tag cfg) a)
            (fun x =>
              ParserM.Return (tag := tag cfg) (β := α) (μ := List)
                (Leaf (cfg := cfg) x)) :
              ParserM (tag := tag cfg) α List (ParseTree cfg)) :: tail)).lower start)
          memo input).1.getD end_ [] := by
    simpa [terminal'_eq_lift_terminalPrimitive (tag := tag cfg) (a := a)]
      using h
  rw [List.traverse, seq_eq_bind] at h_bind
  simp at h_bind
  change result_head :: result_tail ∈
    (((ParserM.Bind
      (terminalPrimitive (tag := tag cfg) a)
      (fun x => List.cons (Leaf (cfg := cfg) x) <$> List.traverse id tail)).lower start)
      memo input).1.getD end_ [] at h_bind
  obtain ⟨prePairs, _postPairs, split, values, preValues, _postValues, x,
    h_toList, h_values, h_action⟩ :=
    mem_lower_bind_exists_action_split_mem
      (tag := tag cfg) (β := α)
      (p := terminalPrimitive (tag := tag cfg) a)
      (k := fun x => List.cons (Leaf (cfg := cfg) x) <$> List.traverse id tail)
      (memo := memo) (input := input)
      (start := start) (end_pos := end_)
      (x := result_head :: result_tail) h_bind
  have h_get : ((terminalPrimitive (tag := tag cfg) a start) memo input).1[split]? =
      some values := by
    rw [← Std.HashMap.mem_toList_iff_getElem?_eq_some]
    rw [h_toList]
    simp
  have h_x_mem :
      x ∈ ((terminalPrimitive (tag := tag cfg) a start) memo input).1.getD split [] := by
    rw [Std.HashMap.getD_eq_getD_getElem?]
    simp [h_get, h_values]
  have h_x' := (mem_terminalPrimitive_iff
    (tag := tag cfg) (a := a) (x := x)
    (input := input) (start := start) (end_pos := split)
    (memo := memo)).mp h_x_mem
  obtain ⟨h_match, h_split, h_x_eq⟩ := h_x'
  let memoPrefix : MemoData (tag cfg) List :=
    ((Traversable.foldl joinUnderCache
      (List.foldl (Traversable.foldl joinUnderCache)
        (pure Std.HashMap.emptyWithCapacity)
        (List.map
          (fun pair : ℕ × List α =>
            match pair with
            | (j, values) =>
                List.map
                  (fun x =>
                    ((List.cons (Leaf (cfg := cfg) x) <$>
                      List.traverse id tail).lower j))
                  values)
          prePairs))
      (List.map
        (fun x =>
          ((List.cons (Leaf (cfg := cfg) x) <$>
            List.traverse id tail).lower split))
        preValues))
      (↑((terminalPrimitive (tag := tag cfg) a start) memo input).2) input).2.val
  have h_prefix_wf : memo_wellFormed cfg input memoPrefix := by
    have h_p :
        ∀ start,
          ∀ memo : MemoData (tag cfg) List,
            memo_wellFormed cfg input memo →
            memo_wellFormed cfg input
              (((terminalPrimitive (tag := tag cfg) a start)
                memo input).2.val) := by
      intro start memo h_memo
      rw [terminalPrimitive_snd_val_eq
        (tag := tag cfg) (a := a)
        (input := input) (start := start) (memo := memo)]
      exact h_memo
    have h_k :
        ∀ x,
          lower_memo_wellFormed cfg
            (List.cons (Leaf (cfg := cfg) x) <$> List.traverse id tail) input := by
      intro x
      exact lower_map_memo_wellFormed
        (cfg := cfg)
        (p := List.traverse id tail)
        (f := List.cons (Leaf (cfg := cfg) x))
        h_tail_memo
    simpa [memoPrefix] using
      (bind_action_prefix_memo_wellFormed
        (cfg := cfg) (input := input)
        (p := terminalPrimitive (tag := tag cfg) a)
        (k := fun x =>
          List.cons (Leaf (cfg := cfg) x) <$> List.traverse id tail)
        (prePairs := prePairs) (preValues := preValues)
        (split := split) (start := start)
        (memo := memo) h_p h_k h_memo)
  obtain ⟨h_head_eq, h_tail⟩ :=
    mem_lower_cons_map_exists_of_cons
      (tag := tag cfg) (β := α)
      (tail := tail) (head_result := Leaf (cfg := cfg) x)
      (memo := memoPrefix) (input := input)
      (split := split) (end_pos := end_)
      (by simpa [memoPrefix] using h_action)
  cases h_x_eq
  cases h_split
  have h_term :
      a ∈
        (((terminal' (tag := tag cfg) (μ := List) a).lower start)
          memo input).1.getD (start + 1) [] := by
    exact (mem_lower_terminal_iff
      (tag := tag cfg) (a := a) (x := a)
      (input := input) (start := start) (end_pos := start + 1)
      (memo := memo)).mpr
      ⟨h_match, rfl, rfl⟩
  have h_head_mem_leaf :
      Leaf (cfg := cfg) a ∈
        (((Leaf (cfg := cfg) <$> terminal' (tag := tag cfg) a).lower start)
          memo input).1.getD (start + 1) [] := by
    exact mem_lower_map_of_mem
      (tag := tag cfg) (β := α)
      (p := terminal' (tag := tag cfg) (μ := List) a)
      (f := Leaf (cfg := cfg))
      (memo := memo) (input := input)
      (start := start) (end_pos := start + 1)
      (x := a) h_term
  have h_start_succ : start + 1 ≤ input.size := by
    have h_lt : start < input.size :=
      (Array.getElem?_eq_some_iff.mp h_match.symm).1
    omega
  refine ⟨h_head_eq, ?_, h_start_succ, memoPrefix, h_prefix_wf, ?_⟩
  · simpa [h_head_eq] using h_head_mem_leaf
  · simpa using h_tail

omit [Fintype ν] in
lemma terminalPrimitive_getElem?_eq_some_of_match
  {cfg : @CFG α ν}
  {a : α} {memo : MemoData (tag cfg) List} {input : Array α} {start : ℕ}
  (h_term : input[start]? = some a) :
    ((terminalPrimitive (tag := tag cfg) a start) memo input).1[start + 1]? =
      some [a] := by
  unfold terminalPrimitive
  simp only [ge_iff_le, Nat.zero_le, decide_true, Bool.true_and]
  simp only [readThe, MonadReader.read, MonadReaderOf.read,
    ReaderT.read, liftM, monadLift, MonadLift.monadLift]
  simp only [instMonadMStateT]
  simp only [ReaderT.instMonad, ReaderT.bind, Id.instMonad, Pure.pure,
    ReaderT.pure]
  simp [h_term.symm, ReaderT.pure, Pure.pure]

omit [Fintype ν] in
lemma terminalPrimitive_toList_eq_singleton_of_match
  {cfg : @CFG α ν}
  {a : α} {memo : MemoData (tag cfg) List} {input : Array α} {start : ℕ}
  (h_term : input[start]? = some a) :
    ((terminalPrimitive (tag := tag cfg) a start) memo input).1.toList =
      [(start + 1, [a])] := by
  unfold terminalPrimitive
  simp only [ge_iff_le, Nat.zero_le, decide_true, Bool.true_and]
  simp only [readThe, MonadReader.read, MonadReaderOf.read,
    ReaderT.read, liftM, monadLift, MonadLift.monadLift]
  simp only [instMonadMStateT]
  simp only [ReaderT.instMonad, ReaderT.bind, Id.instMonad, Pure.pure,
    ReaderT.pure]
  simp [h_term.symm, ReaderT.pure, Pure.pure]
  exact hashMap_singleton_toList_eq_singleton (start + 1) [a]

omit [Fintype ν] in
lemma memoState_pure_snd_val_eq
  {cfg : @CFG α ν} {δ : Type u}
  (x : δ) (memo : MemoData (tag cfg) List) (input : Array α) :
    ((pure x :
        MStateT (MemoData (tag cfg) List) (ReaderM (Array α)) δ)
      memo input).2.val = memo := by
  rfl

omit [Fintype ν] in
lemma memoState_pure_snd_eq
  {cfg : @CFG α ν} {δ : Type u}
  (x : δ) (memo : MemoData (tag cfg) List) (input : Array α) :
    (↑((pure x :
        MStateT (MemoData (tag cfg) List) (ReaderM (Array α)) δ)
      memo input).2 : MemoData (tag cfg) List) = memo := by
  rfl

omit [Fintype ν] in
lemma terminalPrimitive_snd_eq
  {cfg : @CFG α ν}
  (a : α) (memo : MemoData (tag cfg) List) (input : Array α)
  (start : ℕ) :
    (↑((terminalPrimitive (tag := tag cfg) a start)
      memo input).2 : MemoData (tag cfg) List) = memo := by
  exact terminalPrimitive_snd_val_eq
    (tag := tag cfg) (a := a)
    (input := input) (start := start) (memo := memo)

omit [Fintype ν] in
lemma empty_joinUnderCache_prefix_snd_eq
  {cfg : @CFG α ν} {δ : Type u} [DecidableEq δ]
  (memo : MemoData (tag cfg) List) (input : Array α) :
    (↑((Traversable.foldl joinUnderCache
      (pure (Std.HashMap.emptyWithCapacity : ResultMap List δ) :
        MStateT (MemoData (tag cfg) List) (ReaderM (Array α))
          (ResultMap List δ))
      ([] : List
        (MStateT (MemoData (tag cfg) List) (ReaderM (Array α))
          (ResultMap List δ))))
      memo input).2 : MemoData (tag cfg) List) = memo := by
  simp [traversable_foldl_nil, Pure.pure, ReaderT.pure]

omit [Fintype ν] in
lemma lower_return_bind_cons_complete
  {cfg : @CFG α ν} {γ : Type u} [DecidableEq γ]
  {tail : List (ParserM (tag := tag cfg) α List γ)}
  {memo : MemoData (tag cfg) List} {input : Array α}
  {start end_ : ℕ} {x : γ} {xs : List γ}
  (h_tail :
    xs ∈ (((List.traverse id tail).lower start) memo input).1.getD end_ []) :
    x :: xs ∈
      ((((ParserM.Return (tag := tag cfg) (β := α) (μ := List) x) >>=
          fun y => List.cons y <$> List.traverse id tail).lower start)
        memo input).1.getD end_ [] := by
  change x :: xs ∈
    (((List.cons x <$> List.traverse id tail).lower start)
      memo input).1.getD end_ []
  exact mem_lower_map_of_mem
    (tag := tag cfg) (β := α)
    (p := List.traverse id tail)
    (f := List.cons x)
    (memo := memo) (input := input)
    (start := start) (end_pos := end_)
    (x := xs) h_tail

omit [Fintype ν] in
lemma lower_traverse_complete_cons_return
  {cfg : @CFG α ν} {γ : Type u} [DecidableEq γ]
  {tail : List (ParserM (tag := tag cfg) α List γ)}
  {memo : MemoData (tag cfg) List} {input : Array α}
  {start end_ : ℕ} {x : γ} {xs : List γ}
  (h_tail :
    xs ∈ (((List.traverse id tail).lower start) memo input).1.getD end_ []) :
    x :: xs ∈
      (((List.traverse id
        ((ParserM.Return (tag := tag cfg) (β := α) (μ := List) x) :: tail)).lower start)
        memo input).1.getD end_ [] := by
  rw [List.traverse, seq_eq_bind]
  simp
  exact lower_return_bind_cons_complete
    (cfg := cfg) (tail := tail) (memo := memo) (input := input)
    (start := start) (end_ := end_) (x := x) (xs := xs) h_tail

set_option maxHeartbeats 700000 in
omit [Fintype ν] in
lemma lower_traverse_complete_cons_terminal
  {cfg : @CFG α ν}
  {a : α}
  {tail : List (ParserM (tag := tag cfg) α List (ParseTree cfg))}
  {memo : MemoData (tag cfg) List} {input : Array α}
  {start end_ : ℕ} {result_tail : List (ParseTree cfg)}
  (h_term : input[start]? = some a)
  (h_tail :
    result_tail ∈
      (((List.traverse id tail).lower (start + 1)) memo input).1.getD end_ []) :
    Leaf (cfg := cfg) a :: result_tail ∈
      (((List.traverse id
        ((Leaf (cfg := cfg) <$> terminal' (tag := tag cfg) a) :: tail)).lower start)
        memo input).1.getD end_ [] := by
  have h_bind :
      Leaf (cfg := cfg) a :: result_tail ∈
        (((List.traverse id
          ((ParserM.Bind
            (terminalPrimitive (tag := tag cfg) a)
            (fun x =>
              ParserM.Return (tag := tag cfg) (β := α) (μ := List)
                (Leaf (cfg := cfg) x)) :
              ParserM (tag := tag cfg) α List (ParseTree cfg)) :: tail)).lower start)
          memo input).1.getD end_ [] := by
    refine mem_lower_traverse_complete_cons_of_bind_getElem_action_mem
      (tag := tag cfg) (β := α)
      (p := terminalPrimitive (tag := tag cfg) a)
      (k := fun x =>
        ParserM.Return (tag := tag cfg) (β := α) (μ := List)
          (Leaf (cfg := cfg) x))
      (tail := tail)
      (split := start + 1) (values := [a]) (a := a)
      (memo := memo) (input := input)
      (start := start) (end_pos := end_)
      (x := Leaf (cfg := cfg) a) (xs := result_tail)
      ?_ ?_ ?_
    · exact terminalPrimitive_getElem?_eq_some_of_match
        (cfg := cfg) (a := a) (memo := memo) (input := input)
        (start := start) h_term
    · simp
    · intro prePairs postPairs preValues postValues h_toList h_values
      have h_toList' :
          [(start + 1, [a])] =
            prePairs ++ (start + 1, [a]) :: postPairs := by
        simpa [terminalPrimitive_toList_eq_singleton_of_match
          (cfg := cfg) (a := a) (memo := memo) (input := input)
          (start := start) h_term] using h_toList
      have h_prePairs : prePairs = [] := by
        cases prePairs with
        | nil => rfl
        | cons head rest =>
            simp [List.cons_append] at h_toList'
      cases h_prePairs
      have h_postPairs : postPairs = [] := by
        simpa using h_toList'
      cases h_postPairs
      have h_preValues : preValues = [] := by
        cases preValues with
        | nil => rfl
        | cons head rest =>
            simp [List.cons_append] at h_values
      cases h_preValues
      have h_postValues : postValues = [] := by
        simpa using h_values
      cases h_postValues
      let memoPrefix : MemoData (tag cfg) List :=
        ↑((Traversable.foldl joinUnderCache
          (List.foldl (Traversable.foldl joinUnderCache)
            (pure Std.HashMap.emptyWithCapacity)
            (List.map
              (fun pair : ℕ × List α =>
                match pair with
                | (j, values) =>
                    List.map
                      (fun x =>
                        ((ParserM.Return (tag := tag cfg) (β := α) (μ := List)
                          (Leaf (cfg := cfg) x)).lower j))
                      values)
              ([] : List (ℕ × List α))))
          (List.map
            (fun x =>
              ((ParserM.Return (tag := tag cfg) (β := α) (μ := List)
                (Leaf (cfg := cfg) x)).lower (start + 1)))
            ([] : List α)))
          (↑((terminalPrimitive (tag := tag cfg) a start)
            memo input).2 : MemoData (tag cfg) List) input).2
      have h_prefix : memoPrefix = memo := by
        simp [memoPrefix, terminalPrimitive_snd_eq
          (cfg := cfg) (a := a) (memo := memo) (input := input)
          (start := start), traversable_foldl_nil, Pure.pure, ReaderT.pure]
      have h_action :=
        lower_return_bind_cons_complete
          (cfg := cfg) (tail := tail)
          (memo := memo) (input := input)
          (start := start + 1) (end_ := end_)
          (x := Leaf (cfg := cfg) a)
          (xs := result_tail) h_tail
      change Leaf (cfg := cfg) a :: result_tail ∈
        ((((ParserM.Return (tag := tag cfg) (β := α) (μ := List)
              (Leaf (cfg := cfg) a) >>=
            fun y => List.cons y <$> List.traverse id tail).lower (start + 1))
          memoPrefix input).1.getD end_ [])
      rw [h_prefix]
      exact h_action
  simpa [terminal'_eq_lift_terminalPrimitive (tag := tag cfg) (a := a)]
    using h_bind

-- set_option maxHeartbeats 800000 in
omit [Fintype ν] in
lemma terminal'_sound
  {cfg : @CFG α ν}
  {a : α} {input : Array α} {start end_ : ℕ} {tree : ParseTree cfg}
  (h : tree ∈ (runParser (Leaf <$> terminal' (tag := tag cfg) a) input start).1.getD end_ [])
  : tree = Leaf a := by
  obtain ⟨x, h_x, h_tree⟩ := mem_runParser_map_exists_of_mem
    (tag := tag cfg) (β := α)
    (p := terminal' (tag := tag cfg) (μ := List) a)
    (f := Leaf (cfg := cfg))
    (input := input) (start := start) (end_pos := end_) (y := tree) h
  have h_x' := (mem_runParser_terminal_iff (tag := tag cfg)
    (a := a) (x := x) (input := input) (start := start) (end_pos := end_)).mp h_x
  exact h_tree.symm.trans (congrArg Leaf h_x'.2.2)

omit [Fintype ν] in
lemma terminal'_bounded
  {cfg : @CFG α ν}
  {a : α} {input : Array α}
  : result_bounded cfg (Leaf <$> terminal' (tag := tag cfg) a) input := by
  exact result_bounded_of_lower_result_bounded
    (lower_terminal'_result_bounded
      (cfg := cfg) (a := a) (input := input))

omit [Fintype ν] in
lemma lower_failure_empty
  (cfg : @CFG α ν)
  {input : Array α} {memo : MemoData (tag cfg) List} {start : ℕ} :
    (((⊥ : ParserM (tag := tag cfg) α List (ParseTree cfg)).lower start)
      memo input).1.isEmpty := by
  simp [Bot.bot, ParserM.lift, ParserM.lower]
  unfold Parser.failure Parser.bind Parser.bindRun Parser.bindContinue
    Parser.bindActions
  simp [ReaderT.pure, Pure.pure, instMonadMStateT,
    Functor.map, hashMap_emptyWithCapacity_toList_eq_nil]

omit [Fintype ν] in
lemma not_mem_lower_traverse_cons_failure
  {cfg : @CFG α ν}
  {tail : List (ParserM (tag := tag cfg) α List (ParseTree cfg))}
  {memo : MemoData (tag cfg) List} {input : Array α}
  {start end_ : ℕ} {result_head : ParseTree cfg}
  {result_tail : List (ParseTree cfg)}
  (h :
    result_head :: result_tail ∈
      (((List.traverse id
        ((⊥ : ParserM (tag := tag cfg) α List (ParseTree cfg)) :: tail)).lower start)
        memo input).1.getD end_ []) :
    False := by
  have h_lift :
      result_head :: result_tail ∈
        (((List.traverse id
          ((ParserM.lift Parser.failure :
            ParserM (tag := tag cfg) α List (ParseTree cfg)) :: tail)).lower start)
          memo input).1.getD end_ [] := by
    simpa [Bot.bot] using h
  obtain ⟨split, _memo_tail, h_head, _h_tail⟩ :=
    mem_lower_traverse_cons_lift_exists_head_tail
      (tag := tag cfg) (β := α)
      (p := (Parser.failure :
        Parser (tag := tag cfg) α List (ParseTree cfg)))
      (tail := tail)
      (memo := memo) (input := input)
      (start := start) (end_pos := end_) h_lift
  simp [Parser.failure, ReaderT.pure, Pure.pure] at h_head

set_option linter.unusedSectionVars false in
theorem mem_lower_traverse_cons_memoize_exists_head_tail
  {cfg : @CFG α ν}
  (counter : Counter ν)
  (g : ((t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg)) →
      (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  (n : ν)
  (tail : List (ParserM (tag := tag cfg) α List (ParseTree cfg)))
  (memo : MemoData (tag cfg) List) (input : Array α)
  (start end_ : ℕ)
  {result_head : ParseTree cfg} {result_tail : List (ParseTree cfg)}
  (h :
    result_head :: result_tail ∈
      (((List.traverse id ((memoize counter g n) :: tail)).lower start)
        memo input).1.getD end_ []) :
    ∃ split memo_tail,
      result_head ∈ (((memoize counter g n).lower start) memo input).1.getD split [] ∧
      result_tail ∈
        (((List.traverse id tail).lower split) memo_tail input).1.getD end_ [] := by
  by_cases h_counter : counter[n]? = some 0
  · have h_fail :
      result_head :: result_tail ∈
        (((List.traverse id
          ((⊥ : ParserM (tag := tag cfg) α List (ParseTree cfg)) :: tail)).lower start)
          memo input).1.getD end_ [] := by
        simpa [memoize, h_counter] using h
    exact False.elim (not_mem_lower_traverse_cons_failure (cfg := cfg) h_fail)
  · have h_lift :
      result_head :: result_tail ∈
        (((List.traverse id
          ((ParserM.lift
            (memoizeStep counter g n
              (fun fuel => memoize (counter.dec n fuel) g)) :
              ParserM (tag := tag cfg) α List (ParseTree cfg)) :: tail)).lower start)
          memo input).1.getD end_ [] := by
        simpa [memoize, h_counter] using h
    obtain ⟨split, memo_tail, h_head_step, h_tail⟩ :=
      mem_lower_traverse_cons_lift_exists_head_tail
        (tag := tag cfg) (β := α)
        (p := memoizeStep counter g n
          (fun fuel => memoize (counter.dec n fuel) g))
        (tail := tail)
        (memo := memo) (input := input)
        (start := start) (end_pos := end_)
        h_lift
    refine ⟨split, memo_tail, ?_, h_tail⟩
    have h_head_lift :
        result_head ∈
          (((ParserM.lift
            (memoizeStep counter g n
              (fun fuel => memoize (counter.dec n fuel) g))).lower start)
            memo input).1.getD split [] := by
        exact mem_lower_lift_of_mem
          (tag := tag cfg) (β := α)
          (p := memoizeStep counter g n
            (fun fuel => memoize (counter.dec n fuel) g))
          (memo := memo) (input := input)
          (start := start) (end_pos := split)
          (x := result_head) h_head_step
    simpa [memoize, h_counter] using h_head_lift

set_option linter.unusedSectionVars false in
theorem mem_lower_traverse_cons_memoize_exists_head_tail_wf
  {cfg : @CFG α ν}
  (counter : Counter ν)
  (g : ((t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg)) →
      (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  (n : ν)
  (tail : List (ParserM (tag := tag cfg) α List (ParseTree cfg)))
  (memo : MemoData (tag cfg) List) (input : Array α)
  (start end_ : ℕ)
  {result_head : ParseTree cfg} {result_tail : List (ParseTree cfg)}
  (h_step_memo :
    ∀ start,
      ∀ memo : MemoData (tag cfg) List,
        memo_wellFormed cfg input memo →
        memo_wellFormed cfg input
          (((memoizeStep counter g n
            (fun fuel => memoize (counter.dec n fuel) g) start)
            memo input).2.val))
  (h_tail_memo :
    lower_memo_wellFormed cfg (List.traverse id tail) input)
  (h_memo : memo_wellFormed cfg input memo)
  (h :
    result_head :: result_tail ∈
      (((List.traverse id ((memoize counter g n) :: tail)).lower start)
        memo input).1.getD end_ []) :
    ∃ split memo_tail,
      memo_wellFormed cfg input memo_tail ∧
      result_head ∈ (((memoize counter g n).lower start) memo input).1.getD split [] ∧
      result_tail ∈
        (((List.traverse id tail).lower split) memo_tail input).1.getD end_ [] := by
  by_cases h_counter : counter[n]? = some 0
  · have h_fail :
      result_head :: result_tail ∈
        (((List.traverse id
          ((⊥ : ParserM (tag := tag cfg) α List (ParseTree cfg)) :: tail)).lower start)
          memo input).1.getD end_ [] := by
        simpa [memoize, h_counter] using h
    exact False.elim (not_mem_lower_traverse_cons_failure (cfg := cfg) h_fail)
  · let step : Parser (tag := tag cfg) α List (ParseTree cfg) :=
      memoizeStep counter g n
        (fun fuel => memoize (counter.dec n fuel) g)
    have h_lift :
      result_head :: result_tail ∈
        (((List.traverse id
          ((ParserM.lift step :
            ParserM (tag := tag cfg) α List (ParseTree cfg)) :: tail)).lower start)
          memo input).1.getD end_ [] := by
        simpa [memoize, h_counter, step] using h
    rw [List.traverse, seq_eq_bind] at h_lift
    simp at h_lift
    change result_head :: result_tail ∈
      (((ParserM.Bind step
        (fun a => List.cons a <$> List.traverse id tail)).lower start)
        memo input).1.getD end_ [] at h_lift
    obtain ⟨prePairs, postPairs, split, values, preValues, postValues, a,
      h_toList, h_values, h_action⟩ :=
      mem_lower_bind_exists_action_split_mem
        (tag := tag cfg) (β := α)
        (p := step)
        (k := fun a => List.cons a <$> List.traverse id tail)
        (memo := memo) (input := input)
        (start := start) (end_pos := end_)
        (x := result_head :: result_tail) h_lift
    obtain ⟨h_head_eq, h_tail⟩ :=
      mem_lower_cons_map_exists_of_cons
        (tag := tag cfg) (β := α)
        (tail := tail) (head_result := a)
        (memo := _) (input := input)
        (split := split) (end_pos := end_)
        h_action
    have h_get : ((step start) memo input).1[split]? = some values := by
      rw [← Std.HashMap.mem_toList_iff_getElem?_eq_some]
      rw [h_toList]
      simp
    have h_a_mem : a ∈ ((step start) memo input).1.getD split [] := by
      rw [Std.HashMap.getD_eq_getD_getElem?]
      simp [h_get, h_values]
    let memoPrefix : MemoData (tag cfg) List :=
      ((Traversable.foldl joinUnderCache
        (List.foldl (Traversable.foldl joinUnderCache)
          (pure Std.HashMap.emptyWithCapacity)
          (List.map
            (fun pair : ℕ × List (ParseTree cfg) =>
              match pair with
              | (j, values) =>
                  List.map
                    (fun a => ((List.cons a <$> List.traverse id tail).lower j))
                    values)
            prePairs))
        (List.map
          (fun a => ((List.cons a <$> List.traverse id tail).lower split))
          preValues))
        (↑((step start) memo input).2) input).2.val
    have h_prefix_wf : memo_wellFormed cfg input memoPrefix := by
      have h_k_memo :
          ∀ a,
            lower_memo_wellFormed cfg
              (List.cons a <$> List.traverse id tail) input := by
        intro a
        exact lower_map_memo_wellFormed
          (cfg := cfg)
          (p := List.traverse id tail)
          (f := List.cons a)
          h_tail_memo
      simpa [memoPrefix, step] using
        (bind_action_prefix_memo_wellFormed
          (cfg := cfg) (input := input)
          (p := step)
          (k := fun a => List.cons a <$> List.traverse id tail)
          (prePairs := prePairs) (preValues := preValues)
          (split := split) (start := start)
          (memo := memo)
          (by
            intro start memo h_memo
            exact h_step_memo start memo h_memo)
          h_k_memo h_memo)
    refine ⟨split, memoPrefix, h_prefix_wf, ?_, ?_⟩
    · have h_head_lift :
          a ∈
            (((ParserM.lift step :
              ParserM (tag := tag cfg) α List (ParseTree cfg)).lower start)
              memo input).1.getD split [] := by
        exact mem_lower_lift_of_mem
          (tag := tag cfg) (β := α)
          (p := step)
          (memo := memo) (input := input)
          (start := start) (end_pos := split)
          (x := a) h_a_mem
      have h_result_head_lift :
          result_head ∈
            (((ParserM.lift step :
              ParserM (tag := tag cfg) α List (ParseTree cfg)).lower start)
              memo input).1.getD split [] := by
        simpa [h_head_eq] using h_head_lift
      simpa [memoize, h_counter, step] using h_result_head_lift
    · simpa [memoPrefix] using h_tail

omit [Fintype ν] in
theorem lower_failure_sound
  (cfg : @CFG α ν) (n : ν) (input : Array α) :
    lower_sound cfg n ⊥ input := by
  unfold lower_sound
  intro memo _h_memo start end_ _h_bound tree
  simp [Std.HashMap.getD_of_isEmpty, lower_failure_empty cfg]

omit [Fintype ν] in
theorem lower_failure_result_sound
  (cfg : @CFG α ν) (n : ν) (input : Array α) :
    lower_result_sound cfg n ⊥ input := by
  unfold lower_result_sound
  intro memo _h_memo start end_ tree
  simp [Std.HashMap.getD_of_isEmpty, lower_failure_empty cfg]

omit [Fintype ν] in
theorem lower_failure_bounded
  (cfg : @CFG α ν) (input : Array α) :
    lower_result_bounded cfg ⊥ input := by
  unfold lower_result_bounded
  intro memo _h_memo start end_ _h_start tree
  simp [Std.HashMap.getD_of_isEmpty, lower_failure_empty cfg]

omit [Fintype ν] in
theorem lower_failure_memo_wellFormed
  (cfg : @CFG α ν) (input : Array α) :
    lower_memo_wellFormed cfg (⊥ : ParserM (tag := tag cfg) α List (ParseTree cfg)) input := by
  unfold lower_memo_wellFormed
  intro memo h_memo start
  simp [Bot.bot, ParserM.lift, ParserM.lower]
  unfold Parser.failure Parser.bind Parser.bindRun Parser.bindContinue
    Parser.bindActions
  simp [ReaderT.pure, Pure.pure, instMonadMStateT,
    Functor.map, hashMap_emptyWithCapacity_toList_eq_nil]
  exact h_memo

omit [Fintype ν] in
lemma failure_empty (cfg : @CFG α ν) {start : ℕ} : (runParser (tag := tag cfg) (⊥ : ParserM α μ (ParseTree cfg)) input start).1.isEmpty := by
  simp [Bot.bot, runParser, ReaderT.run, MStateT.run, ParserM.lift, ParserM.lower]
  unfold Parser.failure Parser.bind Parser.bindRun Parser.bindContinue Parser.bindActions
  simp [ReaderT.pure, Pure.pure, instMonadMStateT,
    Bifunctor.snd, Functor.map, hashMap_emptyWithCapacity_toList_eq_nil]
  change (Std.HashMap.emptyWithCapacity : Std.HashMap ℕ (μ (ParseTree cfg))).isEmpty = true
  simp

omit [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
theorem failure_sound (cfg : @CFG α ν) (n : ν) (input : Array α) : sound cfg n ⊥ input
  :=
  sound_of_lower_sound (lower_failure_sound cfg n input)

omit [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
theorem failure_bounded (cfg : @CFG α ν) (input : Array α) : result_bounded cfg ⊥ input
  :=
  result_bounded_of_lower_result_bounded (lower_failure_bounded cfg input)

set_option linter.unusedSectionVars false in
theorem lower_result_sound_memoize
  {cfg : @CFG α ν} {input : Array α}
  (counter : Counter ν)
  (g : ((t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg)) →
      (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  {n : ν}
  (h_compute :
    ∀ memo : MemoData (tag cfg) List,
      memo_wellFormed cfg input memo →
      ∀ start : ℕ,
      ∀ _h_no_cache :
        (memo.getD n ⊥)[(Counter.toKey counter, start)]? = none,
        resultMap_sound cfg n
          ((((g (memoize (counter.dec n (input.size - start + 1)) g)
              n).lower start)
            memo input).1)) :
    lower_result_sound cfg n (memoize counter g n) input := by
  by_cases h_counter : counter[n]? = some 0
  · simpa [memoize, h_counter] using
      lower_failure_result_sound cfg n input
  · simpa [memoize, h_counter] using
      lower_result_sound_memoizeStep_lift
        (cfg := cfg) (input := input)
        (counter := counter) (g := g)
        (next := fun fuel => memoize (counter.dec n fuel) g)
        (n := n) h_compute

set_option linter.unusedSectionVars false in
theorem lower_result_bounded_memoize
  {cfg : @CFG α ν} {input : Array α}
  (counter : Counter ν)
  (g : ((t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg)) →
      (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  {n : ν}
  (h_compute :
    ∀ memo : MemoData (tag cfg) List,
      memo_wellFormed cfg input memo →
      ∀ start : ℕ,
      ∀ _h_no_cache :
        (memo.getD n ⊥)[(Counter.toKey counter, start)]? = none,
        resultMap_bounded cfg input start
          ((((g (memoize (counter.dec n (input.size - start + 1)) g)
              n).lower start)
            memo input).1)) :
    lower_result_bounded cfg (memoize counter g n) input := by
  by_cases h_counter : counter[n]? = some 0
  · simpa [memoize, h_counter] using
      lower_failure_bounded cfg input
  · simpa [memoize, h_counter] using
      lower_result_bounded_memoizeStep_lift
        (cfg := cfg) (input := input)
        (counter := counter) (g := g)
        (next := fun fuel => memoize (counter.dec n fuel) g)
        (n := n) h_compute

set_option linter.unusedSectionVars false in
theorem lower_memo_wellFormed_memoize
  {cfg : @CFG α ν} {input : Array α}
  (counter : Counter ν)
  (g : ((t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg)) →
      (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  {n : ν}
  (h_compute :
    ∀ memo : MemoData (tag cfg) List,
      memo_wellFormed cfg input memo →
      ∀ start : ℕ,
      ∀ _h_no_cache :
        (memo.getD n ⊥)[(Counter.toKey counter, start)]? = none,
        memo_wellFormed cfg input
            ((((g (memoize (counter.dec n (input.size - start + 1)) g)
                n).lower start)
              memo input).2.val) ∧
          resultMap_sound cfg n
            ((((g (memoize (counter.dec n (input.size - start + 1)) g)
                n).lower start)
              memo input).1) ∧
          resultMap_bounded cfg input start
            ((((g (memoize (counter.dec n (input.size - start + 1)) g)
                n).lower start)
              memo input).1)) :
    lower_memo_wellFormed cfg (memoize counter g n) input := by
  by_cases h_counter : counter[n]? = some 0
  · simpa [memoize, h_counter] using
      lower_failure_memo_wellFormed cfg input
  · simpa [memoize, h_counter] using
      lower_memo_wellFormed_memoizeStep_lift
        (cfg := cfg) (input := input)
        (counter := counter) (g := g)
        (next := fun fuel => memoize (counter.dec n fuel) g)
        (n := n) h_compute

set_option linter.unusedSectionVars false in
theorem lower_result_bounded_generated_traverse_memoize
  {cfg : @CFG α ν}
  (counter : Counter ν)
  (g : ((t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg)) →
      (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  (rule : List (Symbol α ν)) (input : Array α)
  (h_step_bounds :
    ∀ n,
      ∀ memo : MemoData (tag cfg) List,
        memo_wellFormed cfg input memo →
        ∀ start : ℕ,
        ∀ _h_no_cache :
          (memo.getD n ⊥)[(Counter.toKey counter, start)]? = none,
          resultMap_bounded cfg input start
            ((((g (memoize (counter.dec n (input.size - start + 1)) g)
                n).lower start)
              memo input).1))
  (h_step_memo :
    ∀ n start,
      ∀ memo : MemoData (tag cfg) List,
        memo_wellFormed cfg input memo →
        memo_wellFormed cfg input
          (((memoizeStep counter g n
            (fun fuel => memoize (counter.dec n fuel) g) start)
            memo input).2.val)) :
    ∀ memo : MemoData (tag cfg) List,
      memo_wellFormed cfg input memo →
      ∀ start end_ : ℕ,
      start ≤ input.size →
      ∀ result,
        result ∈
          (((List.traverse id
            (rule.map (generatedListSymbolParser cfg counter g))).lower start)
            memo input).1.getD end_ [] →
        start ≤ end_ ∧ end_ ≤ input.size := by
  induction rule with
  | nil =>
      intro memo _h_memo start end_ h_start result h_mem
      have h_return := (mem_lower_return_iff
        (tag := tag cfg) (β := α)
        (a := ([] : List (ParseTree cfg))) (x := result)
        (memo := memo) (input := input)
        (start := start) (end_pos := end_)).mp (by
          simpa [List.traverse] using h_mem)
      cases h_return.1
      exact ⟨le_rfl, h_start⟩
  | cons sym rest ih =>
      cases sym with
      | term a =>
          intro memo h_memo start end_ h_start result h_mem
          cases result with
          | nil =>
              have h_len := mem_lower_traverse_preserves_length
                (tag := tag cfg) (β := α)
                (xs :=
                  (Leaf (cfg := cfg) <$> terminal' (tag := tag cfg) a) ::
                    rest.map (generatedListSymbolParser cfg counter g))
                (memo := memo) (input := input)
                (start := start) (end_pos := end_)
                (result := ([] : List (ParseTree cfg)))
                (by simpa [generatedListSymbolParser] using h_mem)
              simp at h_len
          | cons result_head result_tail =>
              have h_tail_memo :
                  lower_memo_wellFormed cfg
                    (List.traverse id
                      (rest.map (generatedListSymbolParser cfg counter g)))
                    input :=
                lower_memo_wellFormed_generated_traverse_memoize
                  (cfg := cfg) counter g rest input h_step_memo
              obtain ⟨_h_head_eq, _h_head_mem, h_start_succ,
                memo_tail, h_memo_tail, h_tail_mem⟩ :=
                mem_lower_traverse_cons_terminal_exists_tail_wf
                  (cfg := cfg) (a := a)
                  (tail := rest.map (generatedListSymbolParser cfg counter g))
                  (memo := memo) (input := input)
                  (start := start) (end_ := end_)
                  (result_head := result_head) (result_tail := result_tail)
                  h_tail_memo h_memo
                  (by simpa [generatedListSymbolParser] using h_mem)
              have h_tail_bounds :=
                ih memo_tail h_memo_tail (start + 1) end_
                  h_start_succ result_tail h_tail_mem
              exact ⟨Nat.le_trans (Nat.le_succ start) h_tail_bounds.1,
                h_tail_bounds.2⟩
      | nonterm n =>
          intro memo h_memo start end_ h_start result h_mem
          cases result with
          | nil =>
              have h_len := mem_lower_traverse_preserves_length
                (tag := tag cfg) (β := α)
                (xs :=
                  (memoize counter g n) ::
                    rest.map (generatedListSymbolParser cfg counter g))
                (memo := memo) (input := input)
                (start := start) (end_pos := end_)
                (result := ([] : List (ParseTree cfg)))
                (by simpa [generatedListSymbolParser] using h_mem)
              simp at h_len
          | cons result_head result_tail =>
              have h_tail_memo :
                  lower_memo_wellFormed cfg
                    (List.traverse id
                      (rest.map (generatedListSymbolParser cfg counter g)))
                    input :=
                lower_memo_wellFormed_generated_traverse_memoize
                  (cfg := cfg) counter g rest input h_step_memo
              obtain ⟨split, memo_tail, h_memo_tail,
                h_head_mem, h_tail_mem⟩ :=
                mem_lower_traverse_cons_memoize_exists_head_tail_wf
                  (cfg := cfg) counter g n
                  (tail := rest.map (generatedListSymbolParser cfg counter g))
                  (memo := memo) (input := input)
                  (start := start) (end_ := end_)
                  (result_head := result_head) (result_tail := result_tail)
                  (by
                    intro start memo h_memo
                    exact h_step_memo n start memo h_memo)
                  h_tail_memo h_memo
                  (by simpa [generatedListSymbolParser] using h_mem)
              have h_head_bounds :=
                (lower_result_bounded_memoize
                  (cfg := cfg) (input := input)
                  counter g
                  (n := n)
                  (by
                    intro memo h_memo start h_no_cache
                    exact h_step_bounds n memo h_memo start h_no_cache))
                  memo h_memo start split h_start result_head h_head_mem
              have h_tail_bounds :=
                ih memo_tail h_memo_tail split end_ h_head_bounds.2
                  result_tail h_tail_mem
              exact ⟨Nat.le_trans h_head_bounds.1 h_tail_bounds.1,
                h_tail_bounds.2⟩

set_option linter.unusedSectionVars false in
theorem lower_valid_pairs_generated_traverse_memoize
  {cfg : @CFG α ν}
  (counter : Counter ν)
  (g : ((t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg)) →
      (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  (rule : List (Symbol α ν)) (input : Array α)
  (h_step_sound :
    ∀ n,
      ∀ memo : MemoData (tag cfg) List,
        memo_wellFormed cfg input memo →
        ∀ start : ℕ,
        ∀ _h_no_cache :
          (memo.getD n ⊥)[(Counter.toKey counter, start)]? = none,
          resultMap_sound cfg n
            ((((g (memoize (counter.dec n (input.size - start + 1)) g)
                n).lower start)
              memo input).1))
  (h_step_memo :
    ∀ n start,
      ∀ memo : MemoData (tag cfg) List,
        memo_wellFormed cfg input memo →
        memo_wellFormed cfg input
          (((memoizeStep counter g n
            (fun fuel => memoize (counter.dec n fuel) g) start)
            memo input).2.val)) :
    ∀ memo : MemoData (tag cfg) List,
      memo_wellFormed cfg input memo →
      ∀ start end_ : ℕ,
      ∀ subtrees,
        subtrees ∈
          (((List.traverse id
            (rule.map (generatedListSymbolParser cfg counter g))).lower start)
            memo input).1.getD end_ [] →
        rule.length = subtrees.length ∧
          ∀ pair, pair ∈ List.zip rule subtrees →
            validChildPair (cfg := cfg) pair := by
  induction rule with
  | nil =>
      intro memo _h_memo start end_ subtrees h_mem
      have h_return := (mem_lower_return_iff
        (tag := tag cfg) (β := α)
        (a := ([] : List (ParseTree cfg))) (x := subtrees)
        (memo := memo) (input := input)
        (start := start) (end_pos := end_)).mp (by
          simpa [List.traverse] using h_mem)
      cases h_return.2
      constructor
      · simp
      · intro pair h_pair
        simp at h_pair
  | cons sym rest ih =>
      cases sym with
      | term a =>
          intro memo h_memo start end_ subtrees h_mem
          cases subtrees with
          | nil =>
              have h_len := mem_lower_traverse_preserves_length
                (tag := tag cfg) (β := α)
                (xs :=
                  (Leaf (cfg := cfg) <$> terminal' (tag := tag cfg) a) ::
                    rest.map (generatedListSymbolParser cfg counter g))
                (memo := memo) (input := input)
                (start := start) (end_pos := end_)
                (result := ([] : List (ParseTree cfg)))
                (by simpa [generatedListSymbolParser] using h_mem)
              simp at h_len
          | cons result_head result_tail =>
              have h_tail_memo :
                  lower_memo_wellFormed cfg
                    (List.traverse id
                      (rest.map (generatedListSymbolParser cfg counter g)))
                    input :=
                lower_memo_wellFormed_generated_traverse_memoize
                  (cfg := cfg) counter g rest input h_step_memo
              obtain ⟨h_head_eq, _h_head_mem, _h_start_succ,
                memo_tail, h_memo_tail, h_tail_mem⟩ :=
                mem_lower_traverse_cons_terminal_exists_tail_wf
                  (cfg := cfg) (a := a)
                  (tail := rest.map (generatedListSymbolParser cfg counter g))
                  (memo := memo) (input := input)
                  (start := start) (end_ := end_)
                  (result_head := result_head) (result_tail := result_tail)
                  h_tail_memo h_memo
                  (by simpa [generatedListSymbolParser] using h_mem)
              obtain ⟨h_tail_len, h_tail_pairs⟩ :=
                ih memo_tail h_memo_tail (start + 1) end_
                  result_tail h_tail_mem
              constructor
              · simp [h_tail_len]
              · intro pair h_pair
                simp at h_pair
                cases h_pair with
                | inl h_head_pair =>
                    cases h_head_pair
                    simp [validChildPair, h_head_eq]
                | inr h_tail_pair =>
                    exact h_tail_pairs pair h_tail_pair
      | nonterm n =>
          intro memo h_memo start end_ subtrees h_mem
          cases subtrees with
          | nil =>
              have h_len := mem_lower_traverse_preserves_length
                (tag := tag cfg) (β := α)
                (xs :=
                  (memoize counter g n) ::
                    rest.map (generatedListSymbolParser cfg counter g))
                (memo := memo) (input := input)
                (start := start) (end_pos := end_)
                (result := ([] : List (ParseTree cfg)))
                (by simpa [generatedListSymbolParser] using h_mem)
              simp at h_len
          | cons result_head result_tail =>
              have h_tail_memo :
                  lower_memo_wellFormed cfg
                    (List.traverse id
                      (rest.map (generatedListSymbolParser cfg counter g)))
                    input :=
                lower_memo_wellFormed_generated_traverse_memoize
                  (cfg := cfg) counter g rest input h_step_memo
              obtain ⟨split, memo_tail, h_memo_tail,
                h_head_mem, h_tail_mem⟩ :=
                mem_lower_traverse_cons_memoize_exists_head_tail_wf
                  (cfg := cfg) counter g n
                  (tail := rest.map (generatedListSymbolParser cfg counter g))
                  (memo := memo) (input := input)
                  (start := start) (end_ := end_)
                  (result_head := result_head) (result_tail := result_tail)
                  (by
                    intro start memo h_memo
                    exact h_step_memo n start memo h_memo)
                  h_tail_memo h_memo
                  (by simpa [generatedListSymbolParser] using h_mem)
              have h_head_sound :=
                (lower_result_sound_memoize
                  (cfg := cfg) (input := input)
                  counter g
                  (n := n)
                  (by
                    intro memo h_memo start h_no_cache
                    exact h_step_sound n memo h_memo start h_no_cache))
                  memo h_memo start split result_head h_head_mem
              obtain ⟨h_tail_len, h_tail_pairs⟩ :=
                ih memo_tail h_memo_tail split end_
                  result_tail h_tail_mem
              constructor
              · simp [h_tail_len]
              · intro pair h_pair
                simp at h_pair
                cases h_pair with
                | inl h_head_pair =>
                    cases h_head_pair
                    cases result_head with
                    | Leaf b =>
                        simp [ParseTree.root] at h_head_sound
                    | Node n' rule' children' =>
                        obtain ⟨h_valid, h_root⟩ := h_head_sound
                        have h_eq : n = n' := by
                          simpa [ParseTree.root] using h_root.symm
                        exact ⟨h_eq, h_valid⟩
                | inr h_tail_pair =>
                    exact h_tail_pairs pair h_tail_pair

set_option linter.unusedSectionVars false in
theorem lower_generated_rule_branch_result_sound_bounded_memoize
  {cfg : @CFG α ν}
  (counter : Counter ν)
  (g : ((t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg)) →
      (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  {n : ν} (rule : {rule // rule ∈ cfg.rules n}) (input : Array α)
  (h_step_sound :
    ∀ n,
      ∀ memo : MemoData (tag cfg) List,
        memo_wellFormed cfg input memo →
        ∀ start : ℕ,
        ∀ _h_no_cache :
          (memo.getD n ⊥)[(Counter.toKey counter, start)]? = none,
          resultMap_sound cfg n
            ((((g (memoize (counter.dec n (input.size - start + 1)) g)
                n).lower start)
              memo input).1))
  (h_step_bounds :
    ∀ n,
      ∀ memo : MemoData (tag cfg) List,
        memo_wellFormed cfg input memo →
        ∀ start : ℕ,
        ∀ _h_no_cache :
          (memo.getD n ⊥)[(Counter.toKey counter, start)]? = none,
          resultMap_bounded cfg input start
            ((((g (memoize (counter.dec n (input.size - start + 1)) g)
                n).lower start)
              memo input).1))
  (h_step_memo :
    ∀ n start,
      ∀ memo : MemoData (tag cfg) List,
        memo_wellFormed cfg input memo →
        memo_wellFormed cfg input
          (((memoizeStep counter g n
            (fun fuel => memoize (counter.dec n fuel) g) start)
            memo input).2.val)) :
    lower_result_sound cfg n
        (Node n rule <$>
          List.traverse id
            (rule.val.map (generatedListSymbolParser cfg counter g))) input ∧
      lower_result_bounded cfg
        (Node n rule <$>
          List.traverse id
            (rule.val.map (generatedListSymbolParser cfg counter g))) input ∧
      lower_memo_wellFormed cfg
        (Node n rule <$>
          List.traverse id
            (rule.val.map (generatedListSymbolParser cfg counter g))) input := by
  refine ⟨?_, ?_, ?_⟩
  · exact lower_rule_branch_result_sound_of_traverse_pairs
      (cfg := cfg) (n := n) (rule := rule)
      (mkParser := generatedListSymbolParser cfg counter g)
      (input := input)
      (by
        intro memo h_memo start end_ subtrees h_mem
        exact lower_valid_pairs_generated_traverse_memoize
          (cfg := cfg) counter g rule.val input
          h_step_sound h_step_memo
          memo h_memo start end_ subtrees h_mem)
  · exact lower_rule_branch_result_bounded_of_traverse
      (cfg := cfg) (n := n) (rule := rule)
      (mkParser := generatedListSymbolParser cfg counter g)
      (input := input)
      (by
        intro memo h_memo start end_ h_start subtrees h_mem
        exact lower_result_bounded_generated_traverse_memoize
          (cfg := cfg) counter g rule.val input
          h_step_bounds h_step_memo
          memo h_memo start end_ h_start subtrees h_mem)
  · exact lower_rule_branch_memo_wellFormed_of_traverse
      (cfg := cfg) (n := n) (rule := rule)
      (mkParser := generatedListSymbolParser cfg counter g)
      (input := input)
      (lower_memo_wellFormed_generated_traverse_memoize
        (cfg := cfg) counter g rule.val input h_step_memo)

set_option linter.unusedSectionVars false in
theorem lower_result_bounded_generated_traverse_memoize_guarded
  {cfg : @CFG α ν}
  (counter : Counter ν)
  (g : ((t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg)) →
      (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  (rule : List (Symbol α ν)) (input : Array α)
  (h_body :
    ∀ n,
      counter[n]? ≠ some 0 →
      ∀ memo : MemoData (tag cfg) List,
        memo_wellFormed cfg input memo →
        ∀ start : ℕ,
        ∀ _h_no_cache :
          (memo.getD n ⊥)[(Counter.toKey counter, start)]? = none,
          memo_wellFormed cfg input
              ((((g (memoize (counter.dec n (input.size - start + 1)) g)
                  n).lower start)
                memo input).2.val) ∧
            resultMap_sound cfg n
              ((((g (memoize (counter.dec n (input.size - start + 1)) g)
                  n).lower start)
                memo input).1) ∧
            resultMap_bounded cfg input start
              ((((g (memoize (counter.dec n (input.size - start + 1)) g)
                  n).lower start)
                memo input).1)) :
    ∀ memo : MemoData (tag cfg) List,
      memo_wellFormed cfg input memo →
      ∀ start end_ : ℕ,
      start ≤ input.size →
      ∀ result,
        result ∈
          (((List.traverse id
            (rule.map (generatedListSymbolParser cfg counter g))).lower start)
            memo input).1.getD end_ [] →
        start ≤ end_ ∧ end_ ≤ input.size := by
  have h_step_memo :
      ∀ n,
        counter[n]? ≠ some 0 →
        ∀ start,
        ∀ memo : MemoData (tag cfg) List,
          memo_wellFormed cfg input memo →
          memo_wellFormed cfg input
            (((memoizeStep counter g n
              (fun fuel => memoize (counter.dec n fuel) g) start)
              memo input).2.val) := by
    intro n h_counter start memo h_memo
    exact memo_wellFormed_memoizeStep
      (cfg := cfg) (input := input)
      (counter := counter) (g := g)
      (next := fun fuel => memoize (counter.dec n fuel) g)
      (n := n) (memo := memo) (start := start)
      h_memo
      (fun h_no_cache => h_body n h_counter memo h_memo start h_no_cache)
  induction rule with
  | nil =>
      intro memo _h_memo start end_ h_start result h_mem
      have h_return := (mem_lower_return_iff
        (tag := tag cfg) (β := α)
        (a := ([] : List (ParseTree cfg))) (x := result)
        (memo := memo) (input := input)
        (start := start) (end_pos := end_)).mp (by
          simpa [List.traverse] using h_mem)
      cases h_return.1
      exact ⟨le_rfl, h_start⟩
  | cons sym rest ih =>
      cases sym with
      | term a =>
          intro memo h_memo start end_ h_start result h_mem
          cases result with
          | nil =>
              have h_len := mem_lower_traverse_preserves_length
                (tag := tag cfg) (β := α)
                (xs :=
                  (Leaf (cfg := cfg) <$> terminal' (tag := tag cfg) a) ::
                    rest.map (generatedListSymbolParser cfg counter g))
                (memo := memo) (input := input)
                (start := start) (end_pos := end_)
                (result := ([] : List (ParseTree cfg)))
                (by simpa [generatedListSymbolParser] using h_mem)
              simp at h_len
          | cons result_head result_tail =>
              have h_tail_memo :
                  lower_memo_wellFormed cfg
                    (List.traverse id
                      (rest.map (generatedListSymbolParser cfg counter g)))
                    input :=
                lower_memo_wellFormed_generated_traverse_memoize_guarded
                  (cfg := cfg) counter g rest input h_step_memo
              obtain ⟨_h_head_eq, _h_head_mem, h_start_succ,
                memo_tail, h_memo_tail, h_tail_mem⟩ :=
                mem_lower_traverse_cons_terminal_exists_tail_wf
                  (cfg := cfg) (a := a)
                  (tail := rest.map (generatedListSymbolParser cfg counter g))
                  (memo := memo) (input := input)
                  (start := start) (end_ := end_)
                  (result_head := result_head) (result_tail := result_tail)
                  h_tail_memo h_memo
                  (by simpa [generatedListSymbolParser] using h_mem)
              have h_tail_bounds :=
                ih memo_tail h_memo_tail (start + 1) end_
                  h_start_succ result_tail h_tail_mem
              exact ⟨Nat.le_trans (Nat.le_succ start) h_tail_bounds.1,
                h_tail_bounds.2⟩
      | nonterm n =>
          intro memo h_memo start end_ h_start result h_mem
          cases result with
          | nil =>
              have h_len := mem_lower_traverse_preserves_length
                (tag := tag cfg) (β := α)
                (xs :=
                  (memoize counter g n) ::
                    rest.map (generatedListSymbolParser cfg counter g))
                (memo := memo) (input := input)
                (start := start) (end_pos := end_)
                (result := ([] : List (ParseTree cfg)))
                (by simpa [generatedListSymbolParser] using h_mem)
              simp at h_len
          | cons result_head result_tail =>
              by_cases h_counter : counter[n]? = some 0
              · have h_fail :
                    result_head :: result_tail ∈
                      (((List.traverse id
                        ((⊥ : ParserM (tag := tag cfg) α List (ParseTree cfg)) ::
                          rest.map (generatedListSymbolParser cfg counter g))).lower start)
                        memo input).1.getD end_ [] := by
                  simpa [generatedListSymbolParser, memoize, h_counter] using h_mem
                exact False.elim (not_mem_lower_traverse_cons_failure
                  (cfg := cfg) h_fail)
              · have h_tail_memo :
                    lower_memo_wellFormed cfg
                      (List.traverse id
                        (rest.map (generatedListSymbolParser cfg counter g)))
                      input :=
                  lower_memo_wellFormed_generated_traverse_memoize_guarded
                    (cfg := cfg) counter g rest input h_step_memo
                obtain ⟨split, memo_tail, h_memo_tail,
                  h_head_mem, h_tail_mem⟩ :=
                  mem_lower_traverse_cons_memoize_exists_head_tail_wf
                    (cfg := cfg) counter g n
                    (tail := rest.map (generatedListSymbolParser cfg counter g))
                    (memo := memo) (input := input)
                    (start := start) (end_ := end_)
                    (result_head := result_head) (result_tail := result_tail)
                    (h_step_memo n h_counter)
                    h_tail_memo h_memo
                    (by simpa [generatedListSymbolParser] using h_mem)
                have h_head_bounds :=
                  (lower_result_bounded_memoize
                    (cfg := cfg) (input := input)
                    counter g
                    (n := n)
                    (by
                      intro memo h_memo start h_no_cache
                      exact (h_body n h_counter memo h_memo start h_no_cache).2.2))
                    memo h_memo start split h_start result_head h_head_mem
                have h_tail_bounds :=
                  ih memo_tail h_memo_tail split end_ h_head_bounds.2
                    result_tail h_tail_mem
                exact ⟨Nat.le_trans h_head_bounds.1 h_tail_bounds.1,
                  h_tail_bounds.2⟩

set_option linter.unusedSectionVars false in
theorem lower_valid_pairs_generated_traverse_memoize_guarded
  {cfg : @CFG α ν}
  (counter : Counter ν)
  (g : ((t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg)) →
      (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  (rule : List (Symbol α ν)) (input : Array α)
  (h_body :
    ∀ n,
      counter[n]? ≠ some 0 →
      ∀ memo : MemoData (tag cfg) List,
        memo_wellFormed cfg input memo →
        ∀ start : ℕ,
        ∀ _h_no_cache :
          (memo.getD n ⊥)[(Counter.toKey counter, start)]? = none,
          memo_wellFormed cfg input
              ((((g (memoize (counter.dec n (input.size - start + 1)) g)
                  n).lower start)
                memo input).2.val) ∧
            resultMap_sound cfg n
              ((((g (memoize (counter.dec n (input.size - start + 1)) g)
                  n).lower start)
                memo input).1) ∧
            resultMap_bounded cfg input start
              ((((g (memoize (counter.dec n (input.size - start + 1)) g)
                  n).lower start)
                memo input).1)) :
    ∀ memo : MemoData (tag cfg) List,
      memo_wellFormed cfg input memo →
      ∀ start end_ : ℕ,
      ∀ subtrees,
        subtrees ∈
          (((List.traverse id
            (rule.map (generatedListSymbolParser cfg counter g))).lower start)
            memo input).1.getD end_ [] →
        rule.length = subtrees.length ∧
          ∀ pair, pair ∈ List.zip rule subtrees →
            validChildPair (cfg := cfg) pair := by
  have h_step_memo :
      ∀ n,
        counter[n]? ≠ some 0 →
        ∀ start,
        ∀ memo : MemoData (tag cfg) List,
          memo_wellFormed cfg input memo →
          memo_wellFormed cfg input
            (((memoizeStep counter g n
              (fun fuel => memoize (counter.dec n fuel) g) start)
              memo input).2.val) := by
    intro n h_counter start memo h_memo
    exact memo_wellFormed_memoizeStep
      (cfg := cfg) (input := input)
      (counter := counter) (g := g)
      (next := fun fuel => memoize (counter.dec n fuel) g)
      (n := n) (memo := memo) (start := start)
      h_memo
      (fun h_no_cache => h_body n h_counter memo h_memo start h_no_cache)
  induction rule with
  | nil =>
      intro memo _h_memo start end_ subtrees h_mem
      have h_return := (mem_lower_return_iff
        (tag := tag cfg) (β := α)
        (a := ([] : List (ParseTree cfg))) (x := subtrees)
        (memo := memo) (input := input)
        (start := start) (end_pos := end_)).mp (by
          simpa [List.traverse] using h_mem)
      cases h_return.2
      constructor
      · simp
      · intro pair h_pair
        simp at h_pair
  | cons sym rest ih =>
      cases sym with
      | term a =>
          intro memo h_memo start end_ subtrees h_mem
          cases subtrees with
          | nil =>
              have h_len := mem_lower_traverse_preserves_length
                (tag := tag cfg) (β := α)
                (xs :=
                  (Leaf (cfg := cfg) <$> terminal' (tag := tag cfg) a) ::
                    rest.map (generatedListSymbolParser cfg counter g))
                (memo := memo) (input := input)
                (start := start) (end_pos := end_)
                (result := ([] : List (ParseTree cfg)))
                (by simpa [generatedListSymbolParser] using h_mem)
              simp at h_len
          | cons result_head result_tail =>
              have h_tail_memo :
                  lower_memo_wellFormed cfg
                    (List.traverse id
                      (rest.map (generatedListSymbolParser cfg counter g)))
                    input :=
                lower_memo_wellFormed_generated_traverse_memoize_guarded
                  (cfg := cfg) counter g rest input h_step_memo
              obtain ⟨h_head_eq, _h_head_mem, _h_start_succ,
                memo_tail, h_memo_tail, h_tail_mem⟩ :=
                mem_lower_traverse_cons_terminal_exists_tail_wf
                  (cfg := cfg) (a := a)
                  (tail := rest.map (generatedListSymbolParser cfg counter g))
                  (memo := memo) (input := input)
                  (start := start) (end_ := end_)
                  (result_head := result_head) (result_tail := result_tail)
                  h_tail_memo h_memo
                  (by simpa [generatedListSymbolParser] using h_mem)
              obtain ⟨h_tail_len, h_tail_pairs⟩ :=
                ih memo_tail h_memo_tail (start + 1) end_
                  result_tail h_tail_mem
              constructor
              · simp [h_tail_len]
              · intro pair h_pair
                simp at h_pair
                cases h_pair with
                | inl h_head_pair =>
                    cases h_head_pair
                    simp [validChildPair, h_head_eq]
                | inr h_tail_pair =>
                    exact h_tail_pairs pair h_tail_pair
      | nonterm n =>
          intro memo h_memo start end_ subtrees h_mem
          cases subtrees with
          | nil =>
              have h_len := mem_lower_traverse_preserves_length
                (tag := tag cfg) (β := α)
                (xs :=
                  (memoize counter g n) ::
                    rest.map (generatedListSymbolParser cfg counter g))
                (memo := memo) (input := input)
                (start := start) (end_pos := end_)
                (result := ([] : List (ParseTree cfg)))
                (by simpa [generatedListSymbolParser] using h_mem)
              simp at h_len
          | cons result_head result_tail =>
              by_cases h_counter : counter[n]? = some 0
              · have h_fail :
                    result_head :: result_tail ∈
                      (((List.traverse id
                        ((⊥ : ParserM (tag := tag cfg) α List (ParseTree cfg)) ::
                          rest.map (generatedListSymbolParser cfg counter g))).lower start)
                        memo input).1.getD end_ [] := by
                  simpa [generatedListSymbolParser, memoize, h_counter] using h_mem
                exact False.elim (not_mem_lower_traverse_cons_failure
                  (cfg := cfg) h_fail)
              · have h_tail_memo :
                    lower_memo_wellFormed cfg
                      (List.traverse id
                        (rest.map (generatedListSymbolParser cfg counter g)))
                      input :=
                  lower_memo_wellFormed_generated_traverse_memoize_guarded
                    (cfg := cfg) counter g rest input h_step_memo
                obtain ⟨split, memo_tail, h_memo_tail,
                  h_head_mem, h_tail_mem⟩ :=
                  mem_lower_traverse_cons_memoize_exists_head_tail_wf
                    (cfg := cfg) counter g n
                    (tail := rest.map (generatedListSymbolParser cfg counter g))
                    (memo := memo) (input := input)
                    (start := start) (end_ := end_)
                    (result_head := result_head) (result_tail := result_tail)
                    (h_step_memo n h_counter)
                    h_tail_memo h_memo
                    (by simpa [generatedListSymbolParser] using h_mem)
                have h_head_sound :=
                  (lower_result_sound_memoize
                    (cfg := cfg) (input := input)
                    counter g
                    (n := n)
                    (by
                      intro memo h_memo start h_no_cache
                      exact (h_body n h_counter memo h_memo start h_no_cache).2.1))
                    memo h_memo start split result_head h_head_mem
                obtain ⟨h_tail_len, h_tail_pairs⟩ :=
                  ih memo_tail h_memo_tail split end_
                    result_tail h_tail_mem
                constructor
                · simp [h_tail_len]
                · intro pair h_pair
                  simp at h_pair
                  cases h_pair with
                  | inl h_head_pair =>
                      cases h_head_pair
                      cases result_head with
                      | Leaf b =>
                          simp [ParseTree.root] at h_head_sound
                      | Node n' rule' children' =>
                          obtain ⟨h_valid, h_root⟩ := h_head_sound
                          have h_eq : n = n' := by
                            simpa [ParseTree.root] using h_root.symm
                          exact ⟨h_eq, h_valid⟩
                  | inr h_tail_pair =>
                      exact h_tail_pairs pair h_tail_pair

set_option linter.unusedSectionVars false in
theorem lower_generated_rule_branch_result_sound_bounded_memoize_guarded
  {cfg : @CFG α ν}
  (counter : Counter ν)
  (g : ((t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg)) →
      (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  {n : ν} (rule : {rule // rule ∈ cfg.rules n}) (input : Array α)
  (h_body :
    ∀ n,
      counter[n]? ≠ some 0 →
      ∀ memo : MemoData (tag cfg) List,
        memo_wellFormed cfg input memo →
        ∀ start : ℕ,
        ∀ _h_no_cache :
          (memo.getD n ⊥)[(Counter.toKey counter, start)]? = none,
          memo_wellFormed cfg input
              ((((g (memoize (counter.dec n (input.size - start + 1)) g)
                  n).lower start)
                memo input).2.val) ∧
            resultMap_sound cfg n
              ((((g (memoize (counter.dec n (input.size - start + 1)) g)
                  n).lower start)
                memo input).1) ∧
            resultMap_bounded cfg input start
              ((((g (memoize (counter.dec n (input.size - start + 1)) g)
                  n).lower start)
                memo input).1)) :
    lower_result_sound cfg n
        (Node n rule <$>
          List.traverse id
            (rule.val.map (generatedListSymbolParser cfg counter g))) input ∧
      lower_result_bounded cfg
        (Node n rule <$>
          List.traverse id
            (rule.val.map (generatedListSymbolParser cfg counter g))) input ∧
      lower_memo_wellFormed cfg
        (Node n rule <$>
          List.traverse id
            (rule.val.map (generatedListSymbolParser cfg counter g))) input := by
  have h_step_memo :
      ∀ n,
        counter[n]? ≠ some 0 →
        ∀ start,
        ∀ memo : MemoData (tag cfg) List,
          memo_wellFormed cfg input memo →
          memo_wellFormed cfg input
            (((memoizeStep counter g n
              (fun fuel => memoize (counter.dec n fuel) g) start)
              memo input).2.val) := by
    intro n h_counter start memo h_memo
    exact memo_wellFormed_memoizeStep
      (cfg := cfg) (input := input)
      (counter := counter) (g := g)
      (next := fun fuel => memoize (counter.dec n fuel) g)
      (n := n) (memo := memo) (start := start)
      h_memo
      (fun h_no_cache => h_body n h_counter memo h_memo start h_no_cache)
  refine ⟨?_, ?_, ?_⟩
  · exact lower_rule_branch_result_sound_of_traverse_pairs
      (cfg := cfg) (n := n) (rule := rule)
      (mkParser := generatedListSymbolParser cfg counter g)
      (input := input)
      (by
        intro memo h_memo start end_ subtrees h_mem
        exact lower_valid_pairs_generated_traverse_memoize_guarded
          (cfg := cfg) counter g rule.val input
          h_body
          memo h_memo start end_ subtrees h_mem)
  · exact lower_rule_branch_result_bounded_of_traverse
      (cfg := cfg) (n := n) (rule := rule)
      (mkParser := generatedListSymbolParser cfg counter g)
      (input := input)
      (by
        intro memo h_memo start end_ h_start subtrees h_mem
        exact lower_result_bounded_generated_traverse_memoize_guarded
          (cfg := cfg) counter g rule.val input
          h_body
          memo h_memo start end_ h_start subtrees h_mem)
  · exact lower_rule_branch_memo_wellFormed_of_traverse
      (cfg := cfg) (n := n) (rule := rule)
      (mkParser := generatedListSymbolParser cfg counter g)
      (input := input)
      (lower_memo_wellFormed_generated_traverse_memoize_guarded
        (cfg := cfg) counter g rule.val input h_step_memo)

omit [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
/-- State-aware soundness for parser joins.

This follows `Parser.orElse` directly: the right branch is checked in the memo
state produced by the left branch, not in `startState`.
-/
theorem sound_of_sup_sound_after_left
  (cfg : @CFG α ν) (n : ν)
  (p q : ParserM (tag := tag cfg) α List (ParseTree cfg)) (input : Array α)
  (h_p : sound cfg n p input)
  (h_q_after :
    ∀ start end_ : ℕ,
      ∀ _h_bound : start ≤ end_ ∧ end_ ≤ input.size,
      ∀ tree ∈
        ((q.lower start)
          (↑(((p.lower start) startState input).2)) input).1.getD end_ [],
        tree.Valid ∧ tree.root = Symbol.nonterm n) :
    sound cfg n (p ⊔ q) input := by
  unfold sound at *
  intro start end_ h_bound tree h_mem
  have h_or :=
    (mem_runParser_sup_iff_after_left
      (tag := tag cfg) (β := α)
      p q input start end_ tree).mp h_mem
  cases h_or with
  | inl h_left =>
      exact h_p start end_ h_bound tree h_left
  | inr h_right =>
      exact h_q_after start end_ h_bound tree h_right

omit [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
/-- State-aware lower-level soundness for parser joins.

Unlike `sound_of_sup_sound`, this checks the right branch in the memo state
produced by the left branch.
-/
theorem lower_sound_of_sup_sound_after_left
  (cfg : @CFG α ν) (n : ν)
  (p q : ParserM (tag := tag cfg) α List (ParseTree cfg)) (input : Array α)
  (h_p : lower_sound cfg n p input)
  (h_p_memo : lower_memo_wellFormed cfg p input)
  (h_q : lower_sound cfg n q input) :
    lower_sound cfg n (p ⊔ q) input := by
  unfold lower_sound at *
  intro memo h_memo start end_ h_bound tree h_mem
  have h_or :=
    (mem_lower_sup_iff_after_left
      (tag := tag cfg) (β := α)
      p q memo input start end_ tree).mp h_mem
  cases h_or with
  | inl h_left =>
      exact h_p memo h_memo start end_ h_bound tree h_left
  | inr h_right =>
      exact h_q
        (↑(((p.lower start) memo input).2))
        (h_p_memo memo h_memo start)
        start end_ h_bound tree h_right

omit [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
/-- State-aware lower-level direct result soundness for parser joins.

This is the cache-oriented version of `lower_sound_of_sup_sound_after_left`:
it does not require a span bound premise before proving validity/root
correctness of a result.
-/
theorem lower_result_sound_of_sup_sound_after_left
  (cfg : @CFG α ν) (n : ν)
  (p q : ParserM (tag := tag cfg) α List (ParseTree cfg)) (input : Array α)
  (h_p : lower_result_sound cfg n p input)
  (h_p_memo : lower_memo_wellFormed cfg p input)
  (h_q : lower_result_sound cfg n q input) :
    lower_result_sound cfg n (p ⊔ q) input := by
  unfold lower_result_sound at *
  intro memo h_memo start end_ tree h_mem
  have h_or :=
    (mem_lower_sup_iff_after_left
      (tag := tag cfg) (β := α)
      p q memo input start end_ tree).mp h_mem
  cases h_or with
  | inl h_left =>
      exact h_p memo h_memo start end_ tree h_left
  | inr h_right =>
      exact h_q
        (↑(((p.lower start) memo input).2))
        (h_p_memo memo h_memo start)
        start end_ tree h_right

omit [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
/-- State-aware bounds preservation for parser joins.

The right branch is checked in the state produced by the left branch, matching
`Parser.orElse`.
-/
theorem bounded_of_sup_bounded_after_left
  (cfg : @CFG α ν)
  (p q : ParserM (tag := tag cfg) α List (ParseTree cfg)) (input : Array α)
  (h_p : result_bounded cfg p input)
  (h_q_after :
    ∀ start end_ : ℕ,
      start ≤ input.size →
      ∀ tree,
        tree ∈
          ((q.lower start)
            (↑(((p.lower start) startState input).2)) input).1.getD end_ [] →
        start ≤ end_ ∧ end_ ≤ input.size) :
    result_bounded cfg (p ⊔ q) input := by
  unfold result_bounded at *
  intro start end_ h_start tree h_mem
  have h_or :=
    (mem_runParser_sup_iff_after_left
      (tag := tag cfg) (β := α)
      p q input start end_ tree).mp h_mem
  cases h_or with
  | inl h_left =>
      exact h_p start end_ h_start tree h_left
  | inr h_right =>
      exact h_q_after start end_ h_start tree h_right

omit [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
/-- State-aware lower-level bounds preservation for parser joins.

The right branch is checked in the memo state produced by the left branch,
matching the executable `Parser.orElse`.
-/
theorem lower_bounded_of_sup_bounded_after_left
  (cfg : @CFG α ν)
  (p q : ParserM (tag := tag cfg) α List (ParseTree cfg)) (input : Array α)
  (h_p : lower_result_bounded cfg p input)
  (h_p_memo : lower_memo_wellFormed cfg p input)
  (h_q : lower_result_bounded cfg q input) :
    lower_result_bounded cfg (p ⊔ q) input := by
  unfold lower_result_bounded at *
  intro memo h_memo start end_ h_start tree h_mem
  have h_or :=
    (mem_lower_sup_iff_after_left
      (tag := tag cfg) (β := α)
      p q memo input start end_ tree).mp h_mem
  cases h_or with
  | inl h_left =>
      exact h_p memo h_memo start end_ h_start tree h_left
  | inr h_right =>
      exact h_q
        (↑(((p.lower start) memo input).2))
        (h_p_memo memo h_memo start)
        start end_ h_start tree h_right

omit [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
theorem lower_result_sound_bounded_memo_of_foldl_sup
  (cfg : @CFG α ν) (n : ν)
  (parsers : List (ParserM (tag := tag cfg) α List (ParseTree cfg)))
  (acc : ParserM (tag := tag cfg) α List (ParseTree cfg))
  (input : Array α)
  (h_acc :
    lower_result_sound cfg n acc input ∧
    lower_result_bounded cfg acc input ∧
    lower_memo_wellFormed cfg acc input)
  (h_parsers :
    ∀ p ∈ parsers,
      lower_result_sound cfg n p input ∧
      lower_result_bounded cfg p input ∧
      lower_memo_wellFormed cfg p input) :
    lower_result_sound cfg n
        (parsers.foldl ParserM.instMaxOfTraversableOfDecidableEq.max acc)
        input ∧
      lower_result_bounded cfg
        (parsers.foldl ParserM.instMaxOfTraversableOfDecidableEq.max acc)
        input ∧
      lower_memo_wellFormed cfg
        (parsers.foldl ParserM.instMaxOfTraversableOfDecidableEq.max acc)
        input := by
  induction parsers generalizing acc with
  | nil =>
      simpa using h_acc
  | cons head tail ih =>
      simp [List.foldl]
      have h_head := h_parsers head (by simp)
      have h_acc_head :
          lower_result_sound cfg n (acc ⊔ head) input ∧
          lower_result_bounded cfg (acc ⊔ head) input ∧
          lower_memo_wellFormed cfg (acc ⊔ head) input := by
        refine ⟨?_, ?_, ?_⟩
        · exact lower_result_sound_of_sup_sound_after_left
            cfg n acc head input h_acc.1 h_acc.2.2 h_head.1
        · exact lower_bounded_of_sup_bounded_after_left
            cfg acc head input h_acc.2.1 h_acc.2.2 h_head.2.1
        · exact lower_sup_memo_wellFormed
            (cfg := cfg) (input := input)
            acc head h_acc.2.2 h_head.2.2
      exact ih (acc := acc ⊔ head) h_acc_head
        (by
          intro p h_p
          exact h_parsers p (by simp [h_p]))

set_option linter.unusedSectionVars false in
theorem lower_gen'_result_sound_bounded_memoize
  {cfg : @CFG α ν}
  (counter : Counter ν)
  (g : ((t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg)) →
      (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  (n : ν) (input : Array α)
  (h_body :
    ∀ n,
      counter[n]? ≠ some 0 →
      ∀ memo : MemoData (tag cfg) List,
        memo_wellFormed cfg input memo →
        ∀ start : ℕ,
        ∀ _h_no_cache :
          (memo.getD n ⊥)[(Counter.toKey counter, start)]? = none,
          memo_wellFormed cfg input
              ((((g (memoize (counter.dec n (input.size - start + 1)) g)
                  n).lower start)
                memo input).2.val) ∧
            resultMap_sound cfg n
              ((((g (memoize (counter.dec n (input.size - start + 1)) g)
                  n).lower start)
                memo input).1) ∧
            resultMap_bounded cfg input start
              ((((g (memoize (counter.dec n (input.size - start + 1)) g)
                  n).lower start)
                memo input).1)) :
    lower_result_sound cfg n (gen' (μ := List) cfg (memoize counter g) n) input ∧
      lower_result_bounded cfg (gen' (μ := List) cfg (memoize counter g) n) input ∧
      lower_memo_wellFormed cfg (gen' (μ := List) cfg (memoize counter g) n) input := by
  let parseSym : Symbol α ν → ParserM (tag := tag cfg) α List (ParseTree cfg) :=
    generatedListSymbolParser cfg counter g
  let parseRule : {rule // rule ∈ cfg.rules n} →
      ParserM (tag := tag cfg) α List (ParseTree cfg) :=
    fun rule => Node n rule <$> List.traverse id (rule.val.map parseSym)
  have h_fold :=
    lower_result_sound_bounded_memo_of_foldl_sup
      cfg n ((cfg.rules n).attach.map parseRule)
      (⊥ : ParserM (tag := tag cfg) α List (ParseTree cfg))
      input
      ⟨lower_failure_result_sound cfg n input,
        lower_failure_bounded cfg input,
        lower_failure_memo_wellFormed cfg input⟩
      (by
        intro p h_p
        rw [List.mem_map] at h_p
        rcases h_p with ⟨rule, _h_rule_mem, rfl⟩
        exact lower_generated_rule_branch_result_sound_bounded_memoize_guarded
          (cfg := cfg) counter g rule input h_body)
  simpa [gen', parseSym, parseRule, generatedListSymbolParser] using h_fold

omit [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
theorem lower_complete_of_sup_left
  (cfg : @CFG α ν)
  (p q : ParserM (tag := tag cfg) α List (ParseTree cfg))
  (memo : MemoData (tag cfg) List) (input : Array α)
  {start end_ : ℕ} {tree : ParseTree cfg}
  (h_mem : tree ∈ ((p.lower start) memo input).1.getD end_ []) :
    tree ∈ (((p ⊔ q).lower start) memo input).1.getD end_ [] := by
  exact (mem_lower_sup_iff_after_left
    (tag := tag cfg) (β := α)
    p q memo input start end_ tree).mpr (Or.inl h_mem)

omit [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
theorem lower_complete_of_sup_right_after_left
  (cfg : @CFG α ν)
  (p q : ParserM (tag := tag cfg) α List (ParseTree cfg))
  (memo : MemoData (tag cfg) List) (input : Array α)
  {start end_ : ℕ} {tree : ParseTree cfg}
  (h_mem :
    tree ∈
      ((q.lower start)
        (↑(((p.lower start) memo input).2)) input).1.getD end_ []) :
    tree ∈ (((p ⊔ q).lower start) memo input).1.getD end_ [] := by
  exact (mem_lower_sup_iff_after_left
    (tag := tag cfg) (β := α)
    p q memo input start end_ tree).mpr (Or.inr h_mem)

omit [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
theorem complete_of_sup_left
  (cfg : @CFG α ν)
  (p q : ParserM (tag := tag cfg) α List (ParseTree cfg))
  (input : Array α) {start end_ : ℕ} {tree : ParseTree cfg}
  (h_mem : tree ∈ (runParser p input start).1.getD end_ []) :
    tree ∈ (runParser (p ⊔ q) input start).1.getD end_ [] := by
  exact (mem_runParser_sup_iff_after_left
    (tag := tag cfg) (β := α)
    p q input start end_ tree).mpr (Or.inl h_mem)

omit [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
theorem complete_of_sup_right
  (cfg : @CFG α ν)
  (p q : ParserM (tag := tag cfg) α List (ParseTree cfg))
  (input : Array α) {start end_ : ℕ} {tree : ParseTree cfg}
  (h_mem : tree ∈ (runParser q input start).1.getD end_ []) :
    tree ∈ (runParser (p ⊔ q) input start).1.getD end_ [] := by
  have h := runParser_sup_eq_sup_runParser p q input start
  have h' := Std.HashMap.EquivQuot.getD_eq (s := SemilatticeAlt.setoid) (k := end_) (fallback := []) h
  simp [SemilatticeAlt.setoid, List.memSetoid] at h'
  dsimp [Subset, List.Subset] at *
  apply h'.2
  dsimp [Max.max]
  by_cases h_p_contains_end_ : end_ ∈ (runParser p input start).1
  · by_cases h_q_contains_end_ : end_ ∈ (runParser q input start).1
    · have h_union := Std.HashMap.unionSup_getD_both
        (s := SemilatticeAlt.setoid)
        (semi := List.instSemilatticeAlt.instSemilatticeoidInstSetoid)
        h_p_contains_end_ h_q_contains_end_
      simp [SemilatticeAlt.setoid, List.memSetoid, Subset, List.Subset] at h_union
      apply h_union.2
      simp [Max.max, SemilatticeAlt.orElse]
      right
      simpa [Std.HashMap.getElem_eq_getD (fallback := [])] using h_mem
    ·
      simp [Std.HashMap.getD_eq_fallback h_q_contains_end_] at h_mem
  · have h_union := Std.HashMap.unionSup_getD_of_not_contains
      (s := SemilatticeAlt.setoid)
      (semi := List.instSemilatticeAlt.instSemilatticeoidInstSetoid)
      (fallback := []) (runParser p input start).1 (runParser q input start).1
      h_p_contains_end_
    simp [SemilatticeAlt.setoid, List.memSetoid, Subset, List.Subset] at h_union
    exact h_union.2 h_mem

omit [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
theorem complete_of_sup_right_after_left
  (cfg : @CFG α ν)
  (p q : ParserM (tag := tag cfg) α List (ParseTree cfg))
  (input : Array α) {start end_ : ℕ} {tree : ParseTree cfg}
  (h_mem :
    tree ∈
      ((q.lower start)
        (↑(((p.lower start) startState input).2)) input).1.getD end_ []) :
    tree ∈ (runParser (p ⊔ q) input start).1.getD end_ [] := by
  exact (mem_runParser_sup_iff_after_left
    (tag := tag cfg) (β := α)
    p q input start end_ tree).mpr (Or.inr h_mem)

omit [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
theorem lower_complete_of_foldl_sup_acc
  (cfg : @CFG α ν)
  (parsers : List (ParserM (tag := tag cfg) α List (ParseTree cfg)))
  (acc : ParserM (tag := tag cfg) α List (ParseTree cfg))
  (memo : MemoData (tag cfg) List) (input : Array α)
  {start end_ : ℕ} {tree : ParseTree cfg}
  (h_mem : tree ∈ ((acc.lower start) memo input).1.getD end_ []) :
    tree ∈
      (((parsers.foldl ParserM.instMaxOfTraversableOfDecidableEq.max acc).lower start)
        memo input).1.getD end_ [] := by
  induction parsers generalizing acc with
  | nil =>
      simpa using h_mem
  | cons head tail ih =>
      simp [List.foldl]
      apply ih
      exact lower_complete_of_sup_left cfg acc head memo input h_mem

omit [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
theorem lower_complete_of_foldl_sup_head_after_left
  (cfg : @CFG α ν)
  (tail : List (ParserM (tag := tag cfg) α List (ParseTree cfg)))
  (acc head : ParserM (tag := tag cfg) α List (ParseTree cfg))
  (memo : MemoData (tag cfg) List) (input : Array α)
  {start end_ : ℕ} {tree : ParseTree cfg}
  (h_mem :
    tree ∈
      ((head.lower start)
        (↑(((acc.lower start) memo input).2)) input).1.getD end_ []) :
    tree ∈
      (((tail.foldl ParserM.instMaxOfTraversableOfDecidableEq.max (acc ⊔ head)).lower start)
        memo input).1.getD end_ [] := by
  exact lower_complete_of_foldl_sup_acc
    (cfg := cfg) (parsers := tail) (acc := acc ⊔ head)
    (memo := memo) (input := input)
    (lower_complete_of_sup_right_after_left cfg acc head memo input h_mem)

omit [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
theorem lower_complete_of_foldl_sup_mem_after_prefix
  (cfg : @CFG α ν)
  (pre suffix : List (ParserM (tag := tag cfg) α List (ParseTree cfg)))
  (acc p : ParserM (tag := tag cfg) α List (ParseTree cfg))
  (memo : MemoData (tag cfg) List) (input : Array α)
  {start end_ : ℕ} {tree : ParseTree cfg}
  (h_mem :
    tree ∈
      ((p.lower start)
        (↑((((pre.foldl ParserM.instMaxOfTraversableOfDecidableEq.max acc).lower start)
          memo input).2)) input).1.getD end_ []) :
    tree ∈
      ((((pre ++ p :: suffix).foldl ParserM.instMaxOfTraversableOfDecidableEq.max acc).lower start)
        memo input).1.getD end_ [] := by
  rw [List.foldl_append]
  simp [List.foldl]
  exact lower_complete_of_foldl_sup_head_after_left
    (cfg := cfg) (tail := suffix)
    (acc := pre.foldl ParserM.instMaxOfTraversableOfDecidableEq.max acc)
    (head := p) (memo := memo) (input := input) h_mem

omit [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
theorem complete_of_foldl_sup_mem_after_prefix
  (cfg : @CFG α ν)
  (pre suffix : List (ParserM (tag := tag cfg) α List (ParseTree cfg)))
  (acc p : ParserM (tag := tag cfg) α List (ParseTree cfg))
  (input : Array α) {start end_ : ℕ} {tree : ParseTree cfg}
  (h_mem :
    tree ∈
      ((p.lower start)
        (↑((((pre.foldl ParserM.instMaxOfTraversableOfDecidableEq.max acc).lower start)
          startState input).2)) input).1.getD end_ []) :
    tree ∈
      (runParser
        ((pre ++ p :: suffix).foldl ParserM.instMaxOfTraversableOfDecidableEq.max acc)
        input start).1.getD end_ [] := by
  rw [runParser_fst_eq_lower]
  exact lower_complete_of_foldl_sup_mem_after_prefix
    (cfg := cfg) (pre := pre) (suffix := suffix)
    (acc := acc) (p := p)
    (memo := startState) (input := input) h_mem

omit [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
theorem complete_of_foldl_sup_acc
  (cfg : @CFG α ν)
  (parsers : List (ParserM (tag := tag cfg) α List (ParseTree cfg)))
  (acc : ParserM (tag := tag cfg) α List (ParseTree cfg))
  (input : Array α) {start end_ : ℕ} {tree : ParseTree cfg}
  (h_mem : tree ∈ (runParser acc input start).1.getD end_ []) :
    tree ∈
      (runParser
        (parsers.foldl ParserM.instMaxOfTraversableOfDecidableEq.max acc)
        input start).1.getD end_ [] := by
  induction parsers generalizing acc with
  | nil =>
      simpa using h_mem
  | cons head tail ih =>
      simp [List.foldl]
      apply ih
      exact complete_of_sup_left cfg acc head input h_mem

omit [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
theorem complete_of_foldl_sup_mem
  (cfg : @CFG α ν)
  (parsers : List (ParserM (tag := tag cfg) α List (ParseTree cfg)))
  (acc p : ParserM (tag := tag cfg) α List (ParseTree cfg))
  (input : Array α) {start end_ : ℕ} {tree : ParseTree cfg}
  (h_p : p ∈ parsers)
  (h_mem : tree ∈ (runParser p input start).1.getD end_ []) :
    tree ∈
      (runParser
        (parsers.foldl ParserM.instMaxOfTraversableOfDecidableEq.max acc)
        input start).1.getD end_ [] := by
  induction parsers generalizing acc with
  | nil =>
      simp at h_p
  | cons head tail ih =>
      simp at h_p
      cases h_p with
      | inl h_eq =>
          have h_head_mem : tree ∈ (runParser head input start).1.getD end_ [] := by
            simpa [h_eq] using h_mem
          simp [List.foldl]
          apply complete_of_foldl_sup_acc cfg tail (acc ⊔ head) input
          exact complete_of_sup_right cfg acc head input h_head_mem
      | inr h_tail =>
          simp [List.foldl]
          exact ih (acc := acc ⊔ head) h_tail

omit [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
theorem gen'_rule_complete
  (cfg : @CFG α ν)
  (recur : ν → ParserM (tag := tag cfg) α List (ParseTree cfg))
  {n : ν} {rule : List (Symbol α ν)}
  (h_rule : rule ∈ cfg.rules n)
  {input : Array α} {start end_ : ℕ} {subtrees : List (ParseTree cfg)}
  (h_children :
    TraverseCompleteWitness cfg input
      (rule.map fun sym =>
        match sym with
        | Symbol.term a => Leaf <$> terminal' (tag := tag cfg) a
        | Symbol.nonterm n => recur n)
      start subtrees end_) :
    Node (cfg := cfg) n ⟨rule, h_rule⟩ subtrees ∈
      (runParser (tag := tag cfg) (gen' (μ := List) cfg recur n)
        input start).1.getD end_ [] := by
  unfold gen'
  let parseSym : Symbol α ν → ParserM (tag := tag cfg) α List (ParseTree cfg) :=
    fun sym =>
      match sym with
      | Symbol.term a => Leaf <$> terminal' (tag := tag cfg) a
      | Symbol.nonterm n => recur n
  let parseRule : {rule // rule ∈ cfg.rules n} → ParserM (tag := tag cfg) α List (ParseTree cfg) :=
    fun rule =>
      Node n rule <$> List.traverse id (List.map parseSym rule)
  have h_branch :
      Node (cfg := cfg) n ⟨rule, h_rule⟩ subtrees ∈
        (runParser (tag := tag cfg) (parseRule ⟨rule, h_rule⟩)
          input start).1.getD end_ [] := by
    simpa [parseRule, parseSym] using
      (runParser_rule_branch_complete (cfg := cfg) (n := n)
        (rule := rule) h_rule
        (mkParser := parseSym)
        (input := input) (start := start) (end_ := end_)
        (subtrees := subtrees)
        (by simpa [parseSym] using h_children))
  have h_parseRule_mem :
      parseRule ⟨rule, h_rule⟩ ∈ (cfg.rules n).attach.map parseRule := by
    exact List.mem_map.mpr ⟨⟨rule, h_rule⟩, by simp, rfl⟩
  simpa [parseRule, parseSym] using
    (complete_of_foldl_sup_mem cfg
      ((cfg.rules n).attach.map parseRule)
      (⊥ : ParserM (tag := tag cfg) α List (ParseTree cfg))
      (parseRule ⟨rule, h_rule⟩)
      input h_parseRule_mem h_branch)

omit [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
theorem gen'_rule_complete_of_child_witness
  (cfg : @CFG α ν)
  (recur : ν → ParserM (tag := tag cfg) α List (ParseTree cfg))
  {n : ν} {rule : List (Symbol α ν)}
  (h_rule : rule ∈ cfg.rules n)
  {input : Array α} {start end_ : ℕ} {subtrees : List (ParseTree cfg)}
  (h_children : GeneratedChildWitness cfg recur input rule subtrees start end_) :
    Node (cfg := cfg) n ⟨rule, h_rule⟩ subtrees ∈
      (runParser (tag := tag cfg) (gen' (μ := List) cfg recur n)
        input start).1.getD end_ [] := by
  exact gen'_rule_complete cfg recur h_rule
    (generatedChildWitness_to_traverse (cfg := cfg) h_children)

omit [Monad μ] [SemilatticeAlt μ] [Traversable μ] in
lemma generatedChildWitness_of_admissible_valid_pairs
  {cfg : @CFG α ν}
  {input : Array α}
  {seen : List (SpanVisit ν)} {counter : Counter ν}
  {rule : List (Symbol α ν)} {children : List (ParseTree cfg)}
  {pre post : List α}
  (h_adm :
    AdmissibleForestWith cfg input seen counter children pre.length)
  (h_len : rule.length = children.length)
  (h_valid :
    ∀ pair, pair ∈ List.zip rule children → validChildPair (cfg := cfg) pair)
  (h_input : input.toList = pre ++ forestLeaves (cfg := cfg) children ++ post)
  (h_recur :
    ∀ {childN : ν} {rule' : {rule // rule ∈ cfg.rules childN}}
      {grandchildren : List (ParseTree cfg)} {pre' post' : List α},
      Node (cfg := cfg) childN rule' grandchildren ∈ children →
      AdmissibleTreeWith cfg input seen counter
        (Node (cfg := cfg) childN rule' grandchildren) pre'.length →
      (Node (cfg := cfg) childN rule' grandchildren).Valid →
      input.toList =
        pre' ++ (Node (cfg := cfg) childN rule' grandchildren).leaves ++ post' →
      Node (cfg := cfg) childN rule' grandchildren ∈
        (runParser (tag := tag cfg)
          (memoize counter (gen' (μ := List) cfg) childN)
          input pre'.length).1.getD
          (pre'.length +
            (Node (cfg := cfg) childN rule' grandchildren).leaves.length) []) :
    GeneratedChildWitness cfg
      (memoize counter (gen' (μ := List) cfg)) input rule children pre.length
      (pre.length + (forestLeaves (cfg := cfg) children).length) := by
  induction rule generalizing children pre with
  | nil =>
      cases children with
      | nil =>
          simpa using GeneratedChildWitness.nil
            (cfg := cfg)
            (recur := memoize counter (gen' (μ := List) cfg))
            (input := input) pre.length
      | cons child tail =>
          simp at h_len
  | cons sym rest ih =>
      cases children with
      | nil =>
          simp at h_len
      | cons child tail =>
          obtain ⟨h_child_adm, h_tail_adm⟩ :=
            admissible_forest_cons_inv (cfg := cfg) h_adm
          have h_len_tail : rest.length = tail.length := by
            simpa using h_len
          have h_tail_valid :
              ∀ pair, pair ∈ List.zip rest tail → validChildPair (cfg := cfg) pair := by
            intro pair h_pair
            exact h_valid pair (by simp [h_pair])
          have h_input_tail :
              input.toList =
                (pre ++ child.leaves) ++ forestLeaves (cfg := cfg) tail ++ post := by
            simpa [forestLeaves, List.append_assoc] using h_input
          have h_tail_adm' :
              AdmissibleForestWith cfg input seen counter tail
                (pre ++ child.leaves).length := by
            simpa [List.length_append] using h_tail_adm
          have h_recur_tail :
              ∀ {childN : ν} {rule' : {rule // rule ∈ cfg.rules childN}}
                {grandchildren : List (ParseTree cfg)} {pre' post' : List α},
                Node (cfg := cfg) childN rule' grandchildren ∈ tail →
                AdmissibleTreeWith cfg input seen counter
                  (Node (cfg := cfg) childN rule' grandchildren) pre'.length →
                (Node (cfg := cfg) childN rule' grandchildren).Valid →
                input.toList =
                  pre' ++
                    (Node (cfg := cfg) childN rule' grandchildren).leaves ++
                    post' →
                Node (cfg := cfg) childN rule' grandchildren ∈
                  (runParser (tag := tag cfg)
                    (memoize counter (gen' (μ := List) cfg) childN)
                    input pre'.length).1.getD
                    (pre'.length +
                      (Node (cfg := cfg) childN rule' grandchildren).leaves.length) [] := by
            intro childN rule' grandchildren pre' post' h_mem h_adm_child
              h_valid_child h_input_child
            exact h_recur (by simp [h_mem]) h_adm_child h_valid_child h_input_child
          cases sym with
          | term a =>
              cases child with
              | Leaf b =>
                  have h_ab : a = b := by
                    have h_head :=
                      h_valid (Symbol.term a, Leaf (cfg := cfg) b) (by simp)
                    simpa [validChildPair] using h_head
                  cases h_ab
                  have h_term : input[pre.length]? = some a := by
                    apply array_getElem?_of_toList_eq_append_singleton
                    simpa [forestLeaves, ParseTree.leaves, List.append_assoc]
                      using h_input
                  have h_tail :=
                    ih h_tail_adm' h_len_tail h_tail_valid h_input_tail h_recur_tail
                  exact GeneratedChildWitness.term h_term
                    (by
                      simpa [forestLeaves, ParseTree.leaves, List.length_append,
                        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
                        using h_tail)
              | Node n' rule' grandchildren =>
                  have h_false : False := by
                    have h_head := h_valid
                      (Symbol.term a, Node (cfg := cfg) n' rule' grandchildren) (by simp)
                    simp [validChildPair] at h_head
                  exact False.elim h_false
          | nonterm childN =>
              cases child with
              | Leaf b =>
                  have h_false : False := by
                    have h_head := h_valid
                      (Symbol.nonterm childN, Leaf (cfg := cfg) b) (by simp)
                    simp [validChildPair] at h_head
                  exact False.elim h_false
              | Node n' rule' grandchildren =>
                  have h_child_valid_root :
                      childN = n' ∧
                        (Node (cfg := cfg) n' rule' grandchildren).Valid := by
                    have h_head := h_valid
                      (Symbol.nonterm childN,
                        Node (cfg := cfg) n' rule' grandchildren) (by simp)
                    simpa [validChildPair] using h_head
                  obtain ⟨h_eq, h_child_valid⟩ := h_child_valid_root
                  cases h_eq
                  have h_child_input :
                      input.toList =
                        pre ++
                          (Node (cfg := cfg) childN rule' grandchildren).leaves ++
                          forestLeaves (cfg := cfg) tail ++ post := by
                    simpa [forestLeaves, ParseTree.leaves, List.append_assoc]
                      using h_input
                  have h_child_mem :
                      Node (cfg := cfg) childN rule' grandchildren ∈
                        (runParser (tag := tag cfg)
                          (memoize counter (gen' (μ := List) cfg) childN)
                          input pre.length).1.getD
                          (pre.length +
                            (Node (cfg := cfg) childN rule' grandchildren).leaves.length) [] := by
                    exact h_recur
                      (post' := forestLeaves (cfg := cfg) tail ++ post)
                      (by simp) h_child_adm h_child_valid
                      (by simpa [List.append_assoc] using h_child_input)
                  have h_tail :=
                    ih h_tail_adm' h_len_tail h_tail_valid h_input_tail h_recur_tail
                  exact GeneratedChildWitness.nonterm h_child_mem
                    (by
                      simpa [forestLeaves, ParseTree.leaves, List.length_append, Nat.add_assoc]
                        using h_tail)

set_option maxHeartbeats 1000000 in
omit [Monad μ] [SemilatticeAlt μ] [Traversable μ] in
theorem gen_complete_of_admissible_tree_span
  {cfg : @CFG α ν} {input : Array α}
  {tree : ParseTree cfg} {seen : List (SpanVisit ν)}
  {counter : Counter ν} {n : ν} {pre post : List α}
  (h_root : tree.root = Symbol.nonterm n)
  (h_adm : AdmissibleTreeWith cfg input seen counter tree pre.length)
  (h_valid : tree.Valid)
  (h_input : input.toList = pre ++ tree.leaves ++ post) :
    tree ∈
      (runParser (tag := tag cfg)
        (memoize counter (gen' (μ := List) cfg) n)
        input pre.length).1.getD
        (pre.length + tree.leaves.length) [] := by
  revert seen counter n pre post h_root h_adm h_valid h_input
  refine ((measure (fun tree : ParseTree cfg => sizeOf tree)).wf).induction
    (C := fun tree =>
      ∀ {seen : List (SpanVisit ν)} {counter : Counter ν}
        {n : ν} {pre post : List α},
        tree.root = Symbol.nonterm n →
        AdmissibleTreeWith cfg input seen counter tree pre.length →
        tree.Valid →
        input.toList = pre ++ tree.leaves ++ post →
        tree ∈
          (runParser (tag := tag cfg)
            (memoize counter (gen' (μ := List) cfg) n)
            input pre.length).1.getD
            (pre.length + tree.leaves.length) [])
    tree ?_
  intro tree ih seen counter n pre post h_root h_adm h_valid h_input
  cases tree with
  | Leaf a =>
      simp at h_root
  | Node n' rule children =>
      have h_n : n' = n := by
        simpa using h_root
      cases h_n
      obtain ⟨_h_no_cycle, h_budget, h_children_adm⟩ :=
        admissible_node_inv (cfg := cfg) h_adm
      have h_valid_node := by
        simpa [ParseTree.Valid] using h_valid
      have h_valid' :
          rule.val.length = children.length ∧
          ∀ pair, pair ∈ List.zip rule.val children →
            validChildPair (cfg := cfg) pair := by
        constructor
        · exact h_valid_node.1
        · intro pair h_pair
          cases pair with
          | mk sym subtree =>
              have h_pair_valid := h_valid_node.2 sym subtree h_pair
              cases sym <;> cases subtree <;>
                simp [validChildPair] at h_pair_valid ⊢ <;> assumption
      have h_forest_input :
          input.toList = pre ++ forestLeaves (cfg := cfg) children ++ post := by
        simpa [leaves_node_eq_forestLeaves] using h_input
      let childCounter := counter.dec n (input.size - pre.length + 1)
      have h_child_witness :
          GeneratedChildWitness cfg
            (memoize childCounter (gen' (μ := List) cfg))
            input rule.val children pre.length
            (pre.length + (forestLeaves (cfg := cfg) children).length) := by
        apply generatedChildWitness_of_admissible_valid_pairs
          (cfg := cfg) (input := input)
          (seen :=
            nodeSpanVisit n pre.length
              (Node (cfg := cfg) n rule children) :: seen)
          (counter := childCounter)
          (rule := rule.val) (children := children)
          (pre := pre) (post := post)
        · simpa [childCounter] using h_children_adm
        · exact h_valid'.1
        · exact h_valid'.2
        · exact h_forest_input
        · intro childN rule' grandchildren pre' post' h_mem_child
            h_child_adm h_child_valid h_child_input
          have h_lt :
              sizeOf (Node (cfg := cfg) childN rule' grandchildren) <
                sizeOf (Node (cfg := cfg) n rule children) := by
            exact ParseTree.sizeOf_lt_of_child
              (parent := Node (cfg := cfg) n rule children)
              (child := Node (cfg := cfg) childN rule' grandchildren)
              h_mem_child
          exact ih (Node (cfg := cfg) childN rule' grandchildren) h_lt
            (seen :=
              nodeSpanVisit n pre.length
                (Node (cfg := cfg) n rule children) :: seen)
            (counter := childCounter)
            (n := childN) (pre := pre') (post := post') rfl
            h_child_adm h_child_valid h_child_input
      have h_body :
          Node (cfg := cfg) n rule children ∈
            (runParser (tag := tag cfg)
              (gen' (μ := List) cfg
                (memoize childCounter (gen' (μ := List) cfg)) n)
              input pre.length).1.getD
              (pre.length + (Node (cfg := cfg) n rule children).leaves.length) [] := by
        have h_branch := gen'_rule_complete_of_child_witness
          (cfg := cfg)
          (recur := memoize childCounter (gen' (μ := List) cfg))
          (n := n) (rule := rule.val) rule.property
          (input := input) (start := pre.length)
          (end_ := pre.length + (forestLeaves (cfg := cfg) children).length)
          (subtrees := children) h_child_witness
        simpa [leaves_node_eq_forestLeaves] using h_branch
      exact mem_memoize_startState_of_body_mem
        (tag := tag cfg) (β := α)
        (counter := counter)
        (g := gen' (μ := List) cfg)
        (t := n) (input := input) (start := pre.length)
        (end_pos := pre.length +
          (Node (cfg := cfg) n rule children).leaves.length)
        (x := Node (cfg := cfg) n rule children)
        h_budget
        (by simpa [childCounter] using h_body)

omit [Monad μ] [SemilatticeAlt μ] [Traversable μ] in
theorem gen_complete_of_admissible_node_span
  {cfg : @CFG α ν} {input : Array α}
  {seen : List (SpanVisit ν)} {counter : Counter ν}
  {n : ν} {rule : {rule // rule ∈ cfg.rules n}}
  {children : List (ParseTree cfg)} {pre post : List α}
  (h_adm :
    AdmissibleTreeWith cfg input seen counter
      (Node (cfg := cfg) n rule children) pre.length)
  (h_valid : (Node (cfg := cfg) n rule children).Valid)
  (h_input :
    input.toList =
      pre ++ (Node (cfg := cfg) n rule children).leaves ++ post) :
    Node (cfg := cfg) n rule children ∈
      (runParser (tag := tag cfg)
        (memoize counter (gen' (μ := List) cfg) n)
        input pre.length).1.getD
        (pre.length +
          (Node (cfg := cfg) n rule children).leaves.length) [] := by
  exact gen_complete_of_admissible_tree_span
    (cfg := cfg) (input := input)
    (tree := Node (cfg := cfg) n rule children)
    (seen := seen) (counter := counter) (n := n)
    (pre := pre) (post := post)
    rfl h_adm h_valid h_input

omit [Monad μ] [SemilatticeAlt μ] [Traversable μ] in
theorem gen_complete_exists_of_admissible_valid_tree
  {cfg : @CFG α ν} {n : ν} {input : Array α} {tree : ParseTree cfg}
  (h_adm : AdmissibleTree cfg input tree 0)
  (h_valid : tree.Valid)
  (h_root : tree.root = Symbol.nonterm n)
  (h_leaves : tree.leaves = input.toList) :
    ∃ tree,
      tree ∈ (runParser (tag := tag cfg) (gen (μ := List) cfg n)
        input 0).1.getD input.size [] ∧
      tree.Valid ∧
      tree.root = Symbol.nonterm n ∧
      tree.leaves = input.toList := by
  refine ⟨tree, ?_, h_valid, h_root, h_leaves⟩
  have h_input :
      input.toList = [] ++ tree.leaves ++ [] := by
    simp [h_leaves]
  have h_mem := gen_complete_of_admissible_tree_span
    (cfg := cfg) (input := input) (tree := tree)
    (seen := []) (counter := (Counter.empty : Counter ν))
    (n := n) (pre := []) (post := [])
    h_root h_adm h_valid h_input
  unfold gen
  simpa [h_leaves] using h_mem

omit [Monad μ] [SemilatticeAlt μ] [Traversable μ] [BEq α] [Hashable ν] [Fintype ν] in
theorem exists_minimal_valid_tree_of_derives
  {cfg : @CFG α ν} {n : ν} {input : Array α}
  (h_derives : cfg.derives [Symbol.nonterm n] (input.toList.map Symbol.term)) :
    ∃ tree : ParseTree cfg,
      tree.Valid ∧
      tree.root = Symbol.nonterm n ∧
      tree.leaves = input.toList ∧
      ∀ tree' : ParseTree cfg,
        tree'.Valid →
        tree'.root = Symbol.nonterm n →
        tree'.leaves = input.toList →
        sizeOf tree ≤ sizeOf tree' := by
  classical
  let P : ℕ → Prop := fun k =>
    ∃ tree : ParseTree cfg,
      sizeOf tree = k ∧
      tree.Valid ∧
      tree.root = Symbol.nonterm n ∧
      tree.leaves = input.toList
  have h_exists_tree :
      ∃ tree : ParseTree cfg,
        tree.Valid ∧
        tree.root = Symbol.nonterm n ∧
        tree.leaves = input.toList := by
    exact ParseTree.exists_Valid_tree_of_derives
      (cfg := cfg) (n := n) (w := input.toList) h_derives
  have h_exists_size : ∃ k, P k := by
    obtain ⟨tree, h_valid, h_root, h_leaves⟩ := h_exists_tree
    exact ⟨sizeOf tree, tree, rfl, h_valid, h_root, h_leaves⟩
  obtain ⟨tree, h_size, h_valid, h_root, h_leaves⟩ :=
    Nat.find_spec h_exists_size
  refine ⟨tree, h_valid, h_root, h_leaves, ?_⟩
  intro tree' h_valid' h_root' h_leaves'
  have h_tree'_size : P (sizeOf tree') :=
    ⟨tree', rfl, h_valid', h_root', h_leaves'⟩
  have h_min := Nat.find_min' h_exists_size h_tree'_size
  omega

omit [Monad μ] [SemilatticeAlt μ] [Traversable μ] [BEq α] [DecidableEq α]
  [DecidableEq ν] [Hashable ν] [Fintype ν] in
theorem minimal_valid_tree_no_child_same_root_leaves
  {cfg : @CFG α ν} {n : ν} {input : Array α}
  {tree child : ParseTree cfg}
  (h_min :
    ∀ tree' : ParseTree cfg,
      tree'.Valid →
      tree'.root = Symbol.nonterm n →
      tree'.leaves = input.toList →
      sizeOf tree ≤ sizeOf tree')
  (h_child_mem : child ∈ tree.children)
  (h_child_valid : child.Valid)
  (h_child_root : child.root = Symbol.nonterm n)
  (h_child_leaves : child.leaves = input.toList) :
    False := by
  have h_le : sizeOf tree ≤ sizeOf child :=
    h_min child h_child_valid h_child_root h_child_leaves
  have h_lt : sizeOf child < sizeOf tree :=
    ParseTree.sizeOf_lt_of_child (parent := tree) h_child_mem
  omega

omit [Monad μ] [SemilatticeAlt μ] [Traversable μ] [BEq α] [DecidableEq α]
  [DecidableEq ν] [Hashable ν] [Fintype ν] in
theorem minimal_valid_node_no_smaller_child_replacement_split
  {cfg : @CFG α ν} {n : ν} {input : Array α}
  {rule : {rule // rule ∈ cfg.rules n}}
  {ruleBefore ruleAfter : List (Symbol α ν)} {sym : Symbol α ν}
  {before after : List (ParseTree cfg)} {old new : ParseTree cfg}
  (h_rule : rule.val = ruleBefore ++ sym :: ruleAfter)
  (h_before_len : ruleBefore.length = before.length)
  (h_valid : (Node (cfg := cfg) n rule (before ++ old :: after)).Valid)
  (h_parent_leaves :
    (Node (cfg := cfg) n rule (before ++ old :: after)).leaves = input.toList)
  (h_min :
    ∀ tree' : ParseTree cfg,
      tree'.Valid →
      tree'.root = Symbol.nonterm n →
      tree'.leaves = input.toList →
      sizeOf (Node (cfg := cfg) n rule (before ++ old :: after)) ≤
        sizeOf tree')
  (h_new_valid : new.Valid)
  (h_root : new.root = old.root)
  (h_leaves : new.leaves = old.leaves)
  (h_size : sizeOf new < sizeOf old) :
    False := by
  let replacement := Node (cfg := cfg) n rule (before ++ new :: after)
  have h_replacement :=
    valid_node_replace_child_split
      (cfg := cfg) (n := n) (rule := rule)
      (ruleBefore := ruleBefore) (ruleAfter := ruleAfter)
      (sym := sym) (before := before) (after := after)
      (old := old) (new := new)
      h_rule h_before_len h_valid h_new_valid h_root h_leaves h_size
  have h_replacement_valid : replacement.Valid := h_replacement.1
  have h_replacement_root : replacement.root = Symbol.nonterm n := rfl
  have h_replacement_leaves : replacement.leaves = input.toList := by
    exact h_replacement.2.2.1.trans h_parent_leaves
  have h_min_le : sizeOf (Node (cfg := cfg) n rule (before ++ old :: after)) ≤
      sizeOf replacement :=
    h_min replacement h_replacement_valid h_replacement_root h_replacement_leaves
  have h_replacement_lt :
      sizeOf replacement <
        sizeOf (Node (cfg := cfg) n rule (before ++ old :: after)) :=
    h_replacement.2.2.2
  omega

omit [Monad μ] [SemilatticeAlt μ] [Traversable μ] [BEq α] [DecidableEq α]
  [DecidableEq ν] [Hashable ν] [Fintype ν] in
theorem minimal_valid_tree_no_smaller_subtree_replacement
  {cfg : @CFG α ν} {n : ν} {input : Array α}
  {tree subtree replacement : ParseTree cfg}
  (h_subtree : TreeSubtree (cfg := cfg) subtree tree)
  (h_tree_valid : tree.Valid)
  (h_tree_root : tree.root = Symbol.nonterm n)
  (h_tree_leaves : tree.leaves = input.toList)
  (h_min :
    ∀ tree' : ParseTree cfg,
      tree'.Valid →
      tree'.root = Symbol.nonterm n →
      tree'.leaves = input.toList →
      sizeOf tree ≤ sizeOf tree')
  (h_replacement_valid : replacement.Valid)
  (h_replacement_root : replacement.root = subtree.root)
  (h_replacement_leaves : replacement.leaves = subtree.leaves)
  (h_replacement_size : sizeOf replacement < sizeOf subtree) :
    False := by
  obtain ⟨tree', h_replace⟩ :=
    replaceSubtree_of_subtree
      (cfg := cfg) (target := subtree) (tree := tree)
      (replacement := replacement) h_subtree
  have h_result :=
    replaceSubtree_preserves_valid_root_leaves_size
      (cfg := cfg)
      (old := subtree) (new := replacement)
      (tree := tree) (tree' := tree')
      h_replace h_tree_valid h_replacement_valid
      h_replacement_root h_replacement_leaves h_replacement_size
  have h_tree'_root : tree'.root = Symbol.nonterm n :=
    h_result.2.1.trans h_tree_root
  have h_tree'_leaves : tree'.leaves = input.toList :=
    h_result.2.2.1.trans h_tree_leaves
  have h_min_le : sizeOf tree ≤ sizeOf tree' :=
    h_min tree' h_result.1 h_tree'_root h_tree'_leaves
  have h_lt : sizeOf tree' < sizeOf tree :=
    h_result.2.2.2
  omega

omit [Monad μ] [SemilatticeAlt μ] [Traversable μ] [BEq α] [DecidableEq α]
  [DecidableEq ν] [Hashable ν] [Fintype ν] in
theorem minimal_valid_tree_no_proper_descendant_same_root_leaves
  {cfg : @CFG α ν} {n : ν} {input : Array α}
  {tree ancestor descendant : ParseTree cfg}
  (h_ancestor : TreeSubtree (cfg := cfg) ancestor tree)
  (h_descendant : ProperTreeSubtree (cfg := cfg) descendant ancestor)
  (h_tree_valid : tree.Valid)
  (h_tree_root : tree.root = Symbol.nonterm n)
  (h_tree_leaves : tree.leaves = input.toList)
  (h_min :
    ∀ tree' : ParseTree cfg,
      tree'.Valid →
      tree'.root = Symbol.nonterm n →
      tree'.leaves = input.toList →
      sizeOf tree ≤ sizeOf tree')
  (h_root : descendant.root = ancestor.root)
  (h_leaves : descendant.leaves = ancestor.leaves) :
    False := by
  have h_ancestor_valid :
      ancestor.Valid :=
    treeSubtree_valid_of_valid
      (cfg := cfg) h_ancestor h_tree_valid
  have h_descendant_valid :
      descendant.Valid :=
    properTreeSubtree_valid_of_valid
      (cfg := cfg) h_descendant h_ancestor_valid
  have h_descendant_size :
      sizeOf descendant < sizeOf ancestor :=
    properTreeSubtree_size_lt (cfg := cfg) h_descendant
  exact minimal_valid_tree_no_smaller_subtree_replacement
    (cfg := cfg) (n := n) (input := input)
    (tree := tree) (subtree := ancestor)
    (replacement := descendant)
    h_ancestor h_tree_valid h_tree_root h_tree_leaves h_min
    h_descendant_valid h_root h_leaves h_descendant_size

omit [Monad μ] [SemilatticeAlt μ] [Traversable μ] [BEq α] [DecidableEq α]
  [DecidableEq ν] [Hashable ν] [Fintype ν] in
theorem minimal_valid_tree_no_proper_descendant_same_span
  {cfg : @CFG α ν} {n : ν} {input : Array α}
  {tree ancestor descendant : ParseTree cfg}
  {ancestorPre ancestorPost descendantPre descendantPost : List α}
  (h_ancestor : TreeSubtree (cfg := cfg) ancestor tree)
  (h_descendant : ProperTreeSubtree (cfg := cfg) descendant ancestor)
  (h_tree_valid : tree.Valid)
  (h_tree_root : tree.root = Symbol.nonterm n)
  (h_tree_leaves : tree.leaves = input.toList)
  (h_min :
    ∀ tree' : ParseTree cfg,
      tree'.Valid →
      tree'.root = Symbol.nonterm n →
      tree'.leaves = input.toList →
      sizeOf tree ≤ sizeOf tree')
  (h_ancestor_input :
    input.toList = ancestorPre ++ ancestor.leaves ++ ancestorPost)
  (h_descendant_input :
    input.toList = descendantPre ++ descendant.leaves ++ descendantPost)
  (h_root : descendant.root = ancestor.root)
  (h_start : ancestorPre.length = descendantPre.length)
  (h_end :
    ancestorPre.length + ancestor.leaves.length =
      descendantPre.length + descendant.leaves.length) :
    False := by
  have h_leaves_ancestor_descendant :
      ancestor.leaves = descendant.leaves :=
    list_middle_eq_of_same_span
      (xs := input.toList)
      (pre₁ := ancestorPre) (mid₁ := ancestor.leaves)
      (post₁ := ancestorPost)
      (pre₂ := descendantPre) (mid₂ := descendant.leaves)
      (post₂ := descendantPost)
      h_ancestor_input h_descendant_input h_start h_end
  exact minimal_valid_tree_no_proper_descendant_same_root_leaves
    (cfg := cfg) (n := n) (input := input)
    (tree := tree) (ancestor := ancestor) (descendant := descendant)
    h_ancestor h_descendant h_tree_valid h_tree_root h_tree_leaves h_min
    h_root h_leaves_ancestor_descendant.symm

omit [Monad μ] [SemilatticeAlt μ] [Traversable μ] [BEq α] [DecidableEq α]
  [DecidableEq ν] [Hashable ν] [Fintype ν] in
theorem minimal_valid_tree_no_proper_descendant_same_nodeSpan
  {cfg : @CFG α ν} {n : ν} {input : Array α}
  {tree : ParseTree cfg}
  {ancestorN descendantN : ν}
  {ancestorRule : {rule // rule ∈ cfg.rules ancestorN}}
  {descendantRule : {rule // rule ∈ cfg.rules descendantN}}
  {ancestorChildren descendantChildren : List (ParseTree cfg)}
  {ancestorPre ancestorPost descendantPre descendantPost : List α}
  (h_ancestor :
    TreeSubtree (cfg := cfg)
      (Node (cfg := cfg) ancestorN ancestorRule ancestorChildren) tree)
  (h_descendant :
    ProperTreeSubtree (cfg := cfg)
      (Node (cfg := cfg) descendantN descendantRule descendantChildren)
      (Node (cfg := cfg) ancestorN ancestorRule ancestorChildren))
  (h_tree_valid : tree.Valid)
  (h_tree_root : tree.root = Symbol.nonterm n)
  (h_tree_leaves : tree.leaves = input.toList)
  (h_min :
    ∀ tree' : ParseTree cfg,
      tree'.Valid →
      tree'.root = Symbol.nonterm n →
      tree'.leaves = input.toList →
      sizeOf tree ≤ sizeOf tree')
  (h_ancestor_input :
    input.toList =
      ancestorPre ++
        (Node (cfg := cfg) ancestorN ancestorRule ancestorChildren).leaves ++
        ancestorPost)
  (h_descendant_input :
    input.toList =
      descendantPre ++
        (Node (cfg := cfg) descendantN descendantRule descendantChildren).leaves ++
        descendantPost)
  (h_span :
    nodeSpanVisit ancestorN ancestorPre.length
      (Node (cfg := cfg) ancestorN ancestorRule ancestorChildren) =
    nodeSpanVisit descendantN descendantPre.length
      (Node (cfg := cfg) descendantN descendantRule descendantChildren)) :
    False := by
  have h_span' := h_span
  simp [nodeSpanVisit, leaves_node_eq_forestLeaves, forestLeaves] at h_span'
  obtain ⟨h_nt, h_start, h_end⟩ := h_span'
  apply minimal_valid_tree_no_proper_descendant_same_span
    (cfg := cfg) (n := n) (input := input)
    (tree := tree)
    (ancestor := Node (cfg := cfg) ancestorN ancestorRule ancestorChildren)
    (descendant := Node (cfg := cfg) descendantN descendantRule descendantChildren)
    (ancestorPre := ancestorPre) (ancestorPost := ancestorPost)
    (descendantPre := descendantPre) (descendantPost := descendantPost)
    h_ancestor h_descendant h_tree_valid h_tree_root h_tree_leaves h_min
    h_ancestor_input h_descendant_input
  · simp [ParseTree.root, h_nt]
  · exact h_start
  · simpa [leaves_node_eq_forestLeaves, forestLeaves] using h_end

omit [Monad μ] [SemilatticeAlt μ] [Traversable μ] [BEq α] [DecidableEq α]
  [DecidableEq ν] [Hashable ν] [Fintype ν] in
theorem seenPath_nodeSpan_not_mem_of_minimal
  {cfg : @CFG α ν} {rootN : ν} {input : Array α}
  {root : ParseTree cfg}
  {seen : List (SpanVisit ν)}
  {currentN : ν} {currentRule : {rule // rule ∈ cfg.rules currentN}}
  {currentChildren : List (ParseTree cfg)}
  {currentPre currentPost : List α}
  (h_path :
    SeenPath (cfg := cfg) input root seen
      (Node (cfg := cfg) currentN currentRule currentChildren) currentPre)
  (h_tree_valid : root.Valid)
  (h_tree_root : root.root = Symbol.nonterm rootN)
  (h_tree_leaves : root.leaves = input.toList)
  (h_min :
    ∀ tree' : ParseTree cfg,
      tree'.Valid →
      tree'.root = Symbol.nonterm rootN →
      tree'.leaves = input.toList →
      sizeOf root ≤ sizeOf tree')
  (h_current_input :
    input.toList =
      currentPre ++
        (Node (cfg := cfg) currentN currentRule currentChildren).leaves ++
        currentPost) :
    nodeSpanVisit currentN currentPre.length
      (Node (cfg := cfg) currentN currentRule currentChildren) ∉ seen := by
  intro h_mem
  obtain ⟨ancestorN, ancestorRule, ancestorChildren, ancestorPre,
    ancestorPost, h_visit, h_ancestor_root, h_current_ancestor,
    h_ancestor_input⟩ :=
    seenPath_visit_mem_ancestor
      (cfg := cfg) (input := input) (root := root)
      (current := Node (cfg := cfg) currentN currentRule currentChildren)
      (seen := seen) (pre := currentPre)
      (visit :=
        nodeSpanVisit currentN currentPre.length
          (Node (cfg := cfg) currentN currentRule currentChildren))
      h_path h_mem
  exact minimal_valid_tree_no_proper_descendant_same_nodeSpan
    (cfg := cfg) (n := rootN) (input := input)
    (tree := root)
    (ancestorN := ancestorN) (descendantN := currentN)
    (ancestorRule := ancestorRule) (descendantRule := currentRule)
    (ancestorChildren := ancestorChildren)
    (descendantChildren := currentChildren)
    (ancestorPre := ancestorPre) (ancestorPost := ancestorPost)
    (descendantPre := currentPre) (descendantPost := currentPost)
    h_ancestor_root h_current_ancestor h_tree_valid h_tree_root h_tree_leaves
    h_min h_ancestor_input h_current_input h_visit.symm

omit [Monad μ] [SemilatticeAlt μ] [Traversable μ] [BEq α] [DecidableEq α]
  [DecidableEq ν] [Hashable ν] [Fintype ν] in
theorem minimal_valid_tree_same_tag_proper_subtreeSpan_leaves_length_lt
  {cfg : @CFG α ν} {rootN : ν} {input : Array α}
  {root : ParseTree cfg}
  {n : ν}
  {ancestorRule targetRule : {rule // rule ∈ cfg.rules n}}
  {ancestorChildren targetChildren : List (ParseTree cfg)}
  {ancestorPre ancestorPost targetPre : List α}
  (h_ancestor_root :
    TreeSubtree (cfg := cfg)
      (Node (cfg := cfg) n ancestorRule ancestorChildren) root)
  (h_target_ancestor :
    ProperTreeSubtree (cfg := cfg)
      (Node (cfg := cfg) n targetRule targetChildren)
      (Node (cfg := cfg) n ancestorRule ancestorChildren))
  (h_span :
    SubtreeSpan (cfg := cfg)
      (Node (cfg := cfg) n ancestorRule ancestorChildren) ancestorPre
      (Node (cfg := cfg) n targetRule targetChildren) targetPre)
  (h_tree_valid : root.Valid)
  (h_tree_root : root.root = Symbol.nonterm rootN)
  (h_tree_leaves : root.leaves = input.toList)
  (h_min :
    ∀ tree' : ParseTree cfg,
      tree'.Valid →
      tree'.root = Symbol.nonterm rootN →
      tree'.leaves = input.toList →
      sizeOf root ≤ sizeOf tree')
  (h_ancestor_input :
    input.toList =
      ancestorPre ++
        (Node (cfg := cfg) n ancestorRule ancestorChildren).leaves ++
        ancestorPost) :
    (Node (cfg := cfg) n targetRule targetChildren).leaves.length <
      (Node (cfg := cfg) n ancestorRule ancestorChildren).leaves.length := by
  obtain ⟨targetPost, h_target_input⟩ :=
    subtreeSpan_input
      (cfg := cfg) (input := input)
      (tree := Node (cfg := cfg) n ancestorRule ancestorChildren)
      (target := Node (cfg := cfg) n targetRule targetChildren)
      (pre := ancestorPre) (post := ancestorPost)
      (targetPre := targetPre)
      h_span h_ancestor_input
  have h_bounds := subtreeSpan_bounds (cfg := cfg) h_span
  by_contra h_not_lt
  have h_len_eq :
      (Node (cfg := cfg) n targetRule targetChildren).leaves.length =
        (Node (cfg := cfg) n ancestorRule ancestorChildren).leaves.length := by
    omega
  have h_pre_len_eq : targetPre.length = ancestorPre.length := by
    omega
  have h_end_eq :
      ancestorPre.length +
          (Node (cfg := cfg) n ancestorRule ancestorChildren).leaves.length =
        targetPre.length +
          (Node (cfg := cfg) n targetRule targetChildren).leaves.length := by
    omega
  have h_end_eq' :
      ancestorPre.length +
          (List.map (fun a => a.leaves.length) ancestorChildren).sum =
        targetPre.length +
          (List.map (fun a => a.leaves.length) targetChildren).sum := by
    simpa [leaves_node_eq_forestLeaves, forestLeaves] using h_end_eq
  have h_span_eq :
      nodeSpanVisit n ancestorPre.length
        (Node (cfg := cfg) n ancestorRule ancestorChildren) =
      nodeSpanVisit n targetPre.length
        (Node (cfg := cfg) n targetRule targetChildren) := by
    simp [nodeSpanVisit, leaves_node_eq_forestLeaves, forestLeaves,
      h_pre_len_eq, h_end_eq']
  exact minimal_valid_tree_no_proper_descendant_same_nodeSpan
    (cfg := cfg) (n := rootN) (input := input)
    (tree := root)
    (ancestorN := n) (descendantN := n)
    (ancestorRule := ancestorRule) (descendantRule := targetRule)
    (ancestorChildren := ancestorChildren)
    (descendantChildren := targetChildren)
    (ancestorPre := ancestorPre) (ancestorPost := ancestorPost)
    (descendantPre := targetPre) (descendantPost := targetPost)
    h_ancestor_root h_target_ancestor h_tree_valid h_tree_root h_tree_leaves
    h_min h_ancestor_input h_target_input h_span_eq

set_option linter.unusedSectionVars false in
theorem seenPath_subtreeSpan_count_add_leaves_lt_initialFuel
  {cfg : @CFG α ν} {rootN : ν} {input : Array α}
  {root current : ParseTree cfg}
  {seen : List (SpanVisit ν)} {currentPre : List α}
  {targetN : ν} {targetRule : {rule // rule ∈ cfg.rules targetN}}
  {targetChildren : List (ParseTree cfg)} {targetPre : List α}
  {fuel : ℕ}
  (h_path :
    SeenPath (cfg := cfg) input root seen current currentPre)
  (h_target_span :
    SubtreeSpan (cfg := cfg) current currentPre
      (Node (cfg := cfg) targetN targetRule targetChildren) targetPre)
  (h_tree_valid : root.Valid)
  (h_tree_root : root.root = Symbol.nonterm rootN)
  (h_tree_leaves : root.leaves = input.toList)
  (h_min :
    ∀ tree' : ParseTree cfg,
      tree'.Valid →
      tree'.root = Symbol.nonterm rootN →
      tree'.leaves = input.toList →
      sizeOf root ≤ sizeOf tree')
  (h_initial : spanVisitInitialFuel input targetN seen = some fuel) :
    spanVisitCount targetN seen +
        (Node (cfg := cfg) targetN targetRule targetChildren).leaves.length <
      fuel := by
  induction h_path generalizing targetN targetRule targetChildren targetPre fuel with
  | root =>
      simp [spanVisitInitialFuel] at h_initial
  | child h_parent_path h_parent_input ih =>
      rename_i seen parentPre parentPost parentN parentRule before after child
      let parent : ParseTree cfg :=
        Node (cfg := cfg) parentN parentRule (before ++ child :: after)
      have h_target_parent_span :
          SubtreeSpan (cfg := cfg) parent parentPre
            (Node (cfg := cfg) targetN targetRule targetChildren) targetPre :=
        SubtreeSpan.child h_target_span
      by_cases h_tag : parentN = targetN
      · subst targetN
        cases h_tail_initial :
            spanVisitInitialFuel input parentN seen with
        | some tailFuel =>
            have h_fuel : fuel = tailFuel := by
              have h_fuel' : tailFuel = fuel := by
                simpa [spanVisitInitialFuel, h_tail_initial, parent, nodeSpanVisit]
                  using h_initial
              exact h_fuel'.symm
            subst fuel
            have h_parent_budget :
                spanVisitCount parentN seen + parent.leaves.length <
                  tailFuel := by
              exact ih
                (targetN := parentN) (targetRule := parentRule)
                (targetChildren := before ++ child :: after)
                (targetPre := parentPre) (fuel := tailFuel)
                (SubtreeSpan.here parent parentPre)
                h_tail_initial
            have h_parent_root :
                TreeSubtree (cfg := cfg) parent root :=
              seenPath_treeSubtree (cfg := cfg) h_parent_path
            have h_target_parent_proper :
                ProperTreeSubtree (cfg := cfg)
                  (Node (cfg := cfg) parentN targetRule targetChildren)
                  parent :=
              ProperTreeSubtree.child
                (subtreeSpan_treeSubtree (cfg := cfg) h_target_span)
            have h_target_len_lt_parent :
                (Node (cfg := cfg) parentN targetRule targetChildren).leaves.length <
                  parent.leaves.length :=
              minimal_valid_tree_same_tag_proper_subtreeSpan_leaves_length_lt
                (cfg := cfg) (rootN := rootN) (input := input)
                (root := root) (n := parentN)
                (ancestorRule := parentRule) (targetRule := targetRule)
                (ancestorChildren := before ++ child :: after)
                (targetChildren := targetChildren)
                (ancestorPre := parentPre) (ancestorPost := parentPost)
                (targetPre := targetPre)
                h_parent_root h_target_parent_proper h_target_parent_span
                h_tree_valid h_tree_root h_tree_leaves h_min h_parent_input
            change ((if parentN = parentN then 1 else 0) +
                spanVisitCount parentN seen) +
              (Node (cfg := cfg) parentN targetRule targetChildren).leaves.length <
                tailFuel
            simp only [if_true]
            omega
        | none =>
            have h_fuel :
                fuel = input.size - parentPre.length + 1 := by
              have h_fuel' : input.size - parentPre.length + 1 = fuel := by
                simpa [spanVisitInitialFuel, h_tail_initial, parent, nodeSpanVisit]
                  using h_initial
              exact h_fuel'.symm
            subst fuel
            have h_count_zero :
                spanVisitCount parentN seen = 0 :=
              spanVisitCount_eq_zero_of_initialFuel_none
                (input := input) (seen := seen) (t := parentN)
                h_tail_initial
            have h_parent_root :
                TreeSubtree (cfg := cfg) parent root :=
              seenPath_treeSubtree (cfg := cfg) h_parent_path
            have h_target_parent_proper :
                ProperTreeSubtree (cfg := cfg)
                  (Node (cfg := cfg) parentN targetRule targetChildren)
                  parent :=
              ProperTreeSubtree.child
                (subtreeSpan_treeSubtree (cfg := cfg) h_target_span)
            have h_target_len_lt_parent :
                (Node (cfg := cfg) parentN targetRule targetChildren).leaves.length <
                  parent.leaves.length :=
              minimal_valid_tree_same_tag_proper_subtreeSpan_leaves_length_lt
                (cfg := cfg) (rootN := rootN) (input := input)
                (root := root) (n := parentN)
                (ancestorRule := parentRule) (targetRule := targetRule)
                (ancestorChildren := before ++ child :: after)
                (targetChildren := targetChildren)
                (ancestorPre := parentPre) (ancestorPost := parentPost)
                (targetPre := targetPre)
                h_parent_root h_target_parent_proper h_target_parent_span
                h_tree_valid h_tree_root h_tree_leaves h_min h_parent_input
            have h_parent_end_le :
                parentPre.length + parent.leaves.length ≤ input.size := by
              have h_len :
                  (parentPre ++ parent.leaves ++ parentPost).length =
                    input.size := by
                rw [← h_parent_input]
                simp [Array.length_toList]
              simp [List.length_append] at h_len
              omega
            change ((if parentN = parentN then 1 else 0) +
                spanVisitCount parentN seen) +
              (Node (cfg := cfg) parentN targetRule targetChildren).leaves.length <
                input.size - parentPre.length + 1
            simp only [if_true]
            rw [h_count_zero]
            omega
      · cases h_tail_initial :
            spanVisitInitialFuel input targetN seen with
        | none =>
            simp [spanVisitInitialFuel, h_tail_initial, h_tag] at h_initial
        | some tailFuel =>
            have h_fuel : fuel = tailFuel := by
              have h_fuel' : tailFuel = fuel := by
                simpa [spanVisitInitialFuel, h_tail_initial, h_tag, parent,
                  nodeSpanVisit] using h_initial
              exact h_fuel'.symm
            subst fuel
            have h_tail_budget :=
              ih
                (targetN := targetN) (targetRule := targetRule)
                (targetChildren := targetChildren) (targetPre := targetPre)
                (fuel := tailFuel)
                h_target_parent_span h_tail_initial
            change ((if parentN = targetN then 1 else 0) +
                spanVisitCount targetN seen) +
              (Node (cfg := cfg) targetN targetRule targetChildren).leaves.length <
                tailFuel
            simpa [h_tag, leaves_node_eq_forestLeaves, forestLeaves]
              using h_tail_budget

set_option linter.unusedSectionVars false in
theorem seenPath_count_lt_initialFuel
  {cfg : @CFG α ν} {rootN : ν} {input : Array α}
  {root : ParseTree cfg}
  {seen : List (SpanVisit ν)}
  {currentN : ν} {currentRule : {rule // rule ∈ cfg.rules currentN}}
  {currentChildren : List (ParseTree cfg)}
  {currentPre : List α} {fuel : ℕ}
  (h_path :
    SeenPath (cfg := cfg) input root seen
      (Node (cfg := cfg) currentN currentRule currentChildren) currentPre)
  (h_tree_valid : root.Valid)
  (h_tree_root : root.root = Symbol.nonterm rootN)
  (h_tree_leaves : root.leaves = input.toList)
  (h_min :
    ∀ tree' : ParseTree cfg,
      tree'.Valid →
      tree'.root = Symbol.nonterm rootN →
      tree'.leaves = input.toList →
      sizeOf root ≤ sizeOf tree')
  (h_initial : spanVisitInitialFuel input currentN seen = some fuel) :
    spanVisitCount currentN seen < fuel := by
  have h_budget :=
    seenPath_subtreeSpan_count_add_leaves_lt_initialFuel
      (cfg := cfg) (rootN := rootN) (input := input)
      (root := root)
      (current := Node (cfg := cfg) currentN currentRule currentChildren)
      (seen := seen) (currentPre := currentPre)
      (targetN := currentN) (targetRule := currentRule)
      (targetChildren := currentChildren) (targetPre := currentPre)
      (fuel := fuel)
      h_path (SubtreeSpan.here
        (Node (cfg := cfg) currentN currentRule currentChildren) currentPre)
      h_tree_valid h_tree_root h_tree_leaves h_min h_initial
  omega

set_option maxHeartbeats 1000000 in
set_option linter.unusedSectionVars false in
theorem minimal_valid_tree_admissible_with
  {cfg : @CFG α ν} {rootN : ν} {input : Array α}
  {root tree : ParseTree cfg}
  {seen : List (SpanVisit ν)} {counter : Counter ν}
  {pre post : List α}
  (h_path : SeenPath (cfg := cfg) input root seen tree pre)
  (h_counter : CounterMatchesSeen input seen counter)
  (h_tree_valid : root.Valid)
  (h_tree_root : root.root = Symbol.nonterm rootN)
  (h_tree_leaves : root.leaves = input.toList)
  (h_min :
    ∀ tree' : ParseTree cfg,
      tree'.Valid →
      tree'.root = Symbol.nonterm rootN →
      tree'.leaves = input.toList →
      sizeOf root ≤ sizeOf tree')
  (h_valid : tree.Valid)
  (h_input : input.toList = pre ++ tree.leaves ++ post) :
    AdmissibleTreeWith cfg input seen counter tree pre.length := by
  revert seen counter pre post h_path h_counter h_valid h_input
  refine ((measure (fun tree : ParseTree cfg => sizeOf tree)).wf).induction
    (C := fun tree =>
      ∀ {seen : List (SpanVisit ν)} {counter : Counter ν}
        {pre post : List α},
        SeenPath (cfg := cfg) input root seen tree pre →
        CounterMatchesSeen input seen counter →
        tree.Valid →
        input.toList = pre ++ tree.leaves ++ post →
        AdmissibleTreeWith cfg input seen counter tree pre.length)
    tree ?_
  intro tree ih seen counter pre post h_path h_counter h_valid h_input
  cases tree with
  | Leaf a =>
      exact AdmissibleTreeWith.leaf
        (cfg := cfg) (input := input) seen counter a pre.length
  | Node n rule children =>
      let node : ParseTree cfg := Node (cfg := cfg) n rule children
      have h_no_cycle :
          nodeSpanVisit n pre.length node ∉ seen :=
        seenPath_nodeSpan_not_mem_of_minimal
          (cfg := cfg) (rootN := rootN) (input := input)
          (root := root) (seen := seen)
          (currentN := n) (currentRule := rule)
          (currentChildren := children)
          (currentPre := pre) (currentPost := post)
          h_path h_tree_valid h_tree_root h_tree_leaves h_min
          (by simpa [node] using h_input)
      have h_budget : counter[n]? ≠ some 0 := by
        cases h_initial : spanVisitInitialFuel input n seen with
        | none =>
            exact counterMatchesSeen_getElem?_ne_zero_of_initialFuel_none
              (input := input) (seen := seen) (counter := counter)
              h_counter n h_initial
        | some fuel =>
            have h_count :
                spanVisitCount n seen < fuel :=
              seenPath_count_lt_initialFuel
                (cfg := cfg) (rootN := rootN) (input := input)
                (root := root) (seen := seen)
                (currentN := n) (currentRule := rule)
                (currentChildren := children) (currentPre := pre)
                (fuel := fuel)
                h_path h_tree_valid h_tree_root h_tree_leaves h_min
                h_initial
            exact counterMatchesSeen_getElem?_ne_zero_of_initialFuel_count_lt
              (input := input) (seen := seen) (counter := counter)
              h_counter n h_initial h_count
      let childSeen := nodeSpanVisit n pre.length node :: seen
      let childCounter := counter.dec n (input.size - pre.length + 1)
      have h_child_counter :
          CounterMatchesSeen input childSeen childCounter :=
        counterMatchesSeen_cons_nodeSpan
          (cfg := cfg) (input := input) (seen := seen)
          (counter := counter) h_counter n pre.length node
      have h_children_adm :
          AdmissibleForestWith cfg input childSeen childCounter
            children pre.length := by
        have h_valid_node :
            (Node (cfg := cfg) n rule children).Valid := by
          simpa [node] using h_valid
        have h_parent_input :
            input.toList =
              pre ++ (Node (cfg := cfg) n rule children).leaves ++ post := by
          simpa [node] using h_input
        have go :
            ∀ (before rest : List (ParseTree cfg)),
              children = before ++ rest →
              AdmissibleForestWith cfg input childSeen childCounter rest
                (pre ++ forestLeaves (cfg := cfg) before).length := by
          intro before rest h_split
          induction rest generalizing before with
          | nil =>
              simpa using
                (AdmissibleForestWith.nil
                  (cfg := cfg) (input := input) childSeen childCounter
                  (pre ++ forestLeaves (cfg := cfg) before).length)
          | cons child tail ih_tail =>
              have h_children_split :
                  children = before ++ child :: tail := h_split
              have h_parent_path_split :
                  SeenPath (cfg := cfg) input root seen
                    (Node (cfg := cfg) n rule (before ++ child :: tail)) pre := by
                simpa [h_children_split] using h_path
              have h_parent_input_split :
                  input.toList =
                    pre ++
                      (Node (cfg := cfg) n rule
                        (before ++ child :: tail)).leaves ++
                      post := by
                simpa [h_children_split] using h_parent_input
              have h_child_path :
                  SeenPath (cfg := cfg) input root childSeen child
                    (pre ++ forestLeaves (cfg := cfg) before) := by
                have h_path' :=
                  SeenPath.child
                    (cfg := cfg) (input := input) (root := root)
                    (seen := seen) (parentPre := pre)
                    (parentPost := post) (parentN := n)
                    (parentRule := rule) (before := before)
                    (after := tail) (child := child)
                    h_parent_path_split h_parent_input_split
                simpa [childSeen, node, h_children_split] using h_path'
              have h_child_input :
                  input.toList =
                    (pre ++ forestLeaves (cfg := cfg) before) ++
                      child.leaves ++
                      (forestLeaves (cfg := cfg) tail ++ post) := by
                simpa [h_children_split, leaves_node_eq_forestLeaves,
                  forestLeaves, List.append_assoc] using h_parent_input
              have h_child_valid : child.Valid := by
                have h_valid_split :
                    (Node (cfg := cfg) n rule
                      (before ++ child :: tail)).Valid := by
                  simpa [h_children_split] using h_valid_node
                exact valid_node_child_valid_of_split
                  (cfg := cfg) (n := n) (rule := rule)
                  (before := before) (after := tail)
                  (child := child) h_valid_split
              have h_child_size :
                  sizeOf child <
                    sizeOf (Node (cfg := cfg) n rule children) := by
                exact ParseTree.sizeOf_lt_of_child
                  (parent := Node (cfg := cfg) n rule children)
                  (child := child)
                  (by rw [h_children_split]; simp)
              have h_child_adm :
                  AdmissibleTreeWith cfg input childSeen childCounter child
                    (pre ++ forestLeaves (cfg := cfg) before).length :=
                ih child h_child_size h_child_path h_child_counter
                  h_child_valid h_child_input
              have h_tail_adm :
                  AdmissibleForestWith cfg input childSeen childCounter tail
                    ((pre ++ forestLeaves (cfg := cfg) before).length +
                      child.leaves.length) := by
                have h_tail :=
                  ih_tail (before ++ [child]) (by
                    simpa [List.append_assoc] using h_children_split)
                simpa [forestLeaves, List.length_append, Nat.add_assoc,
                  Nat.add_comm, Nat.add_left_comm] using h_tail
              exact AdmissibleForestWith.cons
                (cfg := cfg) (input := input) childSeen childCounter
                h_child_adm h_tail_adm
        simpa [forestLeaves] using go [] children (by simp)
      exact AdmissibleTreeWith.node
        (cfg := cfg) (input := input) seen counter
        h_no_cycle h_budget (by simpa [childSeen, childCounter, node] using h_children_adm)

set_option maxHeartbeats 1000000 in
set_option linter.unusedSectionVars false in
theorem minimal_valid_tree_admissible
  {cfg : @CFG α ν} {n : ν} {input : Array α}
  {tree : ParseTree cfg}
  (h_valid : tree.Valid)
  (h_root : tree.root = Symbol.nonterm n)
  (h_leaves : tree.leaves = input.toList)
  (h_min :
    ∀ tree' : ParseTree cfg,
      tree'.Valid →
      tree'.root = Symbol.nonterm n →
      tree'.leaves = input.toList →
      sizeOf tree ≤ sizeOf tree') :
    AdmissibleTree cfg input tree 0 := by
  have h_input : input.toList = [] ++ tree.leaves ++ [] := by
    simp [h_leaves]
  exact minimal_valid_tree_admissible_with
    (cfg := cfg) (rootN := n) (input := input)
    (root := tree) (tree := tree)
    (seen := []) (counter := (Counter.empty : Counter ν))
    (pre := []) (post := [])
    SeenPath.root (counterMatchesSeen_nil (ν := ν) input)
    h_valid h_root h_leaves h_min h_valid h_input

set_option maxHeartbeats 1000000 in
set_option linter.unusedSectionVars false in
theorem gen_sound (cfg : @CFG α ν) n input : sound cfg n (gen (μ := List) cfg n) input := by
  unfold gen
  let p (counter : Counter ν)
      (parser : (n : ν) → ParserM (tag := tag cfg) α List (tag cfg n)) :=
    ∀ input,
      (∀ n,
        lower_result_sound cfg n (parser n) input ∧
          lower_result_bounded cfg (parser n) input ∧
          lower_memo_wellFormed cfg (parser n) input) ∧
      (∀ n,
        counter[n]? ≠ some 0 →
        ∀ memo : MemoData (tag cfg) List,
          memo_wellFormed cfg input memo →
          ∀ start : ℕ,
          ∀ _h_no_cache :
            (memo.getD n ⊥)[(Counter.toKey counter, start)]? = none,
            memo_wellFormed cfg input
                ((((gen' (μ := List) cfg
                    (memoize (counter.dec n (input.size - start + 1))
                      (gen' (μ := List) cfg))
                    n).lower start)
                  memo input).2.val) ∧
              resultMap_sound cfg n
                ((((gen' (μ := List) cfg
                    (memoize (counter.dec n (input.size - start + 1))
                      (gen' (μ := List) cfg))
                    n).lower start)
                  memo input).1) ∧
              resultMap_bounded cfg input start
                ((((gen' (μ := List) cfg
                    (memoize (counter.dec n (input.size - start + 1))
                      (gen' (μ := List) cfg))
                    n).lower start)
                  memo input).1))
  have h_all : p Counter.empty (memoize (g := gen' (μ := List) cfg)) := by
    refine memoize_counter_induction (g := gen' (μ := List) cfg) p ?_
    intro counter h_ind input
    have h_body_current :
        ∀ n,
          counter[n]? ≠ some 0 →
          ∀ memo : MemoData (tag cfg) List,
            memo_wellFormed cfg input memo →
            ∀ start : ℕ,
            ∀ _h_no_cache :
              (memo.getD n ⊥)[(Counter.toKey counter, start)]? = none,
              memo_wellFormed cfg input
                  ((((gen' (μ := List) cfg
                      (memoize (counter.dec n (input.size - start + 1))
                        (gen' (μ := List) cfg))
                      n).lower start)
                    memo input).2.val) ∧
                resultMap_sound cfg n
                  ((((gen' (μ := List) cfg
                      (memoize (counter.dec n (input.size - start + 1))
                        (gen' (μ := List) cfg))
                      n).lower start)
                    memo input).1) ∧
                resultMap_bounded cfg input start
                  ((((gen' (μ := List) cfg
                      (memoize (counter.dec n (input.size - start + 1))
                        (gen' (μ := List) cfg))
                      n).lower start)
                    memo input).1) := by
      intro current h_counter memo h_memo start h_no_cache
      have h_lower :=
        lower_gen'_result_sound_bounded_memoize
          (cfg := cfg)
          (counter := counter.dec current (input.size - start + 1))
          (g := gen' (μ := List) cfg)
          current input
          (by
            intro child h_child memo' h_memo' start' h_no_cache'
            exact (h_ind current (input.size - start + 1)
              h_counter input).2 child h_child memo' h_memo' start'
              h_no_cache')
      exact ⟨h_lower.2.2 memo h_memo start,
        resultMap_sound_of_lower_result_sound h_lower.1 memo h_memo start,
        resultMap_bounded_of_lower_result_bounded h_lower.2.1 memo h_memo start⟩
    constructor
    · intro current
      by_cases h_counter : counter[current]? = some 0
      · exact ⟨by
          simpa [memoize, h_counter] using
            lower_failure_result_sound cfg current input,
          by
            simpa [memoize, h_counter] using
              lower_failure_bounded cfg input,
          by
            simpa [memoize, h_counter] using
              lower_failure_memo_wellFormed cfg input⟩
      · exact ⟨
          lower_result_sound_memoize
            (cfg := cfg) (input := input)
            counter (gen' (μ := List) cfg)
            (n := current)
            (by
              intro memo h_memo start h_no_cache
              exact (h_body_current current h_counter memo h_memo start
                h_no_cache).2.1),
          lower_result_bounded_memoize
            (cfg := cfg) (input := input)
            counter (gen' (μ := List) cfg)
            (n := current)
            (by
              intro memo h_memo start h_no_cache
              exact (h_body_current current h_counter memo h_memo start
                h_no_cache).2.2),
          lower_memo_wellFormed_memoize
            (cfg := cfg) (input := input)
            counter (gen' (μ := List) cfg)
            (n := current)
            (by
              intro memo h_memo start h_no_cache
              exact h_body_current current h_counter memo h_memo start
                h_no_cache)⟩
    · exact h_body_current
  exact sound_of_lower_result_sound ((h_all input).1 n).1

-- Generated-parser completeness.
--
theorem gen_complete_exists
  {cfg : @CFG α ν} {n : ν} {input : Array α}
  (h : cfg.derives [Symbol.nonterm n] (input.toList.map Symbol.term)) :
    ∃ tree,
      tree ∈ (runParser (tag := tag cfg) (gen (μ := List) cfg n) input 0).1.getD input.size [] ∧
      tree.Valid ∧
      tree.root = Symbol.nonterm n ∧
      tree.leaves = input.toList := by
  obtain ⟨tree, h_valid, h_root, h_leaves, h_min⟩ :=
    exists_minimal_valid_tree_of_derives
      (cfg := cfg) (n := n) (input := input) h
  have h_adm :
      AdmissibleTree cfg input tree 0 :=
    minimal_valid_tree_admissible
      (cfg := cfg) (n := n) (input := input)
      (tree := tree) h_valid h_root h_leaves h_min
  exact gen_complete_exists_of_admissible_valid_tree
    (cfg := cfg) (n := n) (input := input)
    (tree := tree) h_adm h_valid h_root h_leaves

theorem gen_complete (cfg : @CFG α ν) n input :
    complete cfg n (gen (μ := List) cfg n) input := by
  intro h
  exact gen_complete_exists (cfg := cfg) (n := n) (input := input) h

theorem gen_correct (cfg : @CFG α ν) n input :
    sound cfg n (gen (μ := List) cfg n) input ∧
    complete cfg n (gen (μ := List) cfg n) input := by
  exact ⟨gen_sound cfg n input, gen_complete cfg n input⟩

end Gen
