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


abbrev generatedListSymbolParser
  (cfg : @CFG α ν)
  (counter : Counter ν)
  (g : ((t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg)) →
      (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg)) :
    Symbol α ν → ParserM (tag := tag cfg) α List (ParseTree cfg)
  | Symbol.term a => Leaf (cfg := cfg) <$> terminal' (tag := tag cfg) a
  | Symbol.nonterm n => memoize counter g n

abbrev generatedSymbolParser
  (cfg : @CFG α ν)
  (recur : ν → ParserM (tag := tag cfg) α List (ParseTree cfg)) :
    Symbol α ν → ParserM (tag := tag cfg) α List (ParseTree cfg)
  | Symbol.term a => Leaf (cfg := cfg) <$> terminal' (tag := tag cfg) a
  | Symbol.nonterm n => recur n

abbrev generatedRuleParser
  (cfg : @CFG α ν)
  (recur : ν → ParserM (tag := tag cfg) α List (ParseTree cfg))
  (n : ν)
  (rule : {rule // rule ∈ cfg.rules n}) :
    ParserM (tag := tag cfg) α List (ParseTree cfg) :=
  Node n rule <$>
    List.traverse id (rule.val.map (generatedSymbolParser cfg recur))

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

private abbrev PositionMap (cfg : @CFG α ν) :=
  Std.HashMap (MemoEntryKey ν) (ResultMap List (ParseTree cfg))

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

omit [BEq α] [DecidableEq α] [Fintype ν] in
private theorem positionMap_cache_of_mem
    {cfg : @CFG α ν}
    {positionMap : PositionMap cfg}
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

private abbrev PositionEntries
    (cfg : @CFG α ν)
    (P : MemoEntryKey ν → ResultMap List (ParseTree cfg) → Prop)
    (positionMap : PositionMap cfg) :=
  ∀ entry resultMap, positionMap[entry]? = some resultMap → P entry resultMap

omit [Fintype ν] in
private theorem positionEntries_union
    {cfg : @CFG α ν}
    {P : MemoEntryKey ν → ResultMap List (ParseTree cfg) → Prop}
    {left right : PositionMap cfg}
    (h_sup :
      ∀ entry {left right},
        P entry left →
        P entry right →
        P entry (left.unionSup right))
    (h_quot :
      ∀ entry {left right},
        Quotient.mk
            (Std.HashMap.isSetoid (s := List.memSetoid (ParseTree cfg))) left =
          Quotient.mk
            (Std.HashMap.isSetoid (s := List.memSetoid (ParseTree cfg))) right →
        P entry right →
        P entry left)
    (h_left : PositionEntries cfg P left)
    (h_right : PositionEntries cfg P right) :
    PositionEntries cfg P (positionMapUnion cfg left right) := by
  intro entry resultMap h_cache
  let emptyResultMap : ResultMap List (ParseTree cfg) :=
    Std.HashMap.emptyWithCapacity
  have h_entry : entry ∈ positionMapUnion cfg left right := by
    by_contra h_not_mem
    have h_none := Std.HashMap.getElem?_eq_none
      (m := positionMapUnion cfg left right) (a := entry) h_not_mem
    rw [h_cache] at h_none
    simp at h_none
  have h_output_eq :
      (positionMapUnion cfg left right).getD entry emptyResultMap = resultMap := by
    rw [Std.HashMap.getD_eq_getD_getElem?, h_cache]
    simp
  by_cases h_left_entry : entry ∈ left
  · have h_left_cache :
        left[entry]? = some (left.getD entry emptyResultMap) :=
      positionMap_cache_of_mem
        (cfg := cfg) (positionMap := left) h_left_entry
    have h_left_good :=
      h_left entry (left.getD entry emptyResultMap) h_left_cache
    by_cases h_right_entry : entry ∈ right
    · have h_right_cache :
          right[entry]? = some (right.getD entry emptyResultMap) :=
        positionMap_cache_of_mem
          (cfg := cfg) (positionMap := right) h_right_entry
      have h_right_good :=
        h_right entry (right.getD entry emptyResultMap) h_right_cache
      have h_union := Std.HashMap.unionSup_getD_both
        (s := Std.HashMap.isSetoid
          (s := List.memSetoid (ParseTree cfg)))
        (semi := Std.HashMap.instSemilatticeoidIsSetoid
          (s := List.memSetoid (ParseTree cfg))
          (semi := List.instSemilatticeAlt.instSemilatticeoidInstSetoid))
        (m₁ := left) (m₂ := right) h_left_entry h_right_entry
      have h_eq :
          Quotient.mk
              (Std.HashMap.isSetoid (s := List.memSetoid (ParseTree cfg)))
              resultMap =
            Quotient.mk
              (Std.HashMap.isSetoid (s := List.memSetoid (ParseTree cfg)))
              ((left.getD entry emptyResultMap).unionSup
                (right.getD entry emptyResultMap)) := by
        rw [← h_output_eq]
        simpa [positionMapUnion, emptyResultMap, Max.max,
          Std.HashMap.getElem_eq_getD
            (m := left) (a := entry) (fallback := emptyResultMap),
          Std.HashMap.getElem_eq_getD
            (m := right) (a := entry) (fallback := emptyResultMap)]
          using h_union
      exact h_quot entry h_eq (h_sup entry h_left_good h_right_good)
    · have h_union := Std.HashMap.unionSup_getD_of_right_not_contains
        (s := Std.HashMap.isSetoid
          (s := List.memSetoid (ParseTree cfg)))
        (semi := Std.HashMap.instSemilatticeoidIsSetoid
          (s := List.memSetoid (ParseTree cfg))
          (semi := List.instSemilatticeAlt.instSemilatticeoidInstSetoid))
        (fallback := emptyResultMap) left right h_right_entry
      have h_eq :
          Quotient.mk
              (Std.HashMap.isSetoid (s := List.memSetoid (ParseTree cfg)))
              resultMap =
            Quotient.mk
              (Std.HashMap.isSetoid (s := List.memSetoid (ParseTree cfg)))
              (left.getD entry emptyResultMap) := by
        rw [← h_output_eq]
        simpa [positionMapUnion, emptyResultMap] using h_union
      exact h_quot entry h_eq h_left_good
  · by_cases h_right_entry : entry ∈ right
    · have h_right_cache :
          right[entry]? = some (right.getD entry emptyResultMap) :=
        positionMap_cache_of_mem
          (cfg := cfg) (positionMap := right) h_right_entry
      have h_right_good :=
        h_right entry (right.getD entry emptyResultMap) h_right_cache
      have h_union := Std.HashMap.unionSup_getD_of_not_contains
        (s := Std.HashMap.isSetoid
          (s := List.memSetoid (ParseTree cfg)))
        (semi := Std.HashMap.instSemilatticeoidIsSetoid
          (s := List.memSetoid (ParseTree cfg))
          (semi := List.instSemilatticeAlt.instSemilatticeoidInstSetoid))
        (fallback := emptyResultMap) left right h_left_entry
      have h_eq :
          Quotient.mk
              (Std.HashMap.isSetoid (s := List.memSetoid (ParseTree cfg)))
              resultMap =
            Quotient.mk
              (Std.HashMap.isSetoid (s := List.memSetoid (ParseTree cfg)))
              (right.getD entry emptyResultMap) := by
        rw [← h_output_eq]
        simpa [positionMapUnion, emptyResultMap] using h_union
      exact h_quot entry h_eq h_right_good
    · have h_mem_or : entry ∈ left ∨ entry ∈ right := by
        exact (Std.HashMap.mem_of_unionSup_mem
          (s := Std.HashMap.isSetoid
            (s := List.memSetoid (ParseTree cfg)))
          (semi := Std.HashMap.instSemilatticeoidIsSetoid
            (s := List.memSetoid (ParseTree cfg))
            (semi := List.instSemilatticeAlt.instSemilatticeoidInstSetoid))
          (m₁ := left) (m₂ := right)
          (k := entry)).mp (by simpa [positionMapUnion] using h_entry)
      cases h_mem_or with
      | inl h_mem => exact False.elim (h_left_entry h_mem)
      | inr h_mem => exact False.elim (h_right_entry h_mem)

private abbrev MemoEntries
    (cfg : @CFG α ν)
    (P : (n : ν) → MemoEntryKey ν → ResultMap List (ParseTree cfg) → Prop)
    (memo : MemoData (tag cfg) List) :=
  ∀ n entry resultMap,
    (memo.getD n ⊥)[entry]? = some resultMap →
    P n entry resultMap

omit [Fintype ν] in
private theorem memoEntries_sup
    {cfg : @CFG α ν}
    {P : (n : ν) → MemoEntryKey ν → ResultMap List (ParseTree cfg) → Prop}
    {left right : MemoData (tag cfg) List}
    (h_sup :
      ∀ n entry {left right},
        P n entry left →
        P n entry right →
        P n entry (left.unionSup right))
    (h_quot :
      ∀ n entry {left right},
        Quotient.mk
            (Std.HashMap.isSetoid (s := List.memSetoid (ParseTree cfg))) left =
          Quotient.mk
            (Std.HashMap.isSetoid (s := List.memSetoid (ParseTree cfg))) right →
        P n entry right →
        P n entry left)
    (h_left : MemoEntries cfg P left)
    (h_right : MemoEntries cfg P right) :
    MemoEntries cfg P (left ⊔ right) := by
  intro n entry resultMap h_cache
  let emptyPositionMap : PositionMap cfg := Std.HashMap.emptyWithCapacity
  have h_left_position :
      PositionEntries cfg (P n) (left.getD n emptyPositionMap) := by
    intro entry resultMap h_entry
    exact h_left n entry resultMap (by
      simpa [emptyPositionMap, Bot.bot] using h_entry)
  have h_right_position :
      PositionEntries cfg (P n) (right.getD n emptyPositionMap) := by
    intro entry resultMap h_entry
    exact h_right n entry resultMap (by
      simpa [emptyPositionMap, Bot.bot] using h_entry)
  have h_empty_position :
      PositionEntries cfg (P n) emptyPositionMap := by
    intro entry resultMap h_entry
    simp [emptyPositionMap] at h_entry
  change
    ((Std.DHashMap.unionWith
      (fun _ => positionMapUnion cfg)
      (fun _ => emptyPositionMap)
      left right).getD n emptyPositionMap)[entry]? = some resultMap at h_cache
  by_cases h_left_n : n ∈ left
  · by_cases h_right_n : n ∈ right
    · rw [Std.DHashMap.getD_eq_getD_get?] at h_cache
      rw [Std.DHashMap.unionWith_getElem_both
        (m₁ := left) (m₂ := right)
        (f := fun _ => positionMapUnion cfg)
        (z := fun _ => emptyPositionMap)
        h_left_n h_right_n] at h_cache
      exact positionEntries_union
        (cfg := cfg) (P := P n)
        (h_sup n) (h_quot n)
        (by
          simpa [Std.DHashMap.get_eq_getD
            (m := left) (a := n) (fallback := emptyPositionMap)
            (h := h_left_n)] using h_left_position)
        (by
          simpa [Std.DHashMap.get_eq_getD
            (m := right) (a := n) (fallback := emptyPositionMap)
            (h := h_right_n)] using h_right_position)
        entry resultMap h_cache
    · rw [Std.DHashMap.getD_eq_getD_get?] at h_cache
      rw [Std.DHashMap.unionWith_getElem_not_contains_right
        (m₁ := left) (m₂ := right)
        (f := fun _ => positionMapUnion cfg)
        (z := fun _ => emptyPositionMap)
        h_right_n] at h_cache
      rw [Std.DHashMap.get?_eq_some_get h_left_n] at h_cache
      exact positionEntries_union
        (cfg := cfg) (P := P n)
        (h_sup n) (h_quot n)
        h_left_position h_empty_position
        entry resultMap (by
          simpa [Std.DHashMap.get_eq_getD
            (m := left) (a := n) (fallback := emptyPositionMap)
            (h := h_left_n)] using h_cache)
  · by_cases h_right_n : n ∈ right
    · rw [Std.DHashMap.getD_eq_getD_get?] at h_cache
      rw [Std.DHashMap.unionWith_getElem_not_contains
        (m₁ := left) (m₂ := right)
        (f := fun _ => positionMapUnion cfg)
        (z := fun _ => emptyPositionMap)
        h_left_n] at h_cache
      rw [Std.DHashMap.get?_eq_some_get h_right_n] at h_cache
      exact positionEntries_union
        (cfg := cfg) (P := P n)
        (h_sup n) (h_quot n)
        h_empty_position h_right_position
        entry resultMap (by
          simpa [Std.DHashMap.get_eq_getD
            (m := right) (a := n) (fallback := emptyPositionMap)
            (h := h_right_n)] using h_cache)
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
      rw [Std.DHashMap.getD_eq_getD_get?, h_union_none] at h_cache
      simp [emptyPositionMap] at h_cache

omit [BEq α] [DecidableEq α] [Fintype ν] in
private theorem memoEntries_getD
    {cfg : @CFG α ν}
    {P : (n : ν) → MemoEntryKey ν → ResultMap List (ParseTree cfg) → Prop}
    {memo : MemoData (tag cfg) List}
    (h_empty :
      ∀ n entry,
        P n entry
          (Std.HashMap.emptyWithCapacity :
            ResultMap List (ParseTree cfg)))
    (h_memo : MemoEntries cfg P memo) :
    ∀ n entry,
      P n entry
        ((memo.getD n ⊥).getD entry
          (Std.HashMap.emptyWithCapacity :
            ResultMap List (ParseTree cfg))) := by
  intro n entry
  rw [Std.HashMap.getD_eq_getD_getElem?]
  cases h_entry : (memo.getD n ⊥)[entry]? with
  | none =>
      exact h_empty n entry
  | some resultMap =>
      exact h_memo n entry resultMap h_entry

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

theorem memo_sound_sup
    {cfg : @CFG α ν} {input : Array α}
    {left right : MemoData (tag cfg) List}
    (h_left : memo_sound cfg input left)
    (h_right : memo_sound cfg input right) :
    memo_sound cfg input (left ⊔ right) := by
  let P :
      (n : ν) → MemoEntryKey ν → ResultMap List (ParseTree cfg) → Prop :=
    fun n _ resultMap => resultMap_sound cfg n resultMap
  have h_entries : MemoEntries cfg P (left ⊔ right) :=
    memoEntries_sup
      (P := P)
      (fun n _ _ _ h_left h_right =>
        resultMap_sound_sup h_left h_right)
      (fun n _ _ _ h_eq h_right =>
        resultMap_sound_of_quot_eq h_eq h_right)
      (by
        intro n entry resultMap h_cache
        rcases entry with ⟨key, start⟩
        have h_result :
            (left.getD n ⊥).getD (key, start)
                (Std.HashMap.emptyWithCapacity :
                  ResultMap List (ParseTree cfg)) =
              resultMap := by
          rw [Std.HashMap.getD_eq_getD_getElem?, h_cache]
          rfl
        rw [← h_result]
        exact resultMap_sound_of_memo_sound h_left n key start)
      (by
        intro n entry resultMap h_cache
        rcases entry with ⟨key, start⟩
        have h_result :
            (right.getD n ⊥).getD (key, start)
                (Std.HashMap.emptyWithCapacity :
                  ResultMap List (ParseTree cfg)) =
              resultMap := by
          rw [Std.HashMap.getD_eq_getD_getElem?, h_cache]
          rfl
        rw [← h_result]
        exact resultMap_sound_of_memo_sound h_right n key start)
  intro n key start
  simpa [P, cachedResultMap, Bot.bot] using
    (memoEntries_getD
      (P := P)
      (fun n _ => resultMap_sound_empty cfg n)
      h_entries n (key, start))

theorem memo_bounded_sup
    {cfg : @CFG α ν} {input : Array α}
    {left right : MemoData (tag cfg) List}
    (h_left : memo_bounded cfg input left)
    (h_right : memo_bounded cfg input right) :
    memo_bounded cfg input (left ⊔ right) := by
  let P :
      (n : ν) → MemoEntryKey ν → ResultMap List (ParseTree cfg) → Prop :=
    fun _ entry resultMap =>
      resultMap_bounded cfg input entry.2 resultMap
  have h_entries : MemoEntries cfg P (left ⊔ right) :=
    memoEntries_sup
      (P := P)
      (fun _ _ _ _ h_left h_right =>
        resultMap_bounded_sup h_left h_right)
      (fun _ _ _ _ h_eq h_right =>
        resultMap_bounded_of_quot_eq h_eq h_right)
      (by
        intro n entry resultMap h_cache
        rcases entry with ⟨key, start⟩
        have h_result :
            (left.getD n ⊥).getD (key, start)
                (Std.HashMap.emptyWithCapacity :
                  ResultMap List (ParseTree cfg)) =
              resultMap := by
          rw [Std.HashMap.getD_eq_getD_getElem?, h_cache]
          rfl
        rw [← h_result]
        exact resultMap_bounded_of_memo_bounded h_left n key start)
      (by
        intro n entry resultMap h_cache
        rcases entry with ⟨key, start⟩
        have h_result :
            (right.getD n ⊥).getD (key, start)
                (Std.HashMap.emptyWithCapacity :
                  ResultMap List (ParseTree cfg)) =
              resultMap := by
          rw [Std.HashMap.getD_eq_getD_getElem?, h_cache]
          rfl
        rw [← h_result]
        exact resultMap_bounded_of_memo_bounded h_right n key start)
  intro n key start
  simpa [P, cachedResultMap, Bot.bot] using
    (memoEntries_getD
      (P := P)
      (fun _ entry => resultMap_bounded_empty cfg input entry.2)
      h_entries n (key, start))

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
  rw [Traversable.foldl_toList, Traversable.toList_eq_self]
  exact List.foldlRecOn actions joinUnderCache h_acc (by
    intro current h_current action h_action
    exact joinUnderCache_memo_wellFormed
      (cfg := cfg) (input := input)
      (acc := current) (act := action)
      h_current (h_actions action h_action))

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
  exact
    List.foldlRecOn groups (Traversable.foldl joinUnderCache) h_acc (by
      intro current h_current group h_group
      exact traversable_foldl_joinUnderCache_memo_wellFormed
        (cfg := cfg) (input := input)
        (actions := group) (acc := current)
        h_current (h_groups group h_group))

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
  have h_body_memo_body : memo_wellFormed cfg input body.2.val := by
    simpa [body] using h_body_memo
  have h_join :
      memo_wellFormed cfg input
        (memoWithCachedResult cfg body.2.val n
          (Counter.toKey counter) start
          (body.1.unionSup (cachedResultMap cfg body.2.val n
            (Counter.toKey counter) start))) :=
    memo_wellFormed_memoWithCachedResult
      h_body_memo_body
      (resultMap_sound_sup
        (by simpa [body] using h_body_sound)
        (resultMap_sound_of_memo_sound h_body_memo_body.1
          n (Counter.toKey counter) start))
      (resultMap_bounded_sup
        (by simpa [body] using h_body_bounded)
        (resultMap_bounded_of_memo_bounded h_body_memo_body.2
          n (Counter.toKey counter) start))
  rw [memoizeStep_compute_snd_val_eq
    (counter := counter) (g := g) (next := next) (t := n)
    (memo := memo) (input := input) (start := start)
    h_no_cache]
  simpa [MemoData.cacheInsertSup, Std.HashMap.insertSup,
    memoWithCachedResult, cachedResultMap, Std.HashMap.instMax, Bot.bot, body]
    using h_join

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

set_option linter.unusedSectionVars false in
theorem memo_wellFormed_memoizeStep_of_guarded_body
  {cfg : @CFG α ν} {input : Array α}
  (counter : Counter ν)
  (g : ((t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg)) →
      (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  {n : ν}
  (h_body :
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
    ∀ start,
      ∀ memo : MemoData (tag cfg) List,
        memo_wellFormed cfg input memo →
        memo_wellFormed cfg input
          (((memoizeStep counter g n
            (fun fuel => memoize (counter.dec n fuel) g) start)
            memo input).2.val) := by
  intro start memo h_memo
  exact memo_wellFormed_memoizeStep
    (cfg := cfg) (input := input)
    (counter := counter) (g := g)
    (next := fun fuel => memoize (counter.dec n fuel) g)
    (n := n) (memo := memo) (start := start)
    h_memo
    (fun h_no_cache => h_body memo h_memo start h_no_cache)


omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
lemma list_sizeOf_replace_lt
  {δ : Type u} [SizeOf δ]
  {before after : List δ} {old new : δ}
  (h_lt : sizeOf new < sizeOf old) :
    sizeOf (before ++ new :: after) < sizeOf (before ++ old :: after) := by
  induction before <;> simp_all

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
  have hi : before.length < xs.length := by
    simp only [List.length_append, List.length_cons] at h_len
    omega
  refine ⟨xs.take before.length, xs[before.length],
    xs.drop (before.length + 1), ?_, ?_⟩
  · calc
      xs = xs.take before.length ++ xs.drop before.length :=
        (List.take_append_drop before.length xs).symm
      _ = xs.take before.length ++
          xs[before.length] :: xs.drop (before.length + 1) := by
        rw [List.drop_eq_getElem_cons hi]
  · simp [Nat.le_of_lt hi]

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
lemma valid_node_child_valid_of_split
  {cfg : @CFG α ν}
  {n : ν} {rule : {rule // rule ∈ cfg.rules n}}
  {before after : List (ParseTree cfg)} {child : ParseTree cfg}
  (h_valid : (Node (cfg := cfg) n rule (before ++ child :: after)).Valid) :
    child.Valid := by
  have h_len := (valid_node_iff_ForestValid.mp h_valid).1
  let j : Fin (before ++ child :: after).length :=
    ⟨before.length, by simp⟩
  let i : Fin rule.val.length := ⟨before.length, by rw [h_len]; simp⟩
  have h_child := valid_node_child_at h_valid i j rfl
  simpa [j] using h_child.1

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
abbrev SpanVisit (ν : Type u) := ν × ℕ × ℕ

omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
abbrev nodeSpanVisit {cfg : @CFG α ν}
  (n : ν) (start : ℕ) (tree : ParseTree cfg) : SpanVisit ν :=
  (n, start, start + tree.leaves.length)


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

abbrev lower_memo_complete (cfg : @CFG α ν)
  {γ : Type u} [DecidableEq γ]
  (p : ParserM (tag := tag cfg) α List γ) (input : Array α)
  :=
  ∀ memo : MemoData (tag cfg) List,
  memo_complete cfg input memo →
  ∀ start : ℕ,
    memo_complete cfg input (((p.lower start) memo input).2.val)

private abbrev GeneratedFamily (cfg : @CFG α ν) :=
  (n : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg)

private abbrev GeneratedGenerator (cfg : @CFG α ν) :=
  GeneratedFamily cfg → GeneratedFamily cfg

private abbrev memoizedBody
    (cfg : @CFG α ν) (input : Array α)
    (counter : Counter ν) (g : GeneratedGenerator cfg)
    (n : ν) (start : ℕ) : ParserM (tag := tag cfg) α List (ParseTree cfg) :=
  g (memoize (counter.dec n (input.size - start + 1)) g) n

private abbrev GeneratedBodySafety
    (cfg : @CFG α ν) (input : Array α)
    (counter : Counter ν) (g : GeneratedGenerator cfg) : Prop :=
  ∀ n,
    counter[n]? ≠ some 0 →
    ∀ memo : MemoData (tag cfg) List,
      memo_wellFormed cfg input memo →
      ∀ start : ℕ,
      ∀ _h_no_cache :
        (memo.getD n ⊥)[(Counter.toKey counter, start)]? = none,
        memo_wellFormed cfg input
            ((((memoizedBody cfg input counter g n start).lower start)
              memo input).2.val) ∧
          resultMap_sound cfg n
            ((((memoizedBody cfg input counter g n start).lower start)
              memo input).1) ∧
          resultMap_bounded cfg input start
            ((((memoizedBody cfg input counter g n start).lower start)
              memo input).1)

private abbrev GeneratedFamilySafety
    (cfg : @CFG α ν) (input : Array α)
    (parser : GeneratedFamily cfg) : Prop :=
  ∀ n,
    lower_result_sound cfg n (parser n) input ∧
      lower_result_bounded cfg (parser n) input ∧
      lower_memo_wellFormed cfg (parser n) input

private abbrev GeneratedSoundCounterInvariant
    (cfg : @CFG α ν) (counter : Counter ν)
    (parser : GeneratedFamily cfg) : Prop :=
  ∀ input,
    GeneratedFamilySafety cfg input parser ∧
      GeneratedBodySafety cfg input counter (gen' (μ := List) cfg)

private abbrev GeneratedBodyCompleteness
    (cfg : @CFG α ν) (input : Array α)
    (counter : Counter ν) (g : GeneratedGenerator cfg) : Prop :=
  ∀ n,
    counter[n]? ≠ some 0 →
    ∀ memo : MemoData (tag cfg) List,
      memo_complete cfg input memo →
      ∀ start : ℕ,
      ∀ _h_no_cache :
        (memo.getD n ⊥)[(Counter.toKey counter, start)]? = none,
        memo_complete cfg input
            ((((memoizedBody cfg input counter g n start).lower start)
              memo input).2.val) ∧
          resultMap_complete cfg input n (Counter.toKey counter) start
            ((((memoizedBody cfg input counter g n start).lower start)
              memo input).1)

private abbrev GeneratedTreeCompleteness
    (cfg : @CFG α ν) (input : Array α)
    (counter : Counter ν) (parser : GeneratedFamily cfg) : Prop :=
  ∀ {n : ν} {memo : MemoData (tag cfg) List}
    {pre post : List α} {seen : List (SpanVisit ν)}
    {tree : ParseTree cfg},
    memo_complete cfg input memo →
    tree.root = Symbol.nonterm n →
    AdmissibleTreeWith cfg input seen counter tree pre.length →
    tree.Valid →
    input.toList = pre ++ tree.leaves ++ post →
    tree ∈
      (((parser n).lower pre.length) memo input).1.getD
        (pre.length + tree.leaves.length) []

private abbrev GeneratedCompleteCounterInvariant
    (cfg : @CFG α ν) (input : Array α)
    (counter : Counter ν) (parser : GeneratedFamily cfg) : Prop :=
  (∀ n, lower_memo_complete cfg (parser n) input) ∧
    GeneratedBodyCompleteness cfg input counter (gen' (μ := List) cfg) ∧
    GeneratedTreeCompleteness cfg input counter parser

omit [Fintype ν] in
theorem lower_map_memo_complete
  {cfg : @CFG α ν} {γ δ : Type u} [DecidableEq γ] [DecidableEq δ]
  {p : ParserM (tag := tag cfg) α List γ} {f : γ → δ}
  {input : Array α}
  (h : lower_memo_complete cfg p input) :
    lower_memo_complete cfg (f <$> p) input := by
  intro memo h_memo start
  rw [lower_map_snd_val_eq
    (tag := tag cfg) (β := α)
    (p := p) (f := f)
    (memo := memo) (input := input) (start := start)]
  exact h memo h_memo start

omit [Fintype ν] in
theorem joinUnderCache_memo_complete
  {cfg : @CFG α ν} {γ : Type u} [DecidableEq γ]
  {input : Array α}
  (acc act :
    MStateT (MemoData (tag cfg) List) (ReaderM (Array α))
      (ResultMap List γ))
  (h_acc :
    ∀ memo : MemoData (tag cfg) List,
      memo_complete cfg input memo →
      memo_complete cfg input ((acc memo input).2.val))
  (h_act :
    ∀ memo : MemoData (tag cfg) List,
      memo_complete cfg input memo →
      memo_complete cfg input ((act memo input).2.val)) :
    ∀ memo : MemoData (tag cfg) List,
      memo_complete cfg input memo →
      memo_complete cfg input ((joinUnderCache acc act memo input).2.val) := by
  intro memo h_memo
  rw [joinUnderCache_snd_eq]
  exact h_act _ (h_acc memo h_memo)

omit [Fintype ν] in
theorem traversable_foldl_joinUnderCache_memo_complete
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
      memo_complete cfg input memo →
      memo_complete cfg input ((acc memo input).2.val))
  (h_actions :
    ∀ action ∈ actions,
      ∀ memo : MemoData (tag cfg) List,
        memo_complete cfg input memo →
        memo_complete cfg input ((action memo input).2.val)) :
    ∀ memo : MemoData (tag cfg) List,
      memo_complete cfg input memo →
      memo_complete cfg input
        (((Traversable.foldl joinUnderCache acc actions) memo input).2.val) := by
  rw [Traversable.foldl_toList, Traversable.toList_eq_self]
  exact List.foldlRecOn actions joinUnderCache h_acc (by
    intro current h_current action h_action
    exact joinUnderCache_memo_complete
      (cfg := cfg) (input := input)
      (acc := current) (act := action)
      h_current (h_actions action h_action))

omit [Fintype ν] in
theorem list_foldl_traversable_joinUnderCache_memo_complete
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
      memo_complete cfg input memo →
      memo_complete cfg input ((acc memo input).2.val))
  (h_groups :
    ∀ group ∈ groups, ∀ action ∈ group,
      ∀ memo : MemoData (tag cfg) List,
        memo_complete cfg input memo →
        memo_complete cfg input ((action memo input).2.val)) :
    ∀ memo : MemoData (tag cfg) List,
      memo_complete cfg input memo →
      memo_complete cfg input
        (((List.foldl (Traversable.foldl joinUnderCache) acc groups)
          memo input).2.val) := by
  exact
    List.foldlRecOn groups (Traversable.foldl joinUnderCache) h_acc (by
      intro current h_current group h_group
      exact traversable_foldl_joinUnderCache_memo_complete
        (cfg := cfg) (input := input)
        (actions := group) (acc := current)
        h_current (h_groups group h_group))

omit [Fintype ν] in
theorem bindContinue_memo_complete
  {cfg : @CFG α ν} {δ γ : Type u} [DecidableEq γ]
  {input : Array α}
  (resultMap : ResultMap List δ)
  (f : δ → Parser (tag := tag cfg) α List γ)
  (h_f :
    ∀ a start,
      ∀ memo : MemoData (tag cfg) List,
        memo_complete cfg input memo →
        memo_complete cfg input (((f a start) memo input).2.val)) :
    ∀ memo : MemoData (tag cfg) List,
      memo_complete cfg input memo →
      memo_complete cfg input
        ((Parser.bindContinue (tag := tag cfg) (β := α)
          resultMap f memo input).2.val) := by
  unfold Parser.bindContinue Parser.bindActions
  exact list_foldl_traversable_joinUnderCache_memo_complete
    (cfg := cfg) (input := input)
    (groups := resultMap.toList.map
      (fun pair : ℕ × List δ =>
        match pair with
        | (j, values) => List.map (fun a => f a j) values))
    (acc := pure Std.HashMap.emptyWithCapacity)
    (by
      intro memo h_memo
      simp [Pure.pure, ReaderT.pure]
      intro n counter pre post seen tree resultMap h_cache h_root h_adm
        h_valid h_input
      exact h_memo h_cache h_root h_adm h_valid h_input)
    (by
      intro group h_group action h_action memo h_memo
      rw [List.mem_map] at h_group
      rcases h_group with ⟨pair, _h_pair, rfl⟩
      rcases pair with ⟨j, values⟩
      simp at h_action
      rcases h_action with ⟨a, _h_a, rfl⟩
      exact h_f a j memo h_memo)

omit [Fintype ν] in
theorem parser_bind_memo_complete
  {cfg : @CFG α ν} {δ γ : Type u} [DecidableEq γ]
  {input : Array α}
  (p : Parser (tag := tag cfg) α List δ)
  (f : δ → Parser (tag := tag cfg) α List γ)
  (h_p :
    ∀ start,
      ∀ memo : MemoData (tag cfg) List,
        memo_complete cfg input memo →
        memo_complete cfg input (((p start) memo input).2.val))
  (h_f :
    ∀ a start,
      ∀ memo : MemoData (tag cfg) List,
        memo_complete cfg input memo →
        memo_complete cfg input (((f a start) memo input).2.val)) :
    ∀ start,
      ∀ memo : MemoData (tag cfg) List,
        memo_complete cfg input memo →
        memo_complete cfg input
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
  exact bindContinue_memo_complete
    (cfg := cfg) (input := input)
    (resultMap := ((p start) memo input).1)
    (f := f)
    h_f
    (↑((p start) memo input).2)
    (h_p start memo h_memo)

omit [Fintype ν] in
theorem lower_bind_constructor_memo_complete
  {cfg : @CFG α ν} {δ γ : Type u} [DecidableEq γ]
  {input : Array α}
  (p : Parser (tag := tag cfg) α List δ)
  (k : δ → ParserM (tag := tag cfg) α List γ)
  (h_p :
    ∀ start,
      ∀ memo : MemoData (tag cfg) List,
        memo_complete cfg input memo →
        memo_complete cfg input (((p start) memo input).2.val))
  (h_k :
    ∀ a, lower_memo_complete cfg (k a) input) :
    lower_memo_complete cfg (ParserM.Bind p k) input := by
  intro memo h_memo start
  change memo_complete cfg input
    (((Parser.bind p (fun a => (k a).lower) start) memo input).2.val)
  exact parser_bind_memo_complete
    (cfg := cfg) (input := input)
    (p := p) (f := fun a => (k a).lower)
    h_p
    (fun a start memo h_memo => h_k a memo h_memo start)
    start memo h_memo

omit [Fintype ν] in
theorem lower_lift_memo_complete
  {cfg : @CFG α ν} {γ : Type u} [DecidableEq γ]
  {input : Array α}
  (p : Parser (tag := tag cfg) α List γ)
  (h_p :
    ∀ start,
      ∀ memo : MemoData (tag cfg) List,
        memo_complete cfg input memo →
        memo_complete cfg input (((p start) memo input).2.val)) :
    lower_memo_complete cfg (ParserM.lift p) input := by
  unfold ParserM.lift
  exact lower_bind_constructor_memo_complete
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
theorem bind_action_prefix_memo_complete
  {cfg : @CFG α ν} {δ γ : Type u} [DecidableEq γ]
  {input : Array α}
  (p : Parser (tag := tag cfg) α List δ)
  (k : δ → ParserM (tag := tag cfg) α List γ)
  (prePairs : List (ℕ × List δ)) (preValues : List δ)
  (split start : ℕ) {memo : MemoData (tag cfg) List}
  (h_p :
    ∀ start,
      ∀ memo : MemoData (tag cfg) List,
        memo_complete cfg input memo →
        memo_complete cfg input (((p start) memo input).2.val))
  (h_k : ∀ a, lower_memo_complete cfg (k a) input)
  (h_memo : memo_complete cfg input memo) :
    memo_complete cfg input
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
  have h_after_p : memo_complete cfg input ((p start memo input).2.val) :=
    h_p start memo h_memo
  have h_tail_prefix :
      ∀ action ∈ List.map (fun a => (k a).lower split) preValues,
        ∀ memo : MemoData (tag cfg) List,
          memo_complete cfg input memo →
          memo_complete cfg input ((action memo input).2.val) := by
    intro action h_action memo h_memo
    rw [List.mem_map] at h_action
    rcases h_action with ⟨a, _h_a, rfl⟩
    exact h_k a memo h_memo split
  change memo_complete cfg input
    (((Traversable.foldl joinUnderCache
      (List.foldl (Traversable.foldl joinUnderCache)
        (pure Std.HashMap.emptyWithCapacity)
        (List.map pairAction prePairs))
      (List.map (fun a => (k a).lower split) preValues))
      (↑((p start) memo input).2) input).2.val)
  exact traversable_foldl_joinUnderCache_memo_complete
    (cfg := cfg) (input := input)
    (actions := List.map (fun a => (k a).lower split) preValues)
    (acc := List.foldl (Traversable.foldl joinUnderCache)
      (pure Std.HashMap.emptyWithCapacity)
      (List.map pairAction prePairs))
    (by
      intro memo' h_memo'
      exact list_foldl_traversable_joinUnderCache_memo_complete
        (cfg := cfg) (input := input)
        (groups := List.map pairAction prePairs)
        (acc := pure Std.HashMap.emptyWithCapacity)
        (by
          intro memo h_memo
          simp [Pure.pure, ReaderT.pure]
          intro n counter pre post seen tree resultMap h_cache h_root h_adm
            h_valid h_input
          exact h_memo h_cache h_root h_adm h_valid h_input)
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
theorem parser_pure_memo_complete
  {cfg : @CFG α ν} {γ : Type u}
  {input : Array α} (x : γ) :
    ∀ start,
      ∀ memo : MemoData (tag cfg) List,
        memo_complete cfg input memo →
        memo_complete cfg input
          (((Pure.pure x : Parser (tag := tag cfg) α List γ) start)
            memo input).2.val := by
  intro start memo h_memo
  simp [Pure.pure, ReaderT.pure]
  intro n counter pre post seen tree resultMap h_cache h_root h_adm
    h_valid h_input
  exact h_memo h_cache h_root h_adm h_valid h_input

omit [Fintype ν] in
theorem parser_orElse_memo_complete
  {cfg : @CFG α ν} {γ : Type u} [DecidableEq γ]
  {input : Array α}
  (p q : Parser (tag := tag cfg) α List γ)
  (h_p :
    ∀ start,
      ∀ memo : MemoData (tag cfg) List,
        memo_complete cfg input memo →
        memo_complete cfg input (((p start) memo input).2.val))
  (h_q :
    ∀ start,
      ∀ memo : MemoData (tag cfg) List,
        memo_complete cfg input memo →
        memo_complete cfg input (((q start) memo input).2.val)) :
    ∀ start,
      ∀ memo : MemoData (tag cfg) List,
        memo_complete cfg input memo →
        memo_complete cfg input
          (((Parser.orElse p q start) memo input).2.val) := by
  intro start memo h_memo
  unfold Parser.orElse
  exact joinUnderCache_memo_complete
    (cfg := cfg) (input := input)
    (acc := p start) (act := q start)
    (fun memo h_memo => h_p start memo h_memo)
    (fun memo h_memo => h_q start memo h_memo)
    memo h_memo

omit [Fintype ν] in
theorem lower_sup_memo_complete
  {cfg : @CFG α ν} {γ : Type u} [DecidableEq γ]
  {input : Array α}
  (p q : ParserM (tag := tag cfg) α List γ)
  (h_p : lower_memo_complete cfg p input)
  (h_q : lower_memo_complete cfg q input) :
    lower_memo_complete cfg (p ⊔ q) input := by
  cases p with
  | Return x =>
      cases q with
      | Return y =>
          change lower_memo_complete cfg
            (ParserM.Bind
              (Parser.orElse
                (Pure.pure x : Parser (tag := tag cfg) α List γ)
                (Pure.pure y : Parser (tag := tag cfg) α List γ))
              (ParserM.Return (tag := tag cfg) (β := α) (μ := List)))
            input
          exact lower_bind_constructor_memo_complete
            (cfg := cfg) (input := input)
            (p := Parser.orElse
              (Pure.pure x : Parser (tag := tag cfg) α List γ)
              (Pure.pure y : Parser (tag := tag cfg) α List γ))
            (k := ParserM.Return (tag := tag cfg) (β := α) (μ := List))
            (parser_orElse_memo_complete
              (cfg := cfg) (input := input)
              (p := Pure.pure x)
              (q := Pure.pure y)
              (parser_pure_memo_complete (cfg := cfg) (input := input) x)
              (parser_pure_memo_complete (cfg := cfg) (input := input) y))
            (by
              intro a memo h_memo start
              rw [lower_return_snd_val_eq
                (tag := tag cfg) (β := α)
                (a := a) (memo := memo) (input := input) (start := start)]
              exact h_memo)
      | Bind q kq =>
          change lower_memo_complete cfg
            (ParserM.lift
              (Parser.orElse
                (Pure.pure x : Parser (tag := tag cfg) α List γ)
                (Parser.bind q (fun a => (kq a).lower))))
            input
          exact lower_lift_memo_complete
            (cfg := cfg) (input := input)
            (p := Parser.orElse
              (Pure.pure x : Parser (tag := tag cfg) α List γ)
              (Parser.bind q (fun a => (kq a).lower)))
            (parser_orElse_memo_complete
              (cfg := cfg) (input := input)
              (p := Pure.pure x)
              (q := Parser.bind q (fun a => (kq a).lower))
              (parser_pure_memo_complete (cfg := cfg) (input := input) x)
              (by
                intro start memo h_memo
                exact h_q memo h_memo start))
  | Bind p kp =>
      cases q with
      | Return y =>
          change lower_memo_complete cfg
            (ParserM.lift
              (Parser.orElse
                (Parser.bind p (fun a => (kp a).lower))
                (Pure.pure y : Parser (tag := tag cfg) α List γ)))
            input
          exact lower_lift_memo_complete
            (cfg := cfg) (input := input)
            (p := Parser.orElse
              (Parser.bind p (fun a => (kp a).lower))
              (Pure.pure y : Parser (tag := tag cfg) α List γ))
            (parser_orElse_memo_complete
              (cfg := cfg) (input := input)
              (p := Parser.bind p (fun a => (kp a).lower))
              (q := Pure.pure y)
              (by
                intro start memo h_memo
                exact h_p memo h_memo start)
              (parser_pure_memo_complete (cfg := cfg) (input := input) y))
      | Bind q kq =>
          change lower_memo_complete cfg
            (ParserM.lift
              (Parser.orElse
                (Parser.bind p (fun a => (kp a).lower))
                (Parser.bind q (fun a => (kq a).lower))))
            input
          exact lower_lift_memo_complete
            (cfg := cfg) (input := input)
            (p := Parser.orElse
              (Parser.bind p (fun a => (kp a).lower))
              (Parser.bind q (fun a => (kq a).lower)))
            (parser_orElse_memo_complete
              (cfg := cfg) (input := input)
              (p := Parser.bind p (fun a => (kp a).lower))
              (q := Parser.bind q (fun a => (kq a).lower))
              (by
                intro start memo h_memo
                exact h_p memo h_memo start)
              (by
                intro start memo h_memo
                exact h_q memo h_memo start))

omit [Fintype ν] in
theorem lower_memo_complete_of_foldl_sup
  {cfg : @CFG α ν} {γ : Type u} [DecidableEq γ]
  {input : Array α}
  (parsers : List (ParserM (tag := tag cfg) α List γ))
  (acc : ParserM (tag := tag cfg) α List γ)
  (h_acc : lower_memo_complete cfg acc input)
  (h_parsers : ∀ p ∈ parsers, lower_memo_complete cfg p input) :
    lower_memo_complete cfg
      (parsers.foldl ParserM.instMaxOfTraversableOfDecidableEq.max acc)
      input := by
  exact List.foldlRecOn parsers
    ParserM.instMaxOfTraversableOfDecidableEq.max h_acc (by
      intro current h_current parser h_parser
      exact lower_sup_memo_complete
        (cfg := cfg) (input := input)
        current parser h_current (h_parsers parser h_parser))

omit [BEq α] [DecidableEq α] [Monad μ] [SemilatticeAlt μ] [Traversable μ]
  [Fintype ν] in
theorem memo_complete_empty (cfg : @CFG α ν) (input : Array α) :
    memo_complete cfg input (startState : MemoData (tag cfg) List) := by
  intro n counter pre post seen tree resultMap h_cache _h_root _h_adm _h_valid _h_input
  simp [startState, Bot.bot] at h_cache


theorem memo_complete_sup
    {cfg : @CFG α ν} {input : Array α}
    {left right : MemoData (tag cfg) List}
    (h_left : memo_complete cfg input left)
    (h_right : memo_complete cfg input right) :
    memo_complete cfg input (left ⊔ right) := by
  let P :
      (n : ν) → MemoEntryKey ν → ResultMap List (ParseTree cfg) → Prop :=
    fun n entry resultMap =>
      resultMap_complete cfg input n entry.1 entry.2 resultMap
  have h_entries : MemoEntries cfg P (left ⊔ right) :=
    memoEntries_sup
      (P := P)
      (by
        intro n entry leftMap rightMap h_left _h_right
        intro counter pre post seen tree h_key h_start h_root h_adm
          h_valid h_input
        exact resultMap_mem_unionSup_left
          (h_left h_key h_start h_root h_adm h_valid h_input))
      (by
        intro n entry leftMap rightMap h_eq h_right
        intro counter pre post seen tree h_key h_start h_root h_adm
          h_valid h_input
        have h_right_mem :=
          h_right h_key h_start h_root h_adm h_valid h_input
        have h_equiv :
            Std.HashMap.EquivQuot
              (s := List.memSetoid (ParseTree cfg)) leftMap rightMap :=
          Quotient.exact h_eq
        have h_getD := Std.HashMap.EquivQuot.getD_eq
          (s := List.memSetoid (ParseTree cfg))
          (k := pre.length + tree.leaves.length) (fallback := []) h_equiv
        simp [List.memSetoid, Subset, List.Subset] at h_getD
        exact @h_getD.2 tree h_right_mem)
      (by
        intro n entry resultMap h_cache
        rcases entry with ⟨key, start⟩
        intro counter pre post seen tree h_key h_start h_root h_adm
          h_valid h_input
        exact h_left
          (by simpa [h_key, h_start] using h_cache)
          h_root h_adm h_valid h_input)
      (by
        intro n entry resultMap h_cache
        rcases entry with ⟨key, start⟩
        intro counter pre post seen tree h_key h_start h_root h_adm
          h_valid h_input
        exact h_right
          (by simpa [h_key, h_start] using h_cache)
          h_root h_adm h_valid h_input)
  intro n counter pre post seen tree resultMap h_cache h_root h_adm
    h_valid h_input
  exact
    (h_entries n (Counter.toKey counter, pre.length) resultMap h_cache)
      rfl rfl h_root h_adm h_valid h_input

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
  have h_join_result :
      resultMap_complete cfg input n (Counter.toKey counter) start
        (body.1.unionSup (cachedResultMap cfg body.2.val n
          (Counter.toKey counter) start)) := by
    intro counter' pre post seen tree h_key h_start h_root h_adm
      h_valid h_input
    exact resultMap_mem_unionSup_left
      (h_body_result_body h_key h_start h_root h_adm h_valid h_input)
  have h_join :
      memo_complete cfg input
        (memoWithCachedResult cfg body.2.val n
          (Counter.toKey counter) start
          (body.1.unionSup (cachedResultMap cfg body.2.val n
            (Counter.toKey counter) start))) :=
    memo_complete_memoWithCachedResult
      (cfg := cfg) (input := input)
      h_body_memo_body h_join_result
  rw [memoizeStep_compute_snd_val_eq
    (counter := counter) (g := g) (next := next) (t := n)
    (memo := memo) (input := input) (start := start)
    h_no_cache]
  change memo_complete cfg input
    (memoWithCachedResult cfg body.2.val n
      (Counter.toKey counter) start
      (body.1.unionSup (cachedResultMap cfg body.2.val n
        (Counter.toKey counter) start)))
  exact h_join

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

set_option linter.unusedSectionVars false in
theorem lower_memo_complete_memoizeStep_lift
  {cfg : @CFG α ν} {input : Array α}
  (counter : Counter ν)
  (g : ((t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg)) →
      (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  (next : ℕ → (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  {n : ν}
  (h_compute :
    ∀ memo : MemoData (tag cfg) List,
      memo_complete cfg input memo →
      ∀ start : ℕ,
      ∀ _h_no_cache :
        (memo.getD n ⊥)[(Counter.toKey counter, start)]? = none,
        memo_complete cfg input
            ((((g (next (input.size - start + 1)) n).lower start)
              memo input).2.val) ∧
          resultMap_complete cfg input n (Counter.toKey counter) start
            ((((g (next (input.size - start + 1)) n).lower start)
              memo input).1)) :
    lower_memo_complete cfg
      (ParserM.lift (memoizeStep counter g n next)) input := by
  intro memo h_memo start
  rw [lower_lift_snd_val_eq
    (tag := tag cfg) (β := α)
    (p := memoizeStep counter g n next)
    (memo := memo) (input := input) (start := start)]
  exact memo_complete_memoizeStep
    (cfg := cfg) (input := input)
    (counter := counter) (g := g) (next := next)
    (n := n) (memo := memo) (start := start)
    h_memo
    (fun h_no_cache => h_compute memo h_memo start h_no_cache)

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
theorem counter_dec_self_getElem?
  (counter : Counter ν) (t : ν) (fuel : ℕ) :
    (counter.dec t fuel)[t]? = some (counter.getD t fuel - 1) := by
  change ((counter : Std.HashMap ν ℕ).insert t (counter.getD t fuel - 1))[t]? =
    some (counter.getD t fuel - 1)
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


omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
def counterForSeen (input : Array α) : List (SpanVisit ν) → Counter ν
  | [] => Counter.empty
  | visit :: seen =>
      (counterForSeen input seen).dec visit.1 (input.size - visit.2.1 + 1)


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
def spanVisitCount (t : ν) : List (SpanVisit ν) → ℕ
  | [] => 0
  | visit :: seen =>
      (if visit.1 = t then 1 else 0) + spanVisitCount t seen


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
theorem counter_getElem?_eq_of_toKey_eq
  {left right : Counter ν}
  (h_key : Counter.toKey left = Counter.toKey right)
  (t : ν) :
    left[t]? = right[t]? := by
  apply Option.ext
  intro value
  change left.unwrap[t]? = some value ↔ right.unwrap[t]? = some value
  rw [← Std.HashMap.mem_toList_iff_getElem?_eq_some,
    ← Std.HashMap.mem_toList_iff_getElem?_eq_some]
  change ((t, value) ∈ Counter.toKey left) ↔
    ((t, value) ∈ Counter.toKey right)
  rw [h_key]


omit [BEq α] [DecidableEq α] [Fintype ν] in
theorem counter_dec_getElem?_eq_of_getElem?_eq
  {left right : Counter ν}
  (h_eq : ∀ t : ν, left[t]? = right[t]?)
  (n t : ν) (fuel : ℕ) :
    (left.dec n fuel)[t]? = (right.dec n fuel)[t]? := by
  by_cases h_t : t = n
  · subst t
    rw [counter_dec_self_getElem?, counter_dec_self_getElem?]
    simpa [Std.HashMap.getD_eq_getD_getElem?] using
      congrArg (fun value => some (value.getD fuel - 1)) (h_eq n)
  · have h_ne : n ≠ t := Ne.symm h_t
    rw [counter_dec_other_getElem? (counter := left) (fuel := fuel) h_ne,
      counter_dec_other_getElem? (counter := right) (fuel := fuel) h_ne,
      h_eq t]

set_option linter.unusedSectionVars false in
mutual
  theorem admissibleTreeWith_congr_counter_getElem?
    {cfg : @CFG α ν} {input : Array α}
    {seen : List (SpanVisit ν)} {left right : Counter ν}
    {tree : ParseTree cfg} {start : ℕ}
    (h_eq : ∀ t : ν, left[t]? = right[t]?)
    (h_adm : AdmissibleTreeWith cfg input seen left tree start) :
      AdmissibleTreeWith cfg input seen right tree start := by
    cases h_adm with
    | leaf =>
        constructor
    | node rule children h_no_cycle h_budget h_children =>
        exact AdmissibleTreeWith.node
          (cfg := cfg) (input := input) seen right
          h_no_cycle
          (by
            intro h_zero
            rw [← h_eq _] at h_zero
            exact h_budget h_zero)
          (admissibleForestWith_congr_counter_getElem?
            (cfg := cfg) (input := input)
            (by
              intro t
              exact counter_dec_getElem?_eq_of_getElem?_eq
                (left := left) (right := right) h_eq _ t _)
            h_children)

  theorem admissibleForestWith_congr_counter_getElem?
    {cfg : @CFG α ν} {input : Array α}
    {seen : List (SpanVisit ν)} {left right : Counter ν}
    {children : List (ParseTree cfg)} {start : ℕ}
    (h_eq : ∀ t : ν, left[t]? = right[t]?)
    (h_adm : AdmissibleForestWith cfg input seen left children start) :
      AdmissibleForestWith cfg input seen right children start := by
    cases h_adm with
    | nil =>
        exact AdmissibleForestWith.nil
          (cfg := cfg) (input := input) seen right start
    | cons child children h_child h_tail =>
        exact AdmissibleForestWith.cons
          (cfg := cfg) (input := input) seen right
          (admissibleTreeWith_congr_counter_getElem?
            (cfg := cfg) (input := input) (seen := seen)
            h_eq h_child)
          (admissibleForestWith_congr_counter_getElem?
            (cfg := cfg) (input := input) (seen := seen)
            h_eq h_tail)
end


omit [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν] in
abbrev CounterMatchesSeen
  (input : Array α) (seen : List (SpanVisit ν)) (counter : Counter ν) : Prop :=
  counter = counterForSeen input seen

omit [BEq α] [DecidableEq α] [Fintype ν] in
theorem counterMatchesSeen_nil (input : Array α) :
    CounterMatchesSeen (ν := ν) input [] (Counter.empty : Counter ν) := by
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

omit [Fintype ν] in
theorem lower_rule_branch_result_sound_of_traverse
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
        ForestValid (cfg := cfg) rule.val subtrees) :
    lower_result_sound cfg n
      (Node n rule <$> List.traverse id (rule.val.map mkParser)) input := by
  apply lower_map_result_sound_of_forall
  intro memo h_memo start end_ subtrees h_subtrees
  exact ⟨valid_node_iff_ForestValid.mpr
      (h_children memo h_memo start end_ subtrees h_subtrees),
    by simp [ParseTree.root]⟩

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
theorem lower_rule_branch_memo_complete_of_traverse
  {cfg : @CFG α ν}
  {n : ν} {rule : {rule // rule ∈ cfg.rules n}}
  {mkParser : Symbol α ν → ParserM (tag := tag cfg) α List (ParseTree cfg)}
  {input : Array α}
  (h_children :
    lower_memo_complete cfg
      (List.traverse id (rule.val.map mkParser)) input) :
    lower_memo_complete cfg
      (Node n rule <$> List.traverse id (rule.val.map mkParser)) input := by
  exact lower_map_memo_complete
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


omit [Fintype ν] in
theorem lower_memo_complete_traverse_cons_terminal
  {cfg : @CFG α ν}
  {a : α}
  {tail : List (ParserM (tag := tag cfg) α List (ParseTree cfg))}
  {input : Array α}
  (h_tail :
    lower_memo_complete cfg (List.traverse id tail) input) :
    lower_memo_complete cfg
      (List.traverse id
        ((Leaf (cfg := cfg) <$> terminal' (tag := tag cfg) a) :: tail))
      input := by
  rw [List.traverse, seq_eq_bind]
  simp
  change lower_memo_complete cfg
    (ParserM.Bind (terminalPrimitive (tag := tag cfg) a)
      (fun x =>
        (ParserM.Return (tag := tag cfg) (β := α) (μ := List)
          (Leaf (cfg := cfg) x) >>= fun tree =>
            List.cons tree <$> List.traverse id tail)))
    input
  exact lower_bind_constructor_memo_complete
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
      change lower_memo_complete cfg
        (List.cons (Leaf (cfg := cfg) x) <$> List.traverse id tail) input
      exact lower_map_memo_complete
        (cfg := cfg)
        (p := List.traverse id tail)
        (f := List.cons (Leaf (cfg := cfg) x))
        h_tail)

omit [Fintype ν] in
theorem lower_memo_complete_traverse_cons_lift
  {cfg : @CFG α ν}
  {p : Parser (tag := tag cfg) α List (ParseTree cfg)}
  {tail : List (ParserM (tag := tag cfg) α List (ParseTree cfg))}
  {input : Array α}
  (h_p :
    ∀ start,
      ∀ memo : MemoData (tag cfg) List,
        memo_complete cfg input memo →
        memo_complete cfg input (((p start) memo input).2.val))
  (h_tail :
    lower_memo_complete cfg (List.traverse id tail) input) :
    lower_memo_complete cfg
      (List.traverse id ((ParserM.lift p) :: tail)) input := by
  rw [List.traverse, seq_eq_bind]
  simp
  change lower_memo_complete cfg
    (ParserM.Bind p (fun x => List.cons x <$> List.traverse id tail)) input
  exact lower_bind_constructor_memo_complete
    (cfg := cfg) (input := input)
    (p := p)
    (k := fun x => List.cons x <$> List.traverse id tail)
    h_p
    (by
      intro x
      exact lower_map_memo_complete
        (cfg := cfg)
        (p := List.traverse id tail)
        (f := List.cons x)
        h_tail)

omit [Fintype ν] in
theorem lower_memo_complete_traverse_cons_failure
  {cfg : @CFG α ν}
  {tail : List (ParserM (tag := tag cfg) α List (ParseTree cfg))}
  {input : Array α}
  (h_tail :
    lower_memo_complete cfg (List.traverse id tail) input) :
    lower_memo_complete cfg
      (List.traverse id
        ((⊥ : ParserM (tag := tag cfg) α List (ParseTree cfg)) :: tail))
      input := by
  simpa [Bot.bot] using
    lower_memo_complete_traverse_cons_lift
      (cfg := cfg)
      (p := (Parser.failure :
        Parser (tag := tag cfg) α List (ParseTree cfg)))
      (tail := tail) (input := input)
      (by
        intro start memo h_memo
        simp [Parser.failure, ReaderT.pure, Pure.pure]
        intro n counter pre post seen tree resultMap h_cache h_root h_adm
          h_valid h_input
        exact h_memo h_cache h_root h_adm h_valid h_input)
      h_tail

set_option linter.unusedSectionVars false in
theorem lower_memo_complete_traverse_cons_memoize
  {cfg : @CFG α ν}
  (counter : Counter ν)
  (g : ((t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg)) →
      (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  (n : ν)
  {tail : List (ParserM (tag := tag cfg) α List (ParseTree cfg))}
  {input : Array α}
  (h_step :
    counter[n]? ≠ some 0 →
    ∀ start,
      ∀ memo : MemoData (tag cfg) List,
        memo_complete cfg input memo →
        memo_complete cfg input
          (((memoizeStep counter g n
            (fun fuel => memoize (counter.dec n fuel) g) start)
            memo input).2.val))
  (h_tail :
    lower_memo_complete cfg (List.traverse id tail) input) :
    lower_memo_complete cfg
      (List.traverse id ((memoize counter g n) :: tail)) input := by
  by_cases h_counter : counter[n]? = some 0
  · simpa [memoize, h_counter] using
      lower_memo_complete_traverse_cons_failure
        (cfg := cfg) (tail := tail) (input := input) h_tail
  · simpa [memoize, h_counter] using
      lower_memo_complete_traverse_cons_lift
        (cfg := cfg)
        (p := memoizeStep counter g n
          (fun fuel => memoize (counter.dec n fuel) g))
        (tail := tail) (input := input)
        (h_step h_counter) h_tail

set_option linter.unusedSectionVars false in
theorem lower_memo_complete_generated_traverse_memoize
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
        memo_complete cfg input memo →
        memo_complete cfg input
          (((memoizeStep counter g n
            (fun fuel => memoize (counter.dec n fuel) g) start)
            memo input).2.val)) :
    lower_memo_complete cfg
      (List.traverse id
        (rule.map (generatedListSymbolParser cfg counter g)))
      input := by
  induction rule with
  | nil =>
      intro memo h_memo start
      change memo_complete cfg input
        (↑(((ParserM.Return (tag := tag cfg) (β := α) (μ := List)
          ([] : List (ParseTree cfg))).lower start) memo input).2)
      rw [lower_return_snd_val_eq
        (tag := tag cfg) (β := α)
        (a := ([] : List (ParseTree cfg)))
        (memo := memo) (input := input) (start := start)]
      exact h_memo
  | cons sym rest ih =>
      cases sym with
      | term a =>
          change lower_memo_complete cfg
            (List.traverse id
              ((Leaf (cfg := cfg) <$> terminal' (tag := tag cfg) a) ::
                rest.map (generatedListSymbolParser cfg counter g)))
            input
          exact lower_memo_complete_traverse_cons_terminal
            (cfg := cfg) (a := a)
            (tail := rest.map (generatedListSymbolParser cfg counter g))
            (input := input) ih
      | nonterm n =>
          change lower_memo_complete cfg
            (List.traverse id
              ((memoize counter g n) ::
                rest.map (generatedListSymbolParser cfg counter g)))
            input
          exact lower_memo_complete_traverse_cons_memoize
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
private lemma forestPairValid_replace_same_root
  {cfg : @CFG α ν}
  {sym : Symbol α ν} {old new : ParseTree cfg}
  (h_pair : ForestPairValid (cfg := cfg) (sym, old))
  (h_new_valid : new.Valid)
  (h_root : new.root = old.root) :
    ForestPairValid (cfg := cfg) (sym, new) := by
  rw [ForestPairValid_iff_valid_and_root] at h_pair ⊢
  exact ⟨h_new_valid, h_root.trans h_pair.2⟩

private theorem forall₂_replace_right
    {γ : Type u} {δ : Type u} {R : γ → δ → Prop}
    {leftBefore leftAfter : List γ} {rightBefore rightAfter : List δ}
    {pivot : γ} {old new : δ}
    (h : List.Forall₂ R
      (leftBefore ++ pivot :: leftAfter)
      (rightBefore ++ old :: rightAfter))
    (h_len : leftBefore.length = rightBefore.length)
    (h_new : R pivot new) :
    List.Forall₂ R
      (leftBefore ++ pivot :: leftAfter)
      (rightBefore ++ new :: rightAfter) := by
  have h_prefix := List.forall₂_take_append
    (leftBefore ++ pivot :: leftAfter) rightBefore (old :: rightAfter) h
  have h_rest := List.forall₂_drop_append
    (leftBefore ++ pivot :: leftAfter) rightBefore (old :: rightAfter) h
  have h_prefix' : List.Forall₂ R leftBefore rightBefore := by
    simpa [h_len] using h_prefix
  have h_rest' : List.Forall₂ R (pivot :: leftAfter) (old :: rightAfter) := by
    simpa [h_len] using h_rest
  cases h_rest' with
  | cons _ h_tail =>
      exact List.rel_append h_prefix' (.cons h_new h_tail)

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
  have h_pairs :=
    ForestValid_iff_forall₂.mp (valid_node_iff_ForestValid.mp h_valid)
  rw [h_rule] at h_pairs
  have h_rest := List.forall₂_drop_append
    (ruleBefore ++ sym :: ruleAfter) before (old :: after) h_pairs
  have h_rest' :
      List.Forall₂
        (fun symbol tree => ForestPairValid (cfg := cfg) (symbol, tree))
        (sym :: ruleAfter) (old :: after) := by
    simpa [h_before_len] using h_rest
  have h_old_pair : ForestPairValid (cfg := cfg) (sym, old) := by
    cases h_rest' with
    | cons h_head _ => exact h_head
  have h_new_pair := forestPairValid_replace_same_root
    (cfg := cfg) h_old_pair h_new_valid h_root
  have h_pairs_new :=
    forall₂_replace_right h_pairs h_before_len h_new_pair
  refine ⟨valid_node_iff_ForestValid.mpr
      (ForestValid_iff_forall₂.mpr ?_),
    rfl, ?_, node_sizeOf_replace_child_lt (cfg := cfg) h_size⟩
  · simpa [h_rule] using h_pairs_new
  · rw [ParseTree.leaves_node_eq_forestLeaves,
      ParseTree.leaves_node_eq_forestLeaves]
    simp [ParseTree.forestLeaves, h_leaves]

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
lemma lower_rule_branch_complete
  {cfg : @CFG α ν}
  {n : ν} {rule : List (Symbol α ν)}
  (h_rule : rule ∈ cfg.rules n)
  {mkParser : Symbol α ν → ParserM (tag := tag cfg) α List (ParseTree cfg)}
  {memo : MemoData (tag cfg) List} {input : Array α}
  {start end_ : ℕ} {subtrees : List (ParseTree cfg)}
  (h_children :
    subtrees ∈
      (((List.traverse id (rule.map mkParser)).lower start)
        memo input).1.getD end_ []) :
    Node (cfg := cfg) n ⟨rule, h_rule⟩ subtrees ∈
      (((Node n ⟨rule, h_rule⟩ <$>
          List.traverse id (rule.map mkParser)).lower start)
        memo input).1.getD end_ [] := by
  exact mem_lower_map_of_mem
    (tag := tag cfg) (β := α)
    (p := List.traverse id (rule.map mkParser))
    (f := Node n ⟨rule, h_rule⟩)
    (memo := memo) (input := input)
    (start := start) (end_pos := end_)
    (x := subtrees) h_children


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
theorem lower_return_bind_cons_memo_complete
  {cfg : @CFG α ν} {γ : Type u} [DecidableEq γ]
  {tail : List (ParserM (tag := tag cfg) α List γ)}
  {input : Array α} {x : γ}
  (h_tail : lower_memo_complete cfg (List.traverse id tail) input) :
    lower_memo_complete cfg
      ((ParserM.Return (tag := tag cfg) (β := α) (μ := List) x) >>=
        fun y => List.cons y <$> List.traverse id tail)
      input := by
  change lower_memo_complete cfg
    (List.cons x <$> List.traverse id tail) input
  exact lower_map_memo_complete
    (cfg := cfg) (p := List.traverse id tail)
    (f := List.cons x) h_tail

set_option maxHeartbeats 700000 in
omit [Fintype ν] in
lemma lower_traverse_complete_cons_lift_of_head_tail_complete
  {cfg : @CFG α ν}
  {tail : List (ParserM (tag := tag cfg) α List (ParseTree cfg))}
  {memo : MemoData (tag cfg) List} {input : Array α}
  {start split end_ : ℕ}
  {result_head : ParseTree cfg} {result_tail : List (ParseTree cfg)}
  (p : Parser (tag := tag cfg) α List (ParseTree cfg))
  (h_complete : memo_complete cfg input memo)
  (h_p_memo :
    ∀ start,
      ∀ memo : MemoData (tag cfg) List,
        memo_complete cfg input memo →
        memo_complete cfg input (((p start) memo input).2.val))
  (h_tail_memo :
    lower_memo_complete cfg (List.traverse id tail) input)
  (h_head :
    result_head ∈ ((p start) memo input).1.getD split [])
  (h_tail :
    ∀ memoTail : MemoData (tag cfg) List,
      memo_complete cfg input memoTail →
      result_tail ∈
        (((List.traverse id tail).lower split) memoTail input).1.getD end_ []) :
    result_head :: result_tail ∈
      (((List.traverse id ((ParserM.lift p) :: tail)).lower start)
        memo input).1.getD end_ [] := by
  rw [Std.HashMap.getD_eq_getD_getElem?] at h_head
  cases h_get : ((p start) memo input).1[split]? with
  | none =>
      simp [h_get] at h_head
  | some values =>
      simp [h_get] at h_head
      refine mem_lower_traverse_complete_cons_of_bind_getElem_action_mem
        (tag := tag cfg) (β := α)
        (p := p)
        (k := fun x =>
          ParserM.Return (tag := tag cfg) (β := α) (μ := List) x)
        (tail := tail)
        (split := split) (values := values) (a := result_head)
        (memo := memo) (input := input)
        (start := start) (end_pos := end_)
        (x := result_head) (xs := result_tail)
        h_get h_head ?_
      intro prePairs _postPairs preValues _postValues _h_toList _h_values
      let memoPrefix : MemoData (tag cfg) List :=
        ↑((Traversable.foldl joinUnderCache
          (List.foldl (Traversable.foldl joinUnderCache)
            (pure Std.HashMap.emptyWithCapacity)
            (List.map
              (fun pair : ℕ × List (ParseTree cfg) =>
                match pair with
                | (j, values) =>
                    List.map
                      (fun a =>
                        (((ParserM.Return (tag := tag cfg) (β := α)
                          (μ := List) a) >>= fun a =>
                          List.cons a <$> List.traverse id tail).lower j))
                      values)
              prePairs))
          (List.map
            (fun a =>
              (((ParserM.Return (tag := tag cfg) (β := α) (μ := List) a)
                >>= fun a => List.cons a <$> List.traverse id tail).lower split))
            preValues))
          (↑((p start) memo input).2) input).2
      have h_continue_memo :
          ∀ x : ParseTree cfg,
            lower_memo_complete cfg
              ((ParserM.Return (tag := tag cfg) (β := α) (μ := List) x)
                >>= fun y => List.cons y <$> List.traverse id tail)
              input := by
        intro x
        exact lower_return_bind_cons_memo_complete
          (cfg := cfg) (tail := tail) (input := input)
          (x := x) h_tail_memo
      have h_prefix :
          memo_complete cfg input memoPrefix := by
        intro n counter pre post seen tree resultMap h_cache h_root h_adm
          h_valid h_input
        exact
          (bind_action_prefix_memo_complete
            (cfg := cfg) (input := input)
            (p := p)
            (k := fun x =>
              (ParserM.Return (tag := tag cfg) (β := α) (μ := List) x)
                >>= fun y => List.cons y <$> List.traverse id tail)
            (prePairs := prePairs) (preValues := preValues)
            (split := split) (start := start)
            (memo := memo)
            (h_p := h_p_memo) (h_k := h_continue_memo)
            (h_memo := h_complete))
            (by simpa [memoPrefix] using h_cache)
            h_root h_adm h_valid h_input
      have h_tail_mem := h_tail memoPrefix h_prefix
      change result_head :: result_tail ∈
        ((((ParserM.Return (tag := tag cfg) (β := α) (μ := List)
              result_head) >>=
            fun y => List.cons y <$> List.traverse id tail).lower split)
          memoPrefix input).1.getD end_ []
      exact lower_return_bind_cons_complete
        (cfg := cfg) (tail := tail)
        (memo := memoPrefix) (input := input)
        (start := split) (end_ := end_)
        (x := result_head) (xs := result_tail) h_tail_mem

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

set_option maxHeartbeats 1000000 in
theorem lower_generated_traverse_complete_of_admissible_valid_forest
  {cfg : @CFG α ν}
  (counter : Counter ν)
  (g : ((t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg)) →
      (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  {rule : List (Symbol α ν)} {children : List (ParseTree cfg)}
  {input : Array α} {memo : MemoData (tag cfg) List}
  {seen : List (SpanVisit ν)} {pre post : List α}
  (h_complete : memo_complete cfg input memo)
  (h_adm :
    AdmissibleForestWith cfg input seen counter children pre.length)
  (h_forest : ForestValid (cfg := cfg) rule children)
  (h_input : input.toList = pre ++ forestLeaves (cfg := cfg) children ++ post)
  (h_step :
    ∀ n,
      counter[n]? ≠ some 0 →
      ∀ start,
      ∀ memo : MemoData (tag cfg) List,
        memo_complete cfg input memo →
        memo_complete cfg input
          (((memoizeStep counter g n
            (fun fuel => memoize (counter.dec n fuel) g) start)
            memo input).2.val))
  (h_recur :
    ∀ {memo : MemoData (tag cfg) List},
      memo_complete cfg input memo →
      ∀ {childN : ν} {rule' : {rule // rule ∈ cfg.rules childN}}
        {grandchildren : List (ParseTree cfg)} {pre' post' : List α},
        Node (cfg := cfg) childN rule' grandchildren ∈ children →
        AdmissibleTreeWith cfg input seen counter
          (Node (cfg := cfg) childN rule' grandchildren) pre'.length →
        (Node (cfg := cfg) childN rule' grandchildren).Valid →
        input.toList =
          pre' ++ (Node (cfg := cfg) childN rule' grandchildren).leaves ++ post' →
        Node (cfg := cfg) childN rule' grandchildren ∈
          (((memoize counter g childN).lower pre'.length) memo input).1.getD
            (pre'.length +
              (Node (cfg := cfg) childN rule' grandchildren).leaves.length) []) :
    children ∈
      (((List.traverse id
        (rule.map (generatedListSymbolParser cfg counter g))).lower pre.length)
        memo input).1.getD
        (pre.length + (forestLeaves (cfg := cfg) children).length) [] := by
  obtain ⟨h_len, h_valid⟩ := h_forest
  induction rule generalizing children pre memo with
  | nil =>
      cases children with
      | nil =>
          have h_return :
              ([] : List (ParseTree cfg)) ∈
                (((ParserM.Return (tag := tag cfg) (β := α) (μ := List)
                    ([] : List (ParseTree cfg))).lower pre.length)
                  memo input).1.getD pre.length [] := by
            exact (mem_lower_return_iff
              (tag := tag cfg) (β := α)
              (a := ([] : List (ParseTree cfg)))
              (x := ([] : List (ParseTree cfg)))
              (memo := memo) (input := input)
              (start := pre.length) (end_pos := pre.length)).mpr
              ⟨rfl, rfl⟩
          simpa [List.traverse, forestLeaves] using h_return
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
              ∀ pair, pair ∈ List.zip rest tail →
                ForestPairValid (cfg := cfg) pair := by
            intro pair h_pair
            exact h_valid pair (by simp [h_pair])
          obtain ⟨h_child_adm, h_tail_adm⟩ :=
            admissible_forest_cons_inv (cfg := cfg) h_adm
          have h_input_tail :
              input.toList =
                (pre ++ child.leaves) ++ forestLeaves (cfg := cfg) tail ++ post := by
            simpa [forestLeaves, List.append_assoc] using h_input
          cases sym with
          | term a =>
              cases child with
              | Leaf b =>
                  have h_ab : a = b := by
                    have h_head :=
                      h_valid (Symbol.term a, Leaf (cfg := cfg) b) (by simp)
                    simpa [ForestPairValid] using h_head
                  cases h_ab
                  have h_term : input[pre.length]? = some a := by
                    simp [← Array.getElem?_toList, h_input, forestLeaves,
                      ParseTree.leaves, List.append_assoc]
                  have h_tail_mem :
                      tail ∈
                        (((List.traverse id
                          (rest.map (generatedListSymbolParser cfg counter g))).lower
                          (pre ++ [a]).length)
                          memo input).1.getD
                          ((pre ++ [a]).length +
                            (forestLeaves (cfg := cfg) tail).length) [] := by
                    exact ih
                      (children := tail) (pre := pre ++ [a])
                      (memo := memo)
                      h_complete
                      (by simpa [ParseTree.leaves] using h_tail_adm)
                      (by
                        simpa [ParseTree.leaves] using h_input_tail)
                      (by
                        intro memo' h_complete' childN rule' grandchildren
                          pre' post' h_mem h_adm_child h_child_valid h_child_input
                        exact h_recur h_complete'
                          (by simp [h_mem])
                          h_adm_child h_child_valid h_child_input)
                      h_len_tail h_tail_valid
                  have h_cons :=
                    lower_traverse_complete_cons_terminal
                      (cfg := cfg) (a := a)
                      (tail := rest.map (generatedListSymbolParser cfg counter g))
                      (memo := memo) (input := input)
                      (start := pre.length)
                      (end_ := (pre ++ [a]).length +
                        (forestLeaves (cfg := cfg) tail).length)
                      (result_tail := tail)
                      h_term
                      (by simpa [List.length_append, ParseTree.leaves] using h_tail_mem)
                  simpa [generatedListSymbolParser, forestLeaves, ParseTree.leaves,
                    List.length_append, Nat.add_assoc, Nat.add_comm,
                    Nat.add_left_comm] using h_cons
              | Node childN rule' grandchildren =>
                  have h_false : False := by
                    have h_head :=
                      h_valid
                        (Symbol.term a,
                          Node (cfg := cfg) childN rule' grandchildren) (by simp)
                    simp [ForestPairValid] at h_head
                  exact False.elim h_false
          | nonterm childN =>
              cases child with
              | Leaf b =>
                  have h_false : False := by
                    have h_head :=
                      h_valid (Symbol.nonterm childN, Leaf (cfg := cfg) b) (by simp)
                    simp [ForestPairValid] at h_head
                  exact False.elim h_false
              | Node n' rule' grandchildren =>
                  have h_child_valid_root :
                      childN = n' ∧
                        (Node (cfg := cfg) n' rule' grandchildren).Valid := by
                    have h_head :=
                      h_valid
                        (Symbol.nonterm childN,
                          Node (cfg := cfg) n' rule' grandchildren) (by simp)
                    simpa [ForestPairValid] using h_head
                  obtain ⟨h_eq, h_child_valid⟩ := h_child_valid_root
                  cases h_eq
                  obtain ⟨_h_no_cycle, h_budget, _h_children_adm⟩ :=
                    admissible_node_inv (cfg := cfg) h_child_adm
                  have h_child_input :
                      input.toList =
                        pre ++
                          (Node (cfg := cfg) childN rule' grandchildren).leaves ++
                          (forestLeaves (cfg := cfg) tail ++ post) := by
                    simpa [forestLeaves, ParseTree.leaves, List.append_assoc]
                      using h_input
                  have h_child_mem :
                      Node (cfg := cfg) childN rule' grandchildren ∈
                        (((memoize counter g childN).lower pre.length)
                          memo input).1.getD
                          (pre.length +
                            (Node (cfg := cfg) childN rule' grandchildren).leaves.length) [] := by
                    exact h_recur h_complete
                      (by simp)
                      h_child_adm h_child_valid h_child_input
                  let step : Parser (tag := tag cfg) α List (ParseTree cfg) :=
                    memoizeStep counter g childN
                      (fun fuel => memoize (counter.dec childN fuel) g)
                  have h_head_lift :
                      Node (cfg := cfg) childN rule' grandchildren ∈
                        (((ParserM.lift step :
                          ParserM (tag := tag cfg) α List (ParseTree cfg)).lower
                          pre.length) memo input).1.getD
                          (pre.length +
                            (Node (cfg := cfg) childN rule' grandchildren).leaves.length) [] := by
                    simpa [memoize, h_budget, step] using h_child_mem
                  have h_head_step :
                      Node (cfg := cfg) childN rule' grandchildren ∈
                        ((step pre.length) memo input).1.getD
                          (pre.length +
                            (Node (cfg := cfg) childN rule' grandchildren).leaves.length) [] := by
                    exact mem_lower_lift_exists_of_mem
                      (tag := tag cfg) (β := α)
                      (p := step)
                      (memo := memo) (input := input)
                      (start := pre.length)
                      (end_pos := pre.length +
                        (Node (cfg := cfg) childN rule' grandchildren).leaves.length)
                      (x := Node (cfg := cfg) childN rule' grandchildren)
                      h_head_lift
                  have h_tail_memo :
                      lower_memo_complete cfg
                        (List.traverse id
                          (rest.map (generatedListSymbolParser cfg counter g)))
                        input :=
                    lower_memo_complete_generated_traverse_memoize
                      (cfg := cfg) counter g rest input h_step
                  have h_tail :
                      ∀ memoTail : MemoData (tag cfg) List,
                        memo_complete cfg input memoTail →
                        tail ∈
                          (((List.traverse id
                            (rest.map (generatedListSymbolParser cfg counter g))).lower
                            (pre.length +
                              (Node (cfg := cfg) childN rule' grandchildren).leaves.length))
                            memoTail input).1.getD
                            (pre.length +
                              (Node (cfg := cfg) childN rule' grandchildren).leaves.length +
                              (forestLeaves (cfg := cfg) tail).length) [] := by
                    intro memoTail h_complete_tail
                    have h_tail_input :
                        input.toList =
                          (pre ++
                            (Node (cfg := cfg) childN rule' grandchildren).leaves) ++
                            forestLeaves (cfg := cfg) tail ++ post := by
                      simpa [List.append_assoc] using h_child_input
                    simpa [List.length_append] using
                      (ih
                        (children := tail)
                        (pre := pre ++
                          (Node (cfg := cfg) childN rule' grandchildren).leaves)
                        (memo := memoTail)
                        h_complete_tail
                        (by
                          simpa [forestLeaves, ParseTree.leaves, List.length_append,
                            Nat.add_assoc] using h_tail_adm)
                        h_tail_input
                        (by
                          intro memo' h_complete' childN' rule'' grandchildren'
                            pre' post' h_mem h_adm_child h_child_valid' h_child_input'
                          exact h_recur h_complete'
                            (by simp [h_mem])
                            h_adm_child h_child_valid' h_child_input')
                        h_len_tail h_tail_valid)
                  have h_cons :=
                    lower_traverse_complete_cons_lift_of_head_tail_complete
                      (cfg := cfg)
                      (tail := rest.map (generatedListSymbolParser cfg counter g))
                      (memo := memo) (input := input)
                      (start := pre.length)
                      (split := pre.length +
                        (Node (cfg := cfg) childN rule' grandchildren).leaves.length)
                      (end_ := pre.length +
                        (Node (cfg := cfg) childN rule' grandchildren).leaves.length +
                        (forestLeaves (cfg := cfg) tail).length)
                      (result_head := Node (cfg := cfg) childN rule' grandchildren)
                      (result_tail := tail)
                      step h_complete
                      (h_step childN h_budget)
                      h_tail_memo
                      h_head_step h_tail
                  simpa [generatedListSymbolParser, memoize, h_budget, step,
                    forestLeaves, ParseTree.leaves, List.length_append,
                    Nat.add_assoc] using h_cons


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
theorem lower_failure_memo_complete
  (cfg : @CFG α ν) (input : Array α) :
    lower_memo_complete cfg
      (⊥ : ParserM (tag := tag cfg) α List (ParseTree cfg)) input := by
  unfold lower_memo_complete
  intro memo h_memo start
  simp [Bot.bot, ParserM.lift, ParserM.lower]
  unfold Parser.failure Parser.bind Parser.bindRun Parser.bindContinue
    Parser.bindActions
  simp [ReaderT.pure, Pure.pure, instMonadMStateT,
    Functor.map, hashMap_emptyWithCapacity_toList_eq_nil]
  exact h_memo

omit [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
theorem lower_gen'_memo_complete_of_rules
  {cfg : @CFG α ν} {input : Array α}
  (recur : ν → ParserM (tag := tag cfg) α List (ParseTree cfg))
  (n : ν)
  (h_rules :
    ∀ rule : {rule // rule ∈ cfg.rules n},
      lower_memo_complete cfg (generatedRuleParser cfg recur n rule) input) :
    lower_memo_complete cfg (gen' (μ := List) cfg recur n) input := by
  have h_fold :
      lower_memo_complete cfg
        (((cfg.rules n).attach.map (generatedRuleParser cfg recur n)).foldl
          ParserM.instMaxOfTraversableOfDecidableEq.max
          (⊥ : ParserM (tag := tag cfg) α List (ParseTree cfg)))
        input :=
    lower_memo_complete_of_foldl_sup
      (cfg := cfg) (input := input)
      ((cfg.rules n).attach.map (generatedRuleParser cfg recur n))
      (⊥ : ParserM (tag := tag cfg) α List (ParseTree cfg))
      (lower_failure_memo_complete cfg input)
      (by
        intro p h_p
        rw [List.mem_map] at h_p
        rcases h_p with ⟨rule, _h_rule, rfl⟩
        exact h_rules rule)
  simpa [gen', generatedRuleParser, generatedSymbolParser] using h_fold


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
theorem lower_memo_complete_memoize
  {cfg : @CFG α ν} {input : Array α}
  (counter : Counter ν)
  (g : ((t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg)) →
      (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  {n : ν}
  (h_compute :
    ∀ memo : MemoData (tag cfg) List,
      memo_complete cfg input memo →
      ∀ start : ℕ,
      ∀ _h_no_cache :
        (memo.getD n ⊥)[(Counter.toKey counter, start)]? = none,
        memo_complete cfg input
            ((((g (memoize (counter.dec n (input.size - start + 1)) g)
                n).lower start)
              memo input).2.val) ∧
          resultMap_complete cfg input n (Counter.toKey counter) start
            ((((g (memoize (counter.dec n (input.size - start + 1)) g)
                n).lower start)
              memo input).1)) :
    lower_memo_complete cfg (memoize counter g n) input := by
  by_cases h_counter : counter[n]? = some 0
  · simpa [memoize, h_counter] using
      lower_failure_memo_complete cfg input
  · simpa [memoize, h_counter] using
      lower_memo_complete_memoizeStep_lift
        (cfg := cfg) (input := input)
        (counter := counter) (g := g)
        (next := fun fuel => memoize (counter.dec n fuel) g)
        (n := n) h_compute

private structure GeneratedTraverseSafety
    {cfg : @CFG α ν} (input : Array α) (rule : List (Symbol α ν))
    (start end_ : ℕ) (subtrees : List (ParseTree cfg)) : Prop where
  forest_valid : ForestValid (cfg := cfg) rule subtrees
  bounds :
    start ≤ input.size → start ≤ end_ ∧ end_ ≤ input.size

set_option linter.unusedSectionVars false in
private theorem lower_generated_traverse_safety_memoize_guarded
  {cfg : @CFG α ν}
  (counter : Counter ν)
  (g : ((t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg)) →
      (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  (rule : List (Symbol α ν)) (input : Array α)
  (h_body : GeneratedBodySafety cfg input counter g) :
    ∀ memo : MemoData (tag cfg) List,
      memo_wellFormed cfg input memo →
      ∀ start end_ : ℕ,
      ∀ subtrees,
        subtrees ∈
          (((List.traverse id
            (rule.map (generatedListSymbolParser cfg counter g))).lower start)
            memo input).1.getD end_ [] →
        GeneratedTraverseSafety input rule start end_ subtrees := by
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
    intro n h_counter
    exact memo_wellFormed_memoizeStep_of_guarded_body
      (cfg := cfg) (input := input)
      (counter := counter) (g := g) (n := n)
      (fun memo h_memo start h_no_cache =>
        h_body n h_counter memo h_memo start h_no_cache)
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
      refine ⟨ForestValid_iff_forall₂.mpr .nil, ?_⟩
      · intro h_start
        cases h_return.1
        exact ⟨le_rfl, h_start⟩
  | cons sym rest ih =>
      intro memo h_memo start end_ subtrees h_mem
      cases subtrees with
      | nil =>
          have h_len := mem_lower_traverse_preserves_length
            (tag := tag cfg) (β := α)
            (xs := (sym :: rest).map
              (generatedListSymbolParser cfg counter g))
            (memo := memo) (input := input)
            (start := start) (end_pos := end_)
            (result := ([] : List (ParseTree cfg))) h_mem
          simp at h_len
      | cons result_head result_tail =>
          have h_tail_memo :
              lower_memo_wellFormed cfg
                (List.traverse id
                  (rest.map (generatedListSymbolParser cfg counter g)))
                input :=
            lower_memo_wellFormed_generated_traverse_memoize_guarded
              (cfg := cfg) counter g rest input h_step_memo
          cases sym with
          | term a =>
              obtain ⟨h_head_eq, _h_head_mem, h_start_succ,
                memo_tail, h_memo_tail, h_tail_mem⟩ :=
                mem_lower_traverse_cons_terminal_exists_tail_wf
                  (cfg := cfg) (a := a)
                  (tail := rest.map (generatedListSymbolParser cfg counter g))
                  (memo := memo) (input := input)
                  (start := start) (end_ := end_)
                  (result_head := result_head) (result_tail := result_tail)
                  h_tail_memo h_memo
                  (by simpa [generatedListSymbolParser] using h_mem)
              have h_tail_safe :=
                ih memo_tail h_memo_tail (start + 1) end_
                  result_tail h_tail_mem
              refine ⟨ForestValid_iff_forall₂.mpr ?_, ?_⟩
              · exact .cons (by simp [ForestPairValid, h_head_eq])
                  (ForestValid_iff_forall₂.mp h_tail_safe.forest_valid)
              · intro _h_start
                have h_tail_bounds := h_tail_safe.bounds h_start_succ
                exact ⟨Nat.le_trans (Nat.le_succ start) h_tail_bounds.1,
                  h_tail_bounds.2⟩
          | nonterm n =>
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
              · obtain ⟨split, memo_tail, h_memo_tail,
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
                      exact
                        (h_body n h_counter memo h_memo start h_no_cache).2.1))
                    memo h_memo start split result_head h_head_mem
                have h_tail_safe :=
                  ih memo_tail h_memo_tail split end_
                    result_tail h_tail_mem
                refine ⟨ForestValid_iff_forall₂.mpr ?_, ?_⟩
                · exact .cons
                    (ForestPairValid_iff_valid_and_root.mpr h_head_sound)
                    (ForestValid_iff_forall₂.mp h_tail_safe.forest_valid)
                · intro h_start
                  have h_head_bounds :=
                    (lower_result_bounded_memoize
                      (cfg := cfg) (input := input)
                      counter g
                      (n := n)
                      (by
                        intro memo h_memo start h_no_cache
                        exact
                          (h_body n h_counter memo h_memo start h_no_cache).2.2))
                      memo h_memo start split h_start result_head h_head_mem
                  have h_tail_bounds :=
                    h_tail_safe.bounds h_head_bounds.2
                  exact ⟨Nat.le_trans h_head_bounds.1 h_tail_bounds.1,
                    h_tail_bounds.2⟩


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
    intro n h_counter
    exact memo_wellFormed_memoizeStep_of_guarded_body
      (cfg := cfg) (input := input)
      (counter := counter) (g := g) (n := n)
      (fun memo h_memo start h_no_cache =>
        h_body n h_counter memo h_memo start h_no_cache)
  have h_traverse :=
    lower_generated_traverse_safety_memoize_guarded
      (cfg := cfg) counter g rule.val input h_body
  refine ⟨?_, ?_, ?_⟩
  · exact lower_rule_branch_result_sound_of_traverse
      (cfg := cfg) (n := n) (rule := rule)
      (mkParser := generatedListSymbolParser cfg counter g)
      (input := input)
      (by
        intro memo h_memo start end_ subtrees h_mem
        exact
          (h_traverse memo h_memo start end_ subtrees h_mem).forest_valid)
  · exact lower_rule_branch_result_bounded_of_traverse
      (cfg := cfg) (n := n) (rule := rule)
      (mkParser := generatedListSymbolParser cfg counter g)
      (input := input)
      (by
        intro memo h_memo start end_ h_start subtrees h_mem
        exact
          (h_traverse memo h_memo start end_ subtrees h_mem).bounds h_start)
  · exact lower_rule_branch_memo_wellFormed_of_traverse
      (cfg := cfg) (n := n) (rule := rule)
      (mkParser := generatedListSymbolParser cfg counter g)
      (input := input)
      (lower_memo_wellFormed_generated_traverse_memoize_guarded
        (cfg := cfg) counter g rule.val input h_step_memo)


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
  exact List.foldlRecOn
    (motive := fun parser =>
      lower_result_sound cfg n parser input ∧
      lower_result_bounded cfg parser input ∧
      lower_memo_wellFormed cfg parser input)
    parsers ParserM.instMaxOfTraversableOfDecidableEq.max h_acc (by
      intro current h_current parser h_parser
      have hp := h_parsers parser h_parser
      exact
        ⟨lower_result_sound_of_sup_sound_after_left
            cfg n current parser input h_current.1 h_current.2.2 hp.1,
          lower_bounded_of_sup_bounded_after_left
            cfg current parser input h_current.2.1 h_current.2.2 hp.2.1,
          lower_sup_memo_wellFormed
            (cfg := cfg) (input := input)
            current parser h_current.2.2 hp.2.2⟩)

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
private theorem lower_complete_of_foldl_sup_acc
  (cfg : @CFG α ν)
  (parsers : List (ParserM (tag := tag cfg) α List (ParseTree cfg)))
  (acc : ParserM (tag := tag cfg) α List (ParseTree cfg))
  (memo : MemoData (tag cfg) List) (input : Array α)
  {start end_ : ℕ} {tree : ParseTree cfg}
  (h_mem : tree ∈ ((acc.lower start) memo input).1.getD end_ []) :
    tree ∈
      (((parsers.foldl ParserM.instMaxOfTraversableOfDecidableEq.max acc).lower start)
        memo input).1.getD end_ [] := by
  exact List.foldlRecOn parsers
    ParserM.instMaxOfTraversableOfDecidableEq.max h_mem (by
      intro current h_current parser _h_parser
      exact (mem_lower_sup_iff_after_left
        (tag := tag cfg) (β := α)
        current parser memo input start end_ tree).mpr (Or.inl h_current))

omit [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
private theorem lower_gen'_selected_rule_complete
  (cfg : @CFG α ν)
  (recur : ν → ParserM (tag := tag cfg) α List (ParseTree cfg))
  {n : ν} (rule : {rule // rule ∈ cfg.rules n})
  {memo : MemoData (tag cfg) List} {input : Array α}
  {start end_ : ℕ} {children : List (ParseTree cfg)}
  (h_complete : memo_complete cfg input memo)
  (h_branches :
    ∀ rule' : {rule // rule ∈ cfg.rules n},
      lower_memo_complete cfg
        (generatedRuleParser cfg recur n rule') input)
  (h_children :
    ∀ selectedMemo : MemoData (tag cfg) List,
      memo_complete cfg input selectedMemo →
      children ∈
        (((List.traverse id
          (rule.val.map (generatedSymbolParser cfg recur))).lower start)
          selectedMemo input).1.getD end_ []) :
    Node (cfg := cfg) n rule children ∈
      (((gen' (μ := List) cfg recur n).lower start) memo input).1.getD end_ [] := by
  let parsers :=
    (cfg.rules n).attach.map (generatedRuleParser cfg recur n)
  have h_selected :
      generatedRuleParser cfg recur n rule ∈ parsers := by
    exact List.mem_map.mpr ⟨rule, by simp, rfl⟩
  obtain ⟨rulePrefix, suffix, h_split⟩ :=
    List.mem_iff_append.mp h_selected
  let prefixParser :=
    rulePrefix.foldl ParserM.instMaxOfTraversableOfDecidableEq.max
      (⊥ : ParserM (tag := tag cfg) α List (ParseTree cfg))
  have h_prefix_memo :
      lower_memo_complete cfg prefixParser input := by
    apply lower_memo_complete_of_foldl_sup
      (cfg := cfg)
      (parsers := rulePrefix) (acc := ⊥)
      (lower_failure_memo_complete cfg input)
    intro p h_p
    have h_p_all : p ∈ parsers := by
      rw [h_split]
      simp [h_p]
    rw [List.mem_map] at h_p_all
    rcases h_p_all with ⟨rule', _h_rule_mem, rfl⟩
    exact h_branches rule'
  let selectedMemo : MemoData (tag cfg) List :=
    ↑(((prefixParser.lower start) memo input).2)
  have h_selected_complete :
      memo_complete cfg input selectedMemo := by
    exact h_prefix_memo memo h_complete start
  have h_branch :
      Node (cfg := cfg) n rule children ∈
        (((generatedRuleParser cfg recur n rule).lower start)
          selectedMemo input).1.getD end_ [] := by
    simpa [generatedRuleParser] using
      lower_rule_branch_complete
        (cfg := cfg) (n := n) (rule := rule.val) rule.property
        (mkParser := generatedSymbolParser cfg recur)
        (memo := selectedMemo) (input := input)
        (start := start) (end_ := end_)
        (subtrees := children)
        (h_children selectedMemo h_selected_complete)
  have h_choice :
      Node (cfg := cfg) n rule children ∈
        (((prefixParser ⊔ generatedRuleParser cfg recur n rule).lower start)
          memo input).1.getD end_ [] := by
    exact (mem_lower_sup_iff_after_left
      (tag := tag cfg) (β := α)
      prefixParser (generatedRuleParser cfg recur n rule)
      memo input start end_ (Node (cfg := cfg) n rule children)).mpr
        (Or.inr (by simpa [selectedMemo, prefixParser] using h_branch))
  have h_fold :=
    lower_complete_of_foldl_sup_acc
      (cfg := cfg) (parsers := suffix)
      (acc := prefixParser ⊔ generatedRuleParser cfg recur n rule)
      (memo := memo) (input := input) h_choice
  simpa [gen', parsers, h_split, List.foldl_append, prefixParser,
    generatedRuleParser, generatedSymbolParser] using h_fold

set_option maxHeartbeats 1000000 in
theorem lower_gen'_complete_of_admissible_rule
  {cfg : @CFG α ν}
  (counter : Counter ν)
  (g : ((t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg)) →
      (t : ν) → ParserM (tag := tag cfg) α List (ParseTree cfg))
  {n : ν} (rule : {rule // rule ∈ cfg.rules n})
  {children : List (ParseTree cfg)}
  {input : Array α} {memo : MemoData (tag cfg) List}
  {seen : List (SpanVisit ν)} {pre post : List α}
  (h_complete : memo_complete cfg input memo)
  (h_adm :
    AdmissibleForestWith cfg input seen counter children pre.length)
  (h_valid : (Node (cfg := cfg) n rule children).Valid)
  (h_input :
    input.toList = pre ++ forestLeaves (cfg := cfg) children ++ post)
  (h_step :
    ∀ n,
      counter[n]? ≠ some 0 →
      ∀ start,
      ∀ memo : MemoData (tag cfg) List,
        memo_complete cfg input memo →
        memo_complete cfg input
          (((memoizeStep counter g n
            (fun fuel => memoize (counter.dec n fuel) g) start)
            memo input).2.val))
  (h_recur :
    ∀ {memo : MemoData (tag cfg) List},
      memo_complete cfg input memo →
      ∀ {childN : ν} {rule' : {rule // rule ∈ cfg.rules childN}}
        {grandchildren : List (ParseTree cfg)} {pre' post' : List α},
        Node (cfg := cfg) childN rule' grandchildren ∈ children →
        AdmissibleTreeWith cfg input seen counter
          (Node (cfg := cfg) childN rule' grandchildren) pre'.length →
        (Node (cfg := cfg) childN rule' grandchildren).Valid →
        input.toList =
          pre' ++ (Node (cfg := cfg) childN rule' grandchildren).leaves ++ post' →
        Node (cfg := cfg) childN rule' grandchildren ∈
          (((memoize counter g childN).lower pre'.length) memo input).1.getD
            (pre'.length +
              (Node (cfg := cfg) childN rule' grandchildren).leaves.length) []) :
    Node (cfg := cfg) n rule children ∈
      (((gen' (μ := List) cfg (memoize counter g) n).lower pre.length)
        memo input).1.getD
        (pre.length + (forestLeaves (cfg := cfg) children).length) [] := by
  have h_forest := valid_node_iff_ForestValid.mp h_valid
  have h_fold :=
    lower_gen'_selected_rule_complete
      (cfg := cfg) (recur := memoize counter g) rule
      (memo := memo) (input := input)
      (start := pre.length)
      (end_ := pre.length + (forestLeaves (cfg := cfg) children).length)
      (children := children)
      h_complete
      (by
        intro rule'
        simpa [generatedRuleParser, generatedSymbolParser,
          generatedListSymbolParser] using
          (lower_rule_branch_memo_complete_of_traverse
            (cfg := cfg) (n := n) (rule := rule') (input := input)
            (mkParser := generatedSymbolParser cfg (memoize counter g))
            (by
              simpa [generatedSymbolParser, generatedListSymbolParser] using
                (lower_memo_complete_generated_traverse_memoize
                  (cfg := cfg) counter g rule'.val input h_step))))
      (by
        intro selectedMemo h_selected_complete
        simpa [generatedSymbolParser, generatedListSymbolParser] using
          (lower_generated_traverse_complete_of_admissible_valid_forest
            (cfg := cfg) counter g
            (rule := rule.val) (children := children)
            (input := input) (memo := selectedMemo)
            (seen := seen) (pre := pre) (post := post)
            h_selected_complete h_adm h_forest h_input
            h_step h_recur))
  simpa [leaves_node_eq_forestLeaves] using h_fold

set_option maxHeartbeats 1000000 in
theorem resultMap_complete_lower_gen'_memoized_body
  {cfg : @CFG α ν} {input : Array α}
  {counter : Counter ν} {n : ν}
  {memo : MemoData (tag cfg) List} {start : ℕ}
  (h_complete : memo_complete cfg input memo)
  (h_step :
    ∀ childN,
      (counter.dec n (input.size - start + 1))[childN]? ≠ some 0 →
      ∀ start',
      ∀ memo' : MemoData (tag cfg) List,
        memo_complete cfg input memo' →
        memo_complete cfg input
          (((memoizeStep (counter.dec n (input.size - start + 1))
            (gen' (μ := List) cfg) childN
            (fun fuel =>
              memoize
                ((counter.dec n (input.size - start + 1)).dec childN fuel)
                (gen' (μ := List) cfg))
            start') memo' input).2.val))
  (h_recur :
    ∀ {memo' : MemoData (tag cfg) List},
      memo_complete cfg input memo' →
      ∀ {seen' : List (SpanVisit ν)}
        {childN : ν} {rule' : {rule // rule ∈ cfg.rules childN}}
        {grandchildren : List (ParseTree cfg)} {pre' post' : List α},
        AdmissibleTreeWith cfg input seen'
          (counter.dec n (input.size - start + 1))
          (Node (cfg := cfg) childN rule' grandchildren) pre'.length →
        (Node (cfg := cfg) childN rule' grandchildren).Valid →
        input.toList =
          pre' ++ (Node (cfg := cfg) childN rule' grandchildren).leaves ++ post' →
        Node (cfg := cfg) childN rule' grandchildren ∈
          (((memoize (counter.dec n (input.size - start + 1))
              (gen' (μ := List) cfg) childN).lower pre'.length)
            memo' input).1.getD
            (pre'.length +
              (Node (cfg := cfg) childN rule' grandchildren).leaves.length) []) :
    resultMap_complete cfg input n (Counter.toKey counter) start
      ((((gen' (μ := List) cfg
          (memoize (counter.dec n (input.size - start + 1))
            (gen' (μ := List) cfg)) n).lower start) memo input).1) := by
  intro counter' pre post seen tree h_key h_start h_root h_adm h_valid h_input
  subst start
  cases tree with
  | Leaf a =>
      simp at h_root
  | Node n' rule children =>
      have h_n : n' = n := by
        simpa using h_root
      cases h_n
      obtain ⟨_h_no_cycle, _h_budget, h_children_adm⟩ :=
        admissible_node_inv (cfg := cfg) h_adm
      have h_counter_lookup :
          ∀ t : ν, counter'[t]? = counter[t]? := by
        intro t
        exact counter_getElem?_eq_of_toKey_eq
          (left := counter') (right := counter) h_key t
      have h_children_adm_key :
          AdmissibleForestWith cfg input
            (nodeSpanVisit n pre.length
              (Node (cfg := cfg) n rule children) :: seen)
            (counter.dec n (input.size - pre.length + 1))
            children pre.length := by
        refine admissibleForestWith_congr_counter_getElem?
          (cfg := cfg) (input := input)
          (left := counter'.dec n (input.size - pre.length + 1))
          (right := counter.dec n (input.size - pre.length + 1))
          ?_ h_children_adm
        intro t
        exact counter_dec_getElem?_eq_of_getElem?_eq
          (left := counter') (right := counter)
          h_counter_lookup n t (input.size - pre.length + 1)
      have h_children_adm_body :
          AdmissibleForestWith cfg input
            (nodeSpanVisit n pre.length
              (Node (cfg := cfg) n rule children) :: seen)
            (counter.dec n (input.size - pre.length + 1))
            children pre.length := by
        exact h_children_adm_key
      have h_forest_input :
          input.toList = pre ++ forestLeaves (cfg := cfg) children ++ post := by
        simpa [leaves_node_eq_forestLeaves] using h_input
      have h_node_valid :
          (Node (cfg := cfg) n rule children).Valid := by
        simpa using h_valid
      simpa [leaves_node_eq_forestLeaves] using
        (lower_gen'_complete_of_admissible_rule
          (cfg := cfg)
          (counter := counter.dec n (input.size - pre.length + 1))
          (g := gen' (μ := List) cfg)
          (n := n) (rule := rule)
          (children := children)
          (input := input) (memo := memo)
          (seen :=
            nodeSpanVisit n pre.length
              (Node (cfg := cfg) n rule children) :: seen)
          (pre := pre) (post := post)
          h_complete h_children_adm_body h_node_valid h_forest_input
          h_step
          (by
            intro memo' h_memo childN rule' grandchildren pre' post'
              h_child_mem h_child_adm h_child_valid h_child_input
            exact h_recur h_memo h_child_adm h_child_valid h_child_input))

set_option maxHeartbeats 2000000 in
theorem memoized_gen_complete_invariant
  (cfg : @CFG α ν) (input : Array α) :
    (∀ n,
      lower_memo_complete cfg
        (memoize (Counter.empty : Counter ν) (gen' (μ := List) cfg) n)
        input) ∧
    (∀ {n : ν} {memo : MemoData (tag cfg) List}
      {pre post : List α} {seen : List (SpanVisit ν)}
      {tree : ParseTree cfg},
      memo_complete cfg input memo →
      tree.root = Symbol.nonterm n →
      AdmissibleTreeWith cfg input seen (Counter.empty : Counter ν) tree
        pre.length →
      tree.Valid →
      input.toList = pre ++ tree.leaves ++ post →
      tree ∈
        (((memoize (Counter.empty : Counter ν) (gen' (μ := List) cfg) n).lower
          pre.length) memo input).1.getD
          (pre.length + tree.leaves.length) []) := by
  let p (counter : Counter ν) (parser : GeneratedFamily cfg) :=
    GeneratedCompleteCounterInvariant cfg input counter parser
  have h_all : p (Counter.empty : Counter ν)
      (memoize (g := gen' (μ := List) cfg)) := by
    refine memoize_counter_induction (g := gen' (μ := List) cfg) p ?_
    intro counter h_ind
    have h_body_current :
        GeneratedBodyCompleteness cfg input counter (gen' (μ := List) cfg) := by
      intro current h_counter memo h_memo start h_no_cache
      let childCounter : Counter ν :=
        counter.dec current (input.size - start + 1)
      have h_child : p childCounter
          (memoize (g := gen' (μ := List) cfg) childCounter) := by
        simpa [childCounter] using
          h_ind current (input.size - start + 1) h_counter
      have h_step_guard :
          ∀ childN,
            childCounter[childN]? ≠ some 0 →
            ∀ start',
            ∀ memo' : MemoData (tag cfg) List,
              memo_complete cfg input memo' →
              memo_complete cfg input
                (((memoizeStep childCounter (gen' (μ := List) cfg) childN
                  (fun fuel => memoize (childCounter.dec childN fuel)
                    (gen' (μ := List) cfg))
                  start') memo' input).2.val) := by
        intro childN h_child_counter start' memo' h_memo'
        exact memo_complete_memoizeStep
          (cfg := cfg) (input := input)
          (counter := childCounter)
          (g := gen' (μ := List) cfg)
          (next := fun fuel =>
            memoize (childCounter.dec childN fuel) (gen' (μ := List) cfg))
          (n := childN) (memo := memo') (start := start')
          h_memo'
          (fun h_no_cache' =>
            (h_child.2.1 childN h_child_counter memo' h_memo' start'
              h_no_cache'))
      have h_body_memo :
          lower_memo_complete cfg
            (gen' (μ := List) cfg
              (memoize childCounter (gen' (μ := List) cfg)) current)
            input := by
        exact lower_gen'_memo_complete_of_rules
          (cfg := cfg) (input := input)
          (recur := memoize childCounter (gen' (μ := List) cfg))
          current
          (by
            intro rule
            exact lower_rule_branch_memo_complete_of_traverse
              (cfg := cfg) (n := current) (rule := rule) (input := input)
              (by
                simpa [generatedSymbolParser, generatedListSymbolParser] using
                  (lower_memo_complete_generated_traverse_memoize
                    (cfg := cfg) childCounter (gen' (μ := List) cfg)
                    rule.val input h_step_guard)))
      have h_body_result :
          resultMap_complete cfg input current (Counter.toKey counter) start
            ((((gen' (μ := List) cfg
                (memoize childCounter (gen' (μ := List) cfg)) current).lower
              start) memo input).1) := by
        intro counter' pre post seen tree h_key h_start h_root h_adm h_valid
          h_input
        have h_raw :
            resultMap_complete cfg input current (Counter.toKey counter) start
              ((((gen' (μ := List) cfg
                  (memoize (counter.dec current (input.size - start + 1))
                    (gen' (μ := List) cfg)) current).lower start)
                memo input).1) :=
          resultMap_complete_lower_gen'_memoized_body
            (cfg := cfg) (input := input)
            (counter := counter) (n := current)
            (memo := memo) (start := start)
            h_memo
            (by
              intro childN h_child_counter start' memo' h_memo'
              have h_child_counter' :
                  childCounter[childN]? ≠ some 0 := by
                simpa [childCounter] using h_child_counter
              change memo_complete cfg input
                (((memoizeStep childCounter (gen' (μ := List) cfg) childN
                  (fun fuel => memoize (childCounter.dec childN fuel)
                    (gen' (μ := List) cfg))
                  start') memo' input).2.val)
              exact h_step_guard childN h_child_counter' start' memo' h_memo')
            (by
              intro memo' h_memo' seen' childN rule grandchildren pre post
                h_adm h_valid h_input
              exact h_child.2.2
                (n := childN) (memo := memo')
                (pre := pre) (post := post) (seen := seen')
                (tree := Node (cfg := cfg) childN rule grandchildren)
                h_memo' rfl h_adm h_valid h_input)
        simpa [childCounter] using
          h_raw h_key h_start h_root h_adm h_valid h_input
      constructor
      · intro n' counter' pre post seen tree resultMap h_cache h_root h_adm
          h_valid h_input
        have h_body_memo' :
            memo_complete cfg input
              ((((gen' (μ := List) cfg
                  (memoize childCounter (gen' (μ := List) cfg)) current).lower
                start) memo input).2.val) :=
          h_body_memo memo h_memo start
        simpa [childCounter] using
          h_body_memo' h_cache h_root h_adm h_valid h_input
      · intro counter' pre post seen tree h_key h_start h_root h_adm h_valid
          h_input
        simpa [childCounter] using
          h_body_result h_key h_start h_root h_adm h_valid h_input
    constructor
    · intro current
      by_cases h_counter : counter[current]? = some 0
      · simpa [memoize, h_counter] using
          lower_failure_memo_complete cfg input
      · exact lower_memo_complete_memoize
          (cfg := cfg) (input := input)
          (counter := counter) (g := gen' (μ := List) cfg)
          (n := current)
          (by
            intro memo h_memo start h_no_cache
            exact h_body_current current h_counter memo h_memo start
              h_no_cache)
    constructor
    · exact h_body_current
    · intro current memo pre post seen tree h_memo h_root h_adm h_valid h_input
      cases tree with
      | Leaf a =>
          simp at h_root
      | Node n' rule children =>
          have h_n : n' = current := by
            simpa using h_root
          cases h_n
          obtain ⟨_h_no_cycle, h_budget, _h_children_adm⟩ :=
            admissible_node_inv (cfg := cfg) h_adm
          exact mem_lower_memoize_of_body_or_cache_complete
            (cfg := cfg) (input := input)
            counter (gen' (μ := List) cfg)
            (n := current) (memo := memo)
            (pre := pre) (post := post) (seen := seen)
            (tree := Node (cfg := cfg) current rule children)
            h_budget h_memo rfl h_adm h_valid h_input
            (by
              intro h_no_cache
              exact (h_body_current current h_budget memo h_memo pre.length
                h_no_cache).2 rfl rfl rfl h_adm h_valid h_input)
  constructor
  · exact h_all.1
  · exact h_all.2.2

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
  have h_mem :=
    (memoized_gen_complete_invariant cfg input).2
      (n := n)
      (memo := (startState : MemoData (tag cfg) List))
      (pre := []) (post := []) (seen := [])
      (tree := tree)
      (memo_complete_empty cfg input)
      h_root h_adm h_valid h_input
  unfold gen
  rw [runParser_fst_eq_lower]
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
  let P : ParseTree cfg → Prop := fun tree =>
    tree.Valid ∧ tree.root = Symbol.nonterm n ∧ tree.leaves = input.toList
  have h_exists : ∃ tree, P tree :=
    ParseTree.exists_Valid_tree_of_derives
      (cfg := cfg) (n := n) (w := input.toList) h_derives
  obtain ⟨tree, h_tree, h_min⟩ :=
    exists_minimalFor_of_wellFoundedLT P sizeOf h_exists
  refine ⟨tree, h_tree.1, h_tree.2.1, h_tree.2.2, ?_⟩
  intro tree' h_valid h_root h_leaves
  exact (le_total (sizeOf tree) (sizeOf tree')).elim id
    (h_min ⟨h_valid, h_root, h_leaves⟩)


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
  let p (counter : Counter ν) (parser : GeneratedFamily cfg) :=
    GeneratedSoundCounterInvariant cfg counter parser
  have h_all : p Counter.empty (memoize (g := gen' (μ := List) cfg)) := by
    refine memoize_counter_induction (g := gen' (μ := List) cfg) p ?_
    intro counter h_ind input
    have h_body_current :
        GeneratedBodySafety cfg input counter (gen' (μ := List) cfg) := by
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
