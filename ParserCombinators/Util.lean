-- Some helper lemmas not proven in the Stdlib

import Mathlib.Data.List.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic

universe u
variable {α : Type u} [DecidableEq α]

@[simp]
lemma getRest_append_right (x y z a : List α) (h : a <+: x) (h' : List.getRest x a = some y)
    : List.getRest (x ++ z) a = some (y ++ z) := by
  induction x generalizing a
  · apply List.prefix_nil.mp at h
    subst h
    simp_all [List.getRest]
  · unfold List.getRest
    unfold List.getRest at h'
    split at h'
    · simp_all
    · contradiction
    · simp_all

@[simp]
lemma getRest_elim_prefix (x y a : List α) : List.getRest (x ++ y) (x ++ a) = List.getRest y a := by
  induction x
  · simp
  · rename_i head tail ih
    rw [List.getRest.eq_def]
    simp [ih]

@[simp]
lemma getRest_cons (x : α) (y a : List α) : List.getRest (x :: y) (x :: a) = List.getRest y a := by
    rw [List.getRest.eq_def]
    simp

@[simp]
lemma getRest_append_left (x y z a : List α) (h : a <+: x) (h' : List.getRest x a = some y)
    : List.getRest (z ++ x) (z ++ a) = some y := by
  induction z generalizing y
  · simp only [List.nil_append]
    exact h'
  · rename_i head tail ih
    unfold List.getRest
    unfold List.getRest at h'
    split at h'
    · simp_all only [List.nil_prefix, List.append_nil, Option.some.injEq, List.cons_append, ↓reduceIte, List.getRest]
    · contradiction
    · simp_all only [List.cons_append, Option.ite_none_right_eq_some]
      rename_i l y' l₁
      have h'' := ih y
      simp only [List.getRest, ↓reduceIte, h'.right, forall_const] at h''
      simp only [h'', and_self]

lemma zip_eq_nil_of_eq_length {α β} {xs : List α} {ys : List β} (h_len : xs.length = ys.length)
  (h_zip : xs.zip ys = []) : xs = [] ∧ ys = [] := by
  apply List.zip_eq_nil_iff.mp at h_zip
  have hx : xs = [] := by
    cases h_zip with
    | inl h => assumption
    | inr h =>
      subst h
      exact List.eq_nil_iff_length_eq_zero.mpr h_len
  rw [hx] at h_len
  constructor
  · assumption
  · exact List.eq_nil_iff_length_eq_zero.mpr (id (Eq.symm h_len))

-- lemmas for handling List.findSome? instances associated with hash maps.
private lemma h_findSome?_eq_none {l} (h: k ∉ l) {f : α → β}
  : List.findSome? ((fun x ↦ if x.fst = k then some x.snd else none) ∘ fun k ↦ (k, f k)) l = none
  := by
    apply List.findSome?_eq_none_iff.mpr
    intro x h_mem
    simp
    intro h_x_k
    subst h_x_k
    contradiction
private lemma h_findSome?_eq_some {l} (h: k ∈ l) {f : α → β}
  : List.findSome? ((fun x ↦ if x.fst = k then some x.snd else none) ∘ fun k ↦ (k, f k)) l = some (f k)
  := by
    induction l with
    | nil => contradiction
    | cons head tail ih =>
      simp [List.findSome?_cons]
      apply List.mem_cons.mp at h
      by_cases h_head : head = k
      · simp [h, h_head]
      · simp_all [h_head]
        cases h with
        | inl h_1 =>
          subst h_1
          simp_all only [not_true_eq_false]
        | inr h_2 => simp_all only [forall_const]


namespace Std.HashMap
variable {β : Type v} [BEq α] [LawfulBEq α] [Hashable α] [SemilatticeSup β] [OrderBot β]

def unionWith (m₁ m₂ : Std.HashMap α β) : Std.HashMap α β :=
    Std.HashMap.ofList $ List.map (fun k => (k, m₁.getD k ⊥ ⊔ m₂.getD k ⊥)) (m₁.keys ++ m₂.keys)

lemma unionWith_equiv_idem (m : Std.HashMap α β) : m.unionWith m ~m m := by {
  unfold unionWith
  refine Std.HashMap.Equiv.of_forall_getElem?_eq ?_
  intro k
  simp [Std.HashMap.ofList_eq_insertMany_empty]
  simp [Std.HashMap.getElem?_insertMany_list]
  by_cases h_mem : k ∈ m
  · simp [h_mem]
    simp [<- List.map_reverse, List.findSome?_map]
    rw [h_findSome?_eq_some]
    · simp
      symm
      apply HashMap.getElem_eq_getD
    · simp [h_mem]
  · rw [Std.HashMap.getElem?_eq_none h_mem]
    simp [List.findSome?_eq_none_iff]
    intro a h_a h_a_k
    rw [h_a_k] at h_a
    contradiction
}

lemma unionWith_equiv_comm (m₁ m₂ : Std.HashMap α β) : m₁.unionWith m₂ ~m m₂.unionWith m₁ := by {
  unfold unionWith
  refine Std.HashMap.Equiv.of_forall_getElem?_eq ?_
  intro k
  simp [Std.HashMap.ofList_eq_insertMany_empty]
  simp [Std.HashMap.getElem?_insertMany_list]
  simp [<- List.map_reverse, List.findSome?_map]

  by_cases h_mem₁ : k ∈ m₁.keys.reverse
  · by_cases h_mem₂ : k ∈ m₂.keys.reverse
    · repeat rw [h_findSome?_eq_some h_mem₁, h_findSome?_eq_some h_mem₂]
      simp [sup_comm]
    · repeat rw [h_findSome?_eq_none h_mem₂]
      simp [sup_comm]
  · repeat rw [h_findSome?_eq_none h_mem₁]
    simp [sup_comm]
}

omit [DecidableEq α] in
lemma mem_of_unionWith_mem {m₁ m₂ : Std.HashMap α β} : k ∈ m₁.unionWith m₂ ↔ k ∈ m₁ ∨ k ∈ m₂ := by
  unfold unionWith
  simp [Std.HashMap.mem_ofList]

lemma unionWith_getElem_of_not_contains (m₁ m₂ : Std.HashMap α β) (h : k ∉ m₁) : (m₁.unionWith m₂)[k]? = m₂[k]? := by
  unfold unionWith
  simp [Std.HashMap.ofList_eq_insertMany_empty]
  simp [Std.HashMap.getElem?_insertMany_list]
  simp [<- List.map_reverse, List.findSome?_map]
  rw [h_findSome?_eq_none (l := m₁.keys.reverse)]
  · simp
    by_cases h₂ : k ∈ m₂
    · rw [h_findSome?_eq_some]
      · simp [getD_eq_fallback h]
        simp [h₂, <- getElem_eq_getD]
      · simp [h₂]
    · rw [h_findSome?_eq_none]
      · simp [h₂]
      · simp [h₂]
  · simp [h]

lemma unionWith_getD_of_not_contains (m₁ m₂ : Std.HashMap α β) (h : k ∉ m₁) {fallback}
    : (m₁.unionWith m₂).getD k fallback = m₂.getD k fallback := by
  repeat rw [getD_eq_getD_getElem?]
  simp [unionWith_getElem_of_not_contains m₁ m₂ h]

lemma unionWith_getD_both {m₁ m₂ : Std.HashMap α β} (h₁ : k ∈ m₁) (h₂ : k ∈ m₂)
    : (m₁.unionWith m₂).getD k ⊥ = m₁[k] ⊔ m₂[k] := by
  repeat rw [getD_eq_getD_getElem?]
  unfold unionWith
  simp [Std.HashMap.ofList_eq_insertMany_empty]
  simp [Std.HashMap.getElem?_insertMany_list]
  simp [<- List.map_reverse, List.findSome?_map]
  rw [h_findSome?_eq_some (l := m₂.keys.reverse)]
  · simp [<- getElem_eq_getD, h₁, h₂]
  · simp_all

lemma unionWith_equiv_assoc (m₁ m₂ m₃ : Std.HashMap α β)
    : (m₁.unionWith m₂).unionWith m₃ ~m m₁.unionWith (m₂.unionWith m₃) := by {
  rw [unionWith]
  nth_rw 3 [unionWith]
  refine Std.HashMap.Equiv.of_forall_getElem?_eq ?_
  intro k
  simp [Std.HashMap.ofList_eq_insertMany_empty]
  simp [Std.HashMap.getElem?_insertMany_list]
  simp [<- List.map_reverse, List.findSome?_map]

  by_cases h_mem₁ : k ∈ m₁.keys.reverse
  · by_cases h_mem₂ : k ∈ m₂.keys.reverse
    · by_cases h_mem₃ : k ∈ m₃.keys.reverse
      · repeat rw [h_findSome?_eq_some h_mem₃]
        simp
        rw [h_findSome?_eq_some]
        · simp_all [unionWith_getD_both, <- getElem_eq_getD, sup_assoc]
        · simp_all [mem_of_unionWith_mem]
      · rw [h_findSome?_eq_none h_mem₃]
        repeat rw [h_findSome?_eq_some]
        · simp_all
          rw [Equiv.getD_eq $ unionWith_equiv_comm m₂ m₃]
          simp [unionWith_getD_of_not_contains, getD_eq_fallback, h_mem₃]
          simp [unionWith_getD_both, <- getElem_eq_getD, h_mem₁, h_mem₂]
        · simp_all
        · simp_all [mem_of_unionWith_mem]
        · simp_all [mem_of_unionWith_mem]
    · by_cases h_mem₃ : k ∈ m₃.keys.reverse
      · rw [h_findSome?_eq_some h_mem₃]
        simp_all
        rw [h_findSome?_eq_some]
        · simp
          rw [Equiv.getD_eq $ unionWith_equiv_comm m₁ m₂]
          simp_all [unionWith_getD_of_not_contains]
        · simp_all [mem_of_unionWith_mem]
      · have h_mem₂₃ : k ∉ (m₂.unionWith m₃).keys.reverse := by
          simp at h_mem₂
          simp at h_mem₃
          simp [List.mem_reverse, mem_of_unionWith_mem, h_mem₂, h_mem₃]
        rw [h_findSome?_eq_none h_mem₃, h_findSome?_eq_none h_mem₂₃]
        simp_all
        repeat rw [h_findSome?_eq_some]
        · rw [Equiv.getD_eq $ unionWith_equiv_comm m₁ m₂]
          simp_all [unionWith_getD_of_not_contains]
        · simp_all
        · simp_all [mem_of_unionWith_mem]
  · repeat rw [h_findSome?_eq_none h_mem₁]
    simp_all
    by_cases h_mem₂ : k ∈ m₂.keys.reverse
    · by_cases h_mem₃ : k ∈ m₃.keys.reverse
      · rw [h_findSome?_eq_some h_mem₃]
        simp_all
        rw [h_findSome?_eq_some]
        · simp [getD_eq_fallback, h_mem₁]
          simp [unionWith_getD_of_not_contains m₁ m₂ h_mem₁]
          simp [<- getElem_eq_getD, h_mem₂, h_mem₃]
          simp [unionWith_getD_both, h_mem₂, h_mem₃]
        · simp_all [mem_of_unionWith_mem]
      · rw [h_findSome?_eq_none h_mem₃]
        simp_all
        repeat rw [h_findSome?_eq_some]
        · rw [unionWith_getD_of_not_contains m₁ m₂ h_mem₁]
          rw [Equiv.getD_eq (unionWith_equiv_comm m₂ m₃)]
          rw [unionWith_getD_of_not_contains m₃ m₂ h_mem₃]
          simp [getD_eq_fallback, h_mem₁, h_mem₃]
        · simp_all [mem_of_unionWith_mem]
        · simp_all [mem_of_unionWith_mem]
    · have h_mem₁₂ : k ∉ (m₁.unionWith m₂).keys.reverse := by
        simp at h_mem₂
        simp [List.mem_reverse, mem_of_unionWith_mem, h_mem₁, h_mem₂]
      repeat rw [h_findSome?_eq_none h_mem₁₂]
      simp
      by_cases h_mem₃ : k ∈ m₃.keys.reverse
      · repeat rw [h_findSome?_eq_some]
        · simp_all [getD_eq_fallback]
          simp [unionWith_getD_of_not_contains m₂ m₃ h_mem₂]
        · simp_all [mem_of_unionWith_mem]
        · simp_all
      · have h_mem₂₃ : k ∉ (m₂.unionWith m₃).keys.reverse := by
          simp at h_mem₂
          simp at h_mem₃
          simp [List.mem_reverse, mem_of_unionWith_mem, h_mem₂, h_mem₃]
        repeat rw [h_findSome?_eq_none h_mem₂₃]
        repeat rw [h_findSome?_eq_none h_mem₃]


}
end Std.HashMap

namespace Std.DHashMap
def unionWith {K v} [BEq K] [LawfulBEq K] [Hashable K] (m₁ m₂ : Std.DHashMap K v) (f : (α : K) → v α → v α → v α) : Std.DHashMap K v :=
  m₂.fold (fun m k v2 =>
    match m.get? k with
    -- Collision case, meshes the two values found into one new value (based on the given function `f`)
    | some v1 => m.insert k (f k v1 v2)
    -- New key case, juar adds the value we found
    | none => m.insert k v2) m₁
end Std.DHashMap
