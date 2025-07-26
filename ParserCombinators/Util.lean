-- Some helper lemmas not proven in the Stdlib

import Mathlib.Data.List.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic

universe u v
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
lemma h_findSome?_eq_none {l} (h: k ∉ l) {f : α → β}
  : List.findSome? ((fun x ↦ if x.fst = k then some x.snd else none) ∘ fun k ↦ (k, f k)) l = none
  := by
    apply List.findSome?_eq_none_iff.mpr
    intro x h_mem
    simp
    intro h_x_k
    subst h_x_k
    contradiction

lemma h_findSome?_eq_none' {β : α → Type v} {l} (h: k ∉ l) {f : (a : α) → β a}
  : List.findSome? ((fun a ↦ if h : a = k then some (congrArg β h ▸ f a) else none)) l = none
  := by
    apply List.findSome?_eq_none_iff.mpr
    intro x h_mem
    simp
    intro h_x_k
    subst h_x_k
    contradiction

lemma h_findSome?_eq_some {l} (h: k ∈ l) {f : α → β}
  : List.findSome? ((fun x ↦ if x.fst = k then some x.snd else none) ∘ fun k ↦ (k, f k)) l = some (f k)
  := by
    induction l with
    | nil => contradiction
    | cons head tail ih =>
      simp [List.findSome?_cons]
      apply List.mem_cons.mp at h
      by_cases h_head : head = k
      · simp [h_head]
      · simp_all
        cases h with
        | inl h_1 =>
          subst h_1
          simp_all only [not_true_eq_false]
        | inr h_2 => simp_all only [forall_const]

lemma h_findSome?_eq_some' {β : α → Type v} {l} (h: k ∈ l) {f : (a : α) → β a}
  : List.findSome? ((fun a ↦ if h : a = k then some (congrArg β h ▸ f a) else none)) l = some (f k)
  := by
    induction l with
    | nil => contradiction
    | cons head tail ih =>
      simp [List.findSome?_cons]
      apply List.mem_cons.mp at h
      by_cases h_head : head = k
      · subst h_head
        simp
      · simp_all
        cases h with
        | inl h_1 =>
          subst h_1
          simp_all only [not_true_eq_false]
        | inr h_2 => simp_all only [forall_const]

namespace Std.HashMap
variable {β : Type v} [BEq α] [LawfulBEq α] [Hashable α]

section unionSup
variable [Max β] [Bot β]

-- Take the union of `m₁` and `m₂`, merge conflicting values with `⊔`.
-- The definition doesn't assume a semilattice structure, but the theorems do.
def unionSup (m₁ m₂ : Std.HashMap α β) : Std.HashMap α β :=
    Std.HashMap.ofList $ List.map (fun k => (k, m₁.getD k ⊥ ⊔ m₂.getD k ⊥)) (m₁.keys ++ m₂.keys)

end unionSup

variable [SemilatticeSup β] [OrderBot β]

lemma unionSup_equiv_idem (m : Std.HashMap α β) : m.unionSup m ~m m := by {
  unfold unionSup
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

lemma unionSup_equiv_comm (m₁ m₂ : Std.HashMap α β) : m₁.unionSup m₂ ~m m₂.unionSup m₁ := by {
  unfold unionSup
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
lemma mem_of_unionSup_mem {m₁ m₂ : Std.HashMap α β} : k ∈ m₁.unionSup m₂ ↔ k ∈ m₁ ∨ k ∈ m₂ := by
  unfold unionSup
  simp [Std.HashMap.mem_ofList]

lemma unionSup_getElem_of_not_contains (m₁ m₂ : Std.HashMap α β) (h : k ∉ m₁) : (m₁.unionSup m₂)[k]? = m₂[k]? := by
  unfold unionSup
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

lemma unionSup_getElem_both {m₁ m₂ : Std.HashMap α β} (h₁ : k ∈ m₁) (h₂ : k ∈ m₂)
    : (m₁.unionSup m₂)[k]? = m₁[k] ⊔ m₂[k] := by
  unfold unionSup
  simp [Std.HashMap.ofList_eq_insertMany_empty]
  simp [Std.HashMap.getElem?_insertMany_list]
  simp [<- List.map_reverse, List.findSome?_map]
  rw [h_findSome?_eq_some (l := m₂.keys.reverse)]
  · simp [<- getElem_eq_getD, h₁, h₂]
  · simp_all

lemma unionSup_getD_of_not_contains (m₁ m₂ : Std.HashMap α β) (h : k ∉ m₁) {fallback}
    : (m₁.unionSup m₂).getD k fallback = m₂.getD k fallback := by
  repeat rw [getD_eq_getD_getElem?]
  simp [unionSup_getElem_of_not_contains m₁ m₂ h]

lemma unionSup_getD_both {m₁ m₂ : Std.HashMap α β} (h₁ : k ∈ m₁) (h₂ : k ∈ m₂)
    : (m₁.unionSup m₂).getD k ⊥ = m₁[k] ⊔ m₂[k] := by
  repeat rw [getD_eq_getD_getElem?]
  unfold unionSup
  simp [Std.HashMap.ofList_eq_insertMany_empty]
  simp [Std.HashMap.getElem?_insertMany_list]
  simp [<- List.map_reverse, List.findSome?_map]
  rw [h_findSome?_eq_some (l := m₂.keys.reverse)]
  · simp [<- getElem_eq_getD, h₁, h₂]
  · simp_all

lemma unionSup_get?_of_Equiv_left {m₁ m₁' m₂ : Std.HashMap α β} (h : m₁ ~m m₁') (k : α)
    : (m₁.unionSup m₂).get? k = (m₁'.unionSup m₂).get? k := by
  repeat rw [get?_eq_getElem?]
  by_cases h_mem₁ : k ∈ m₁
  · have h_mem₁' := (Equiv.mem_iff h).mp h_mem₁
    by_cases h_mem₂ : k ∈ m₂
    · simp [unionSup_getElem_both, h_mem₁, h_mem₁', h_mem₂]
      rw [Equiv.getElem_eq h_mem₁ h]
    · rw [Equiv.getElem?_eq (unionSup_equiv_comm m₁ m₂)]
      rw [Equiv.getElem?_eq (unionSup_equiv_comm m₁' m₂)]
      simp [unionSup_getElem_of_not_contains, h_mem₂]
      rw [Equiv.getElem?_eq h]
  · have h_mem₁' : k ∉ m₁' := (not_congr (Equiv.mem_iff h)).mp h_mem₁
    simp [unionSup_getElem_of_not_contains, h_mem₁, h_mem₁']

lemma unionSup_get?_of_Equiv_right {m₁ m₂ m₂' : Std.HashMap α β} (h : m₂ ~m m₂') (k : α)
    : (m₁.unionSup m₂).get? k = (m₁.unionSup m₂').get? k := by
  repeat rw [get?_eq_getElem?]
  rw [Equiv.getElem?_eq (unionSup_equiv_comm m₁ m₂)]
  rw [Equiv.getElem?_eq (unionSup_equiv_comm m₁ m₂')]
  repeat rw [<- get?_eq_getElem?]
  exact unionSup_get?_of_Equiv_left h k

lemma unionSup_Equiv_left {m₁ m₁' m₂ : Std.HashMap α β} (h : m₁ ~m m₁')
    : (m₁.unionSup m₂) ~m (m₁'.unionSup m₂) := by
  apply Equiv.of_forall_getElem?_eq
  intro k
  repeat rw [<- get?_eq_getElem?]
  apply unionSup_get?_of_Equiv_left h k

lemma unionSup_Equiv_right {m₁ m₂ m₂' : Std.HashMap α β} (h : m₂ ~m m₂')
    : (m₁.unionSup m₂) ~m (m₁.unionSup m₂') := by
  apply Equiv.of_forall_getElem?_eq
  intro k
  repeat rw [<- get?_eq_getElem?]
  apply unionSup_get?_of_Equiv_right h k

lemma unionSup_Equiv {m₁ m₁' m₂ m₂' : Std.HashMap α β} (h₁ : m₁ ~m m₁') (h₂ : m₂ ~m m₂')
    : (m₁.unionSup m₂) ~m (m₁'.unionSup m₂') :=
  Equiv.trans (unionSup_Equiv_left h₁) (unionSup_Equiv_right h₂)


lemma unionSup_equiv_assoc (m₁ m₂ m₃ : Std.HashMap α β)
    : (m₁.unionSup m₂).unionSup m₃ ~m m₁.unionSup (m₂.unionSup m₃) := by {
  rw [unionSup]
  nth_rw 3 [unionSup]
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
        · simp_all [unionSup_getD_both, <- getElem_eq_getD, sup_assoc]
        · simp_all [mem_of_unionSup_mem]
      · rw [h_findSome?_eq_none h_mem₃]
        repeat rw [h_findSome?_eq_some]
        · simp_all
          rw [Equiv.getD_eq $ unionSup_equiv_comm m₂ m₃]
          simp [unionSup_getD_of_not_contains, getD_eq_fallback, h_mem₃]
          simp [unionSup_getD_both, <- getElem_eq_getD, h_mem₁, h_mem₂]
        · simp_all
        · simp_all [mem_of_unionSup_mem]
        · simp_all [mem_of_unionSup_mem]
    · by_cases h_mem₃ : k ∈ m₃.keys.reverse
      · rw [h_findSome?_eq_some h_mem₃]
        simp_all
        rw [h_findSome?_eq_some]
        · simp
          rw [Equiv.getD_eq $ unionSup_equiv_comm m₁ m₂]
          simp_all [unionSup_getD_of_not_contains]
        · simp_all [mem_of_unionSup_mem]
      · have h_mem₂₃ : k ∉ (m₂.unionSup m₃).keys.reverse := by
          simp at h_mem₂
          simp at h_mem₃
          simp [List.mem_reverse, mem_of_unionSup_mem, h_mem₂, h_mem₃]
        rw [h_findSome?_eq_none h_mem₃, h_findSome?_eq_none h_mem₂₃]
        simp_all
        repeat rw [h_findSome?_eq_some]
        · rw [Equiv.getD_eq $ unionSup_equiv_comm m₁ m₂]
          simp_all [unionSup_getD_of_not_contains]
        · simp_all
        · simp_all [mem_of_unionSup_mem]
  · repeat rw [h_findSome?_eq_none h_mem₁]
    simp_all
    by_cases h_mem₂ : k ∈ m₂.keys.reverse
    · by_cases h_mem₃ : k ∈ m₃.keys.reverse
      · rw [h_findSome?_eq_some h_mem₃]
        simp_all
        rw [h_findSome?_eq_some]
        · simp [getD_eq_fallback, h_mem₁]
          simp [unionSup_getD_of_not_contains m₁ m₂ h_mem₁]
          simp [<- getElem_eq_getD, h_mem₂, h_mem₃]
          simp [unionSup_getD_both, h_mem₂, h_mem₃]
        · simp_all [mem_of_unionSup_mem]
      · rw [h_findSome?_eq_none h_mem₃]
        simp_all
        repeat rw [h_findSome?_eq_some]
        · rw [unionSup_getD_of_not_contains m₁ m₂ h_mem₁]
          rw [Equiv.getD_eq (unionSup_equiv_comm m₂ m₃)]
          rw [unionSup_getD_of_not_contains m₃ m₂ h_mem₃]
          simp [getD_eq_fallback, h_mem₁, h_mem₃]
        · simp_all [mem_of_unionSup_mem]
        · simp_all [mem_of_unionSup_mem]
    · have h_mem₁₂ : k ∉ (m₁.unionSup m₂).keys.reverse := by
        simp at h_mem₂
        simp [List.mem_reverse, mem_of_unionSup_mem, h_mem₁, h_mem₂]
      repeat rw [h_findSome?_eq_none h_mem₁₂]
      simp
      by_cases h_mem₃ : k ∈ m₃.keys.reverse
      · repeat rw [h_findSome?_eq_some]
        · simp_all [getD_eq_fallback]
          simp [unionSup_getD_of_not_contains m₂ m₃ h_mem₂]
        · simp_all [mem_of_unionSup_mem]
        · simp_all
      · have h_mem₂₃ : k ∉ (m₂.unionSup m₃).keys.reverse := by
          simp at h_mem₂
          simp at h_mem₃
          simp [List.mem_reverse, mem_of_unionSup_mem, h_mem₂, h_mem₃]
        repeat rw [h_findSome?_eq_none h_mem₂₃]
        repeat rw [h_findSome?_eq_none h_mem₃]
}

lemma empty_unionSup_equiv_self (m : Std.HashMap α β) : emptyWithCapacity.unionSup m ~m m := by
  refine Std.HashMap.Equiv.of_forall_getElem?_eq ?_
  intro k
  rw [unionSup_getElem_of_not_contains]
  · simp

lemma unionSup_empty_equiv_self (m : Std.HashMap α β) : m.unionSup emptyWithCapacity ~m m :=
  Equiv.trans (unionSup_equiv_comm m emptyWithCapacity) (empty_unionSup_equiv_self m)

-- The Semilattice induced by unionSup
section Semilattice
def isSetoid : Setoid (HashMap α β) where
  r := Std.HashMap.Equiv
  iseqv := {
    refl := .refl
    symm := .symm
    trans := .trans
  }

abbrev QEquiv α β [BEq α] [Hashable α] := @Quotient (HashMap α β) isSetoid

instance : Max (QEquiv α β) where
  max q₁ q₂ := by
    refine Quotient.liftOn₂ q₁ q₂ (fun a b => Quotient.mk isSetoid (a.unionSup b)) ?_
    intro a₁ b₁ a₂ b₂ h_a h_b
    simp_all [instHasEquivOfSetoid, isSetoid]
    apply unionSup_Equiv h_a h_b

instance : SemilatticeSup (QEquiv α β) := by
  refine SemilatticeSup.mk' ?_ ?_ ?_
  · dsimp [max]
    refine Quotient.ind₂ ?_
    simp [isSetoid]
    exact unionSup_equiv_comm
  · dsimp [max]
    intro q₁ q₂ q₃
    refine Quotient.inductionOn₃ q₁ q₂ q₃ ?_
    simp [isSetoid]
    exact unionSup_equiv_assoc
  · dsimp [max]
    refine Quotient.ind ?_
    simp [isSetoid]
    exact unionSup_equiv_idem

instance : OrderBot (QEquiv α β) where
  bot := Quotient.mk isSetoid HashMap.emptyWithCapacity
  bot_le q := by
    have h : ⟦emptyWithCapacity⟧ ⊔ q = q := by
      dsimp [max]
      refine Quotient.inductionOn q ?_
      intro m
      simp [isSetoid]
      apply Equiv.of_forall_getElem?_eq
      intro k
      rw [unionSup_getElem_of_not_contains emptyWithCapacity m]
      simp
    rw [<- h]
    apply SemilatticeSup.le_sup_left


end Semilattice
end Std.HashMap

namespace Std.DHashMap
variable {β : α → Type v} [BEq α] [LawfulBEq α] [Hashable α]

-- Theorems that are missing from Std.DHashMap
section Augment

theorem get?_insertMany_list [LawfulHashable α] {l : List ((a : α) × β a)} {k : α} :
    get? (insertMany m l) k =
      (l.findSomeRev? (fun ⟨a, b⟩ => if h : a = k then some (congrArg β h ▸ b) else none)).or (get? m k) := by
  induction l generalizing m with
  | nil =>
    rw [get?_insertMany_list_of_contains_eq_false] <;> simp
  | cons x l ih =>
    rcases x with ⟨a, b⟩
    rw [insertMany_cons, ih, get?_insert]
    by_cases h : a = k
    · simp [h]
      refine congrArg ?_ ?_
      · subst h
        simp_all only [List.findSomeRev?_eq_findSome?_reverse, cast_eq]
    · simp [h]
end Augment

-- Take the union of `m₁` and `m₂`, merge conflicting values with the given function and the given
-- bottom value.
--
-- `sup` is supposed to be a join operator, and `bot` is supposed to be a bottom value for a
-- quotient type over values.  This function does not enforce such signatures but some of the
-- theorems about it do.
def unionWith (sup : (a : α) → β a → β a → β a) (bot : (a : α) → β a)
  (m₁ m₂ : Std.DHashMap α β) : Std.DHashMap α β :=
    Std.DHashMap.ofList $ List.map (fun k => ⟨k, sup k (m₁.getD k $ bot k) (m₂.getD k $ bot k)⟩) (m₁.keys ++ m₂.keys)

-- Theorems that show that `unionWith` over a `Semilatticeoid` behaves like a join operation.
section Semilatticeoid
variable [h_sup : (a : α) → SemilatticeSup (β a)] [h_bot : (a : α) → OrderBot (β a)]

abbrev unionSup (m₁ m₂ : Std.DHashMap α β) : Std.DHashMap α β := unionWith (fun _ => max) (fun _ => ⊥) m₁ m₂

lemma unionSup_equiv_idem (m : Std.DHashMap α β) : m.unionSup m ~m m := by {
  unfold unionSup unionWith
  simp
  refine Std.DHashMap.Equiv.of_forall_get?_eq ?_
  intro k
  simp [Std.DHashMap.ofList_eq_insertMany_empty]
  simp only [get?_insertMany_list, List.findSomeRev?_eq_findSome?_reverse,
    List.reverse_append, List.findSome?_append, Option.or_self, get?_empty, Option.or_none]
  simp only [<- List.map_reverse, List.findSome?_map]
  unfold Function.comp
  simp
  by_cases h_mem : k ∈ m
  · simp only [get?_eq_some_get h_mem]
    rw [h_findSome?_eq_some']
    · simp
      symm
      apply DHashMap.get_eq_getD
    · simp [h_mem]
  · simp only [get?_eq_none h_mem]
    rw [h_findSome?_eq_none']
    simp_all
}

lemma unionSup_equiv_comm (m₁ m₂ : Std.DHashMap α β) : m₁.unionSup m₂ ~m m₂.unionSup m₁ := by {
  unfold unionSup unionWith
  refine Std.DHashMap.Equiv.of_forall_get?_eq ?_
  intro k
  simp [Std.DHashMap.ofList_eq_insertMany_empty]
  simp only [get?_insertMany_list, List.findSomeRev?_eq_findSome?_reverse,
    List.reverse_append, List.findSome?_append, get?_empty, Option.or_none]
  simp only [<- List.map_reverse, List.findSome?_map]
  unfold Function.comp
  simp

  by_cases h_mem₁ : k ∈ m₁.keys.reverse
  · by_cases h_mem₂ : k ∈ m₂.keys.reverse
    · repeat rw [h_findSome?_eq_some' h_mem₁, h_findSome?_eq_some' h_mem₂]
      simp [sup_comm]
    · repeat rw [h_findSome?_eq_none' h_mem₂]
      simp [sup_comm]
  · repeat rw [h_findSome?_eq_none' h_mem₁]
    simp [sup_comm]
}

omit h_bot h_sup [DecidableEq α] in
lemma mem_iff_unionWith_mem {m₁ m₂ : Std.DHashMap α β} : k ∈ m₁.unionWith sup bot m₂ ↔ k ∈ m₁ ∨ k ∈ m₂ := by
  unfold unionWith
  simp [Std.DHashMap.mem_ofList]

lemma unionSup_getElem_of_not_contains (m₁ m₂ : Std.DHashMap α β) (h : k ∉ m₁) : (m₁.unionSup m₂).get? k = m₂.get? k := by
  unfold unionSup unionWith
  simp [Std.DHashMap.ofList_eq_insertMany_empty]
  simp [Std.DHashMap.get?_insertMany_list]
  simp [<- List.map_reverse, List.findSome?_map]
  unfold Function.comp
  rw [h_findSome?_eq_none' (l := m₁.keys.reverse)]
  · simp
    by_cases h₂ : k ∈ m₂
    · rw [h_findSome?_eq_some']
      · simp [getD_eq_fallback h]
        simp [get?_eq_some_get, <- get_eq_getD, h₂]
      · simp [h₂]
    · rw [h_findSome?_eq_none']
      · simp [get?_eq_none h₂]
      · simp [h₂]
  · simp [h]

lemma unionSup_getElem_both {m₁ m₂ : Std.DHashMap α β} (h₁ : k ∈ m₁) (h₂ : k ∈ m₂)
    : ((m₁.unionSup m₂).get? k) = (m₁.get k h₁) ⊔ (m₂.get k h₂) := by
  unfold unionSup unionWith
  simp [Std.DHashMap.ofList_eq_insertMany_empty]
  simp [Std.DHashMap.get?_insertMany_list]
  simp [<- List.map_reverse, List.findSome?_map]
  unfold Function.comp
  rw [h_findSome?_eq_some' (l := m₂.keys.reverse)]
  · simp [<- get_eq_getD, h₁, h₂]
  · simp_all

lemma unionSup_getD_of_not_contains (m₁ m₂ : Std.DHashMap α β) (h : k ∉ m₁) {fallback}
    : (m₁.unionSup m₂).getD k fallback = m₂.getD k fallback := by
  repeat rw [getD_eq_getD_get?]
  simp [unionSup_getElem_of_not_contains m₁ m₂ h]

lemma unionSup_getD_both {m₁ m₂ : Std.DHashMap α β} (h₁ : k ∈ m₁) (h₂ : k ∈ m₂)
    : (m₁.unionSup m₂).getD k ⊥ = m₁.get k h₁ ⊔ m₂.get k h₂ := by
  repeat rw [getD_eq_getD_get?]
  unfold unionSup unionWith
  simp [ofList_eq_insertMany_empty]
  simp [getD_eq_getD_get?, get?_insertMany_list]
  simp [<- List.map_reverse, List.findSome?_map]
  unfold Function.comp
  rw [h_findSome?_eq_some' (l := m₂.keys.reverse)]
  · simp [get?_eq_some_get, h₁, h₂]
  · simp_all

lemma unionSup_get?_of_Equiv_left {m₁ m₁' m₂ : Std.DHashMap α β} (h : m₁ ~m m₁') (k : α)
    : (m₁.unionSup m₂).get? k = (m₁'.unionSup m₂).get? k := by
  by_cases h_mem₁ : k ∈ m₁
  · have h_mem₁' := (Equiv.mem_iff h).mp h_mem₁
    by_cases h_mem₂ : k ∈ m₂
    · simp [unionSup_getElem_both, h_mem₁, h_mem₁', h_mem₂]
      rw [Equiv.get_eq h_mem₁ h]
    · rw [Equiv.get?_eq (unionSup_equiv_comm m₁ m₂)]
      rw [Equiv.get?_eq (unionSup_equiv_comm m₁' m₂)]
      simp [unionSup_getElem_of_not_contains, h_mem₂]
      rw [Equiv.get?_eq h]
  · have h_mem₁' : k ∉ m₁' := (not_congr (Equiv.mem_iff h)).mp h_mem₁
    simp [unionSup_getElem_of_not_contains, h_mem₁, h_mem₁']

lemma unionSup_get?_of_Equiv_right {m₁ m₂ m₂' : Std.DHashMap α β} (h : m₂ ~m m₂') (k : α)
    : (m₁.unionSup m₂).get? k = (m₁.unionSup m₂').get? k := by
  rw [Equiv.get?_eq (unionSup_equiv_comm m₁ m₂)]
  rw [Equiv.get?_eq (unionSup_equiv_comm m₁ m₂')]
  exact unionSup_get?_of_Equiv_left h k

lemma unionSup_Equiv_left {m₁ m₁' m₂ : Std.DHashMap α β} (h : m₁ ~m m₁')
    : (m₁.unionSup m₂) ~m (m₁'.unionSup m₂) := by
  apply Equiv.of_forall_get?_eq
  intro k
  apply unionSup_get?_of_Equiv_left h k

lemma unionSup_Equiv_right {m₁ m₂ m₂' : Std.DHashMap α β} (h : m₂ ~m m₂')
    : (m₁.unionSup m₂) ~m (m₁.unionSup m₂') := by
  apply Equiv.of_forall_get?_eq
  intro k
  apply unionSup_get?_of_Equiv_right h k

lemma unionSup_Equiv {m₁ m₁' m₂ m₂' : Std.DHashMap α β} (h₁ : m₁ ~m m₁') (h₂ : m₂ ~m m₂')
    : (m₁.unionSup m₂) ~m (m₁'.unionSup m₂') :=
  Equiv.trans (unionSup_Equiv_left h₁) (unionSup_Equiv_right h₂)

end Std.DHashMap.Semilatticeoid
