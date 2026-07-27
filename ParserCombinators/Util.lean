-- Some helper lemmas not proven in the Stdlib

import Mathlib.Data.List.Basic
import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic
import ParserCombinators.Order

universe u v
variable {α : Type u} [DecidableEq α]

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
lemma h_findSome?_eq_none' {β : α → Type v} {l} (h: k ∉ l) {f : (a : α) → β a}
  : List.findSome? ((fun a ↦ if h : a = k then some (congrArg β h ▸ f a) else none)) l = none
  := by
    rw [List.findSome?_eq_none_iff]
    simp only [dite_eq_right_iff, Option.some_ne_none, imp_false]
    intro x hx hxk
    subst x
    exact h hx

lemma h_findSome?_eq_some' {β : α → Type v} {l} (h: k ∈ l) {f : (a : α) → β a}
  : List.findSome? ((fun a ↦ if h : a = k then some (congrArg β h ▸ f a) else none)) l = some (f k)
  := by
    induction l with
    | nil => simp at h
    | cons a l ih =>
      rw [List.findSome?_cons]
      by_cases hak : a = k
      · subst a
        simp
      · simp only [hak, ↓reduceDIte]
        exact ih (List.mem_cons.mp h |>.resolve_left (Ne.symm hak))

namespace Std.HashMap
variable {β : Type v} [BEq α] [LawfulBEq α] [Hashable α]

section unionSup
variable [instMax : Max β] [instBot : Bot β]

-- Take the union of `m₁` and `m₂`, merge conflicting values with `⊔`.
-- The definition doesn't assume a semilattice structure, but the theorems do.
def unionSup (m₁ m₂ : Std.HashMap α β) : Std.HashMap α β :=
  m₂.fold (init := m₁) fun acc k v =>
    acc.alter k fun old => some (old.getD ⊥ ⊔ v)

/-- Insert one value while joining it with any value already stored at the key. -/
def insertSup (m : Std.HashMap α β) (k : α) (v : β) : Std.HashMap α β :=
  m.insert k (v ⊔ m.getD k ⊥)

end unionSup

variable [s : Setoid β] [semi : Semilatticeoid β s]

/--
A relaxed equivalence relation that checks whether the value of each key is equivalent rather
than equal.
-/
def EquivQuot (m₁ m₂ : Std.HashMap α β) : Prop :=
  map (fun _ => Quotient.mk s) m₁ ~m map (fun _ => Quotient.mk s) m₂

@[inherit_doc]
scoped infixl:50 " ~q " => EquivQuot

namespace EquivQuot

omit [DecidableEq α] [Semilatticeoid β s]

section BasicTheorems
omit [LawfulBEq α]

@[simp]
theorem refl (m : Std.HashMap α β) : m ~q m := by
  simp [EquivQuot]

theorem symm {m₁ m₂ : Std.HashMap α β} : m₁ ~q m₂ → m₂ ~q m₁ := by
  simp [EquivQuot]
  apply Std.HashMap.Equiv.comm.mp

theorem trans {m₁ m₂ m₃ : Std.HashMap α β} : m₁ ~q m₂ → m₂ ~q m₃ → m₁ ~q m₃ := by
  simp [EquivQuot]
  apply Std.HashMap.Equiv.trans

end BasicTheorems

theorem mem_iff {m₁ m₂ : Std.HashMap α β} (h : m₁ ~q m₂) {k : α} : k ∈ m₁ ↔ k ∈ m₂ := by
  unfold EquivQuot at h
  constructor
  · intro h_mem
    apply mem_map.mp $ (Equiv.mem_iff h).mp (mem_map.mpr h_mem)
  · intro h_mem
    apply mem_map.mp $ (Equiv.mem_iff h).mpr (mem_map.mpr h_mem)

theorem getElem_eq [EquivBEq α] {k : α} (hk : k ∈ m₁) (h : m₁ ~q m₂) :
    Quotient.mk s m₁[k] = Quotient.mk s (m₂[k]'(h.mem_iff.mp hk)) := by
  dsimp [EquivQuot] at h
  have hk' : k ∈ map (fun x ↦ Quotient.mk s) m₁ := by simp [hk]
  have hk'' : k ∈ map (fun x ↦ Quotient.mk s) m₂ := by apply (Equiv.mem_iff h).mp hk'
  have h' : (map (fun x ↦ Quotient.mk s) m₁)[k] = (map (fun x ↦ Quotient.mk s) m₂)[k] := by
    apply Equiv.getElem_eq hk' h
  simp [-Quotient.eq] at h'
  exact h'

theorem getElem?_eq [EquivBEq α] {m₁ m₂ : Std.HashMap α β} {k : α} (h : m₁ ~q m₂) :
    Option.map (Quotient.mk s) m₁[k]? = Option.map (Quotient.mk s) m₂[k]? := by
  by_cases h₁ : k ∈ m₁
  · simp [h₁, (mem_iff h).mp h₁, -Quotient.eq]
    exact getElem_eq h₁ h
  · have h₂ : k ∉ m₂ := by
      intro contra
      apply h₁ $ (mem_iff h).mpr contra
    simp [h₁, h₂]

theorem getD_eq [EquivBEq α] {m₁ m₂ : Std.HashMap α β} {k : α} (h : m₁ ~q m₂) :
    Quotient.mk s (m₁.getD k fallback) = Quotient.mk s (m₂.getD k fallback) := by
  by_cases h₁ : k ∈ m₁
  · simp [<- getElem_eq_getD, h₁, (mem_iff h).mp h₁, -Quotient.eq]
    exact getElem_eq h₁ h
  · have h₂ : k ∉ m₂ := by
      intro contra
      apply h₁ $ (mem_iff h).mpr contra
    simp [getD_eq_fallback, h₁, h₂]

end EquivQuot

private def unionSupStep
    (acc : Std.HashMap α β) (entry : α × β) : Std.HashMap α β :=
  acc.alter entry.1 fun old => some (old.getD ⊥ ⊔ entry.2)

omit [DecidableEq α] in
private theorem foldl_unionSupStep_getElem?_of_key_not_mem
    (entries : List (α × β)) (acc : Std.HashMap α β) (k : α)
    (h : ∀ entry ∈ entries, entry.1 ≠ k) :
    (entries.foldl unionSupStep acc)[k]? = acc[k]? := by
  induction entries generalizing acc with
  | nil => rfl
  | cons entry entries ih =>
      rw [List.foldl_cons, ih]
      · simp only [unionSupStep, Std.HashMap.getElem?_alter]
        simp [h entry (by simp)]
      · intro entry' hmem
        exact h entry' (by simp [hmem])

omit [DecidableEq α] [BEq α] [LawfulBEq α] [Hashable α] s semi in
private theorem pairwise_key_ne_of_mem
    {entry : α × β} {entries : List (α × β)}
    (hp : (entry :: entries).Pairwise (fun a b => a.1 ≠ b.1)) :
    ∀ entry' ∈ entries, entry'.1 ≠ entry.1 := by
  intro entry' hmem
  exact ((List.pairwise_cons.mp hp).1 entry' hmem).symm

omit [DecidableEq α] in
private theorem foldl_unionSupStep_getElem?_eq
    (entries : List (α × β))
    (hp : entries.Pairwise (fun a b => a.1 ≠ b.1))
    (acc : Std.HashMap α β) (k : α) :
    (entries.foldl unionSupStep acc)[k]?.map (Quotient.mk s) =
      Option.merge (fun x y => x ⊔ y)
        (acc[k]?.map (Quotient.mk s))
        ((entries.find? (fun entry => entry.1 == k)).map
          (fun entry => Quotient.mk s entry.2)) := by
  induction entries generalizing acc with
  | nil => simp
  | cons entry entries ih =>
      rw [List.foldl_cons]
      by_cases heq : entry.1 = k
      · subst k
        rw [foldl_unionSupStep_getElem?_of_key_not_mem]
        · cases hacc : acc[entry.1]? with
          | none =>
              simp [unionSupStep, hacc]
              exact Quotient.eq.mp
                (@Semilatticeoid.bot_sup_eq' β s _ (a := entry.2))
          | some val =>
              simp [unionSupStep, hacc,
                ← Semilatticeoid.quot_max_eq_max_quot]
        · exact pairwise_key_ne_of_mem hp
      · rw [ih (List.pairwise_cons.mp hp).2]
        have hlookup : (unionSupStep acc entry)[k]? = acc[k]? := by
          simp [unionSupStep, Std.HashMap.getElem?_alter, heq]
        rw [hlookup]
        simp [heq]

omit [DecidableEq α] s semi in
private theorem map_snd_find?_toList
    (m : Std.HashMap α β) (k : α) :
    (m.toList.find? (fun entry => entry.1 == k)).map Prod.snd = m[k]? := by
  cases hfind : m.toList.find? (fun entry => entry.1 == k) with
  | none =>
      simp only [Option.map_none]
      exact (Std.HashMap.getElem?_eq_none
        (Std.HashMap.find?_toList_eq_none_iff_not_mem.mp hfind)).symm
  | some entry =>
      rcases entry with ⟨k', v⟩
      have h :=
        Std.HashMap.find?_toList_eq_some_iff_getKey?_eq_some_and_getElem?_eq_some.mp
          hfind
      simp only [Option.map_some]
      exact h.2.symm

omit [DecidableEq α] in
private theorem unionSup_getElem?_eq_merge
    (m₁ m₂ : Std.HashMap α β) (k : α) :
    Option.map (Quotient.mk s) (m₁.unionSup m₂)[k]? =
      Option.merge (· ⊔ ·)
        (Option.map (Quotient.mk s) m₁[k]?)
        (Option.map (Quotient.mk s) m₂[k]?) := by
  unfold unionSup
  rw [Std.HashMap.fold_eq_foldl_toList]
  change
    Option.map (Quotient.mk s)
        (m₂.toList.foldl unionSupStep m₁)[k]? =
      Option.merge (· ⊔ ·)
        (Option.map (Quotient.mk s) m₁[k]?)
        (Option.map (Quotient.mk s) m₂[k]?)
  rw [foldl_unionSupStep_getElem?_eq]
  · have hmap :
        Option.map (fun entry => Quotient.mk s entry.2)
            (m₂.toList.find? (fun entry => entry.1 == k)) =
          Option.map (Quotient.mk s) m₂[k]? := by
      have hh := congrArg (Option.map (Quotient.mk s))
        (map_snd_find?_toList m₂ k)
      simpa only [Option.map_map, Function.comp_apply] using hh
    rw [hmap]
  · simpa using m₂.distinct_keys_toList

omit [DecidableEq α] in
lemma mem_of_unionSup_mem {m₁ m₂ : Std.HashMap α β} : k ∈ m₁.unionSup m₂ ↔ k ∈ m₁ ∨ k ∈ m₂ := by
  repeat rw [Std.HashMap.mem_iff_isSome_getElem?]
  have h := congrArg Option.isSome
    (unionSup_getElem?_eq_merge m₁ m₂ k)
  have hbool :
      (m₁.unionSup m₂).contains k = (m₁.contains k || m₂.contains k) := by
    simpa using h
  simpa only [Std.HashMap.isSome_getElem?_eq_contains, Bool.or_eq_true] using
    Bool.eq_iff_iff.mp hbool

set_option linter.unusedSectionVars false in
lemma unionSup_getElem_of_not_contains (m₁ m₂ : Std.HashMap α β) (h : k ∉ m₁)
    : Option.map (Quotient.mk s) (m₁.unionSup m₂)[k]? = Option.map (Quotient.mk s) m₂[k]? := by
  rw [unionSup_getElem?_eq_merge]
  simp [h]

set_option linter.unusedSectionVars false in
lemma unionSup_getElem_both {m₁ m₂ : Std.HashMap α β} (h₁ : k ∈ m₁) (h₂ : k ∈ m₂)
    : Option.map (Quotient.mk s) (m₁.unionSup m₂)[k]? = some (⟦m₁[k]⟧ ⊔ ⟦m₂[k]⟧) := by
  rw [unionSup_getElem?_eq_merge]
  simp [h₁, h₂]

set_option linter.unusedSectionVars false in
lemma unionSup_equiv_idem (m : Std.HashMap α β) : m.unionSup m ~q m := by
  apply Std.HashMap.Equiv.of_forall_getElem?_eq
  intro k
  simp only [Std.HashMap.getElem?_map]
  rw [unionSup_getElem?_eq_merge]
  exact Std.IdempotentOp.idempotent _

set_option linter.unusedSectionVars false in
lemma unionSup_equiv_comm (m₁ m₂ : Std.HashMap α β) : m₁.unionSup m₂ ~q m₂.unionSup m₁ := by
  apply Std.HashMap.Equiv.of_forall_getElem?_eq
  intro k
  simp only [Std.HashMap.getElem?_map]
  rw [unionSup_getElem?_eq_merge, unionSup_getElem?_eq_merge]
  exact Std.Commutative.comm _ _

lemma unionSup_getD_of_not_contains (m₁ m₂ : Std.HashMap α β) (h : k ∉ m₁) {fallback}
    : Quotient.mk s ((m₁.unionSup m₂).getD k fallback) = Quotient.mk s (m₂.getD k fallback) := by
  repeat rw [getD_eq_getD_getElem?]
  rw [<- Option.getD_map (f := Quotient.mk s)]
  simp [unionSup_getElem_of_not_contains m₁ m₂ h]

lemma unionSup_getD_of_right_not_contains (m₁ m₂ : Std.HashMap α β) (h : k ∉ m₂) {fallback}
    : Quotient.mk s ((m₁.unionSup m₂).getD k fallback) = Quotient.mk s (m₁.getD k fallback) := by
  rw [EquivQuot.getD_eq (unionSup_equiv_comm m₁ m₂)]
  exact unionSup_getD_of_not_contains m₂ m₁ h

lemma unionSup_getD_both {m₁ m₂ : Std.HashMap α β} (h₁ : k ∈ m₁) (h₂ : k ∈ m₂)
    : Quotient.mk s ((m₁.unionSup m₂).getD k ⊥) = ⟦m₁[k] ⊔ m₂[k]⟧ := by
  rw [getD_eq_getD_getElem?,
    ← Option.getD_map (f := Quotient.mk s)]
  rw [unionSup_getElem_both h₁ h₂]
  simp [← Semilatticeoid.quot_max_eq_max_quot]

lemma unionSup_get?_of_Equiv_left {m₁ m₁' m₂ : Std.HashMap α β} (h : m₁ ~q m₁') (k : α)
    : Option.map (Quotient.mk s) ((m₁.unionSup m₂).get? k) = Option.map (Quotient.mk s) ((m₁'.unionSup m₂).get? k) := by
  repeat rw [get?_eq_getElem?]
  by_cases h_mem₁ : k ∈ m₁
  · have h_mem₁' := (EquivQuot.mem_iff h).mp h_mem₁
    by_cases h_mem₂ : k ∈ m₂
    · simp [unionSup_getElem_both, h_mem₁, h_mem₁', h_mem₂]
      rw [EquivQuot.getElem_eq h_mem₁ h]
    · rw [EquivQuot.getElem?_eq (unionSup_equiv_comm m₁ m₂)]
      rw [EquivQuot.getElem?_eq (unionSup_equiv_comm m₁' m₂)]
      simp [unionSup_getElem_of_not_contains, h_mem₂]
      rw [EquivQuot.getElem?_eq h]
  · have h_mem₁' : k ∉ m₁' := (not_congr (EquivQuot.mem_iff h)).mp h_mem₁
    simp [unionSup_getElem_of_not_contains, h_mem₁, h_mem₁']

lemma unionSup_get?_of_Equiv_right {m₁ m₂ m₂' : Std.HashMap α β} (h : m₂ ~q m₂') (k : α)
    : Option.map (Quotient.mk s) ((m₁.unionSup m₂).get? k) = Option.map (Quotient.mk s) ((m₁.unionSup m₂').get? k) := by
  repeat rw [get?_eq_getElem?]
  rw [EquivQuot.getElem?_eq (unionSup_equiv_comm m₁ m₂)]
  rw [EquivQuot.getElem?_eq (unionSup_equiv_comm m₁ m₂')]
  repeat rw [<- get?_eq_getElem?]
  exact unionSup_get?_of_Equiv_left h k

lemma unionSup_Equiv_left {m₁ m₁' m₂ : Std.HashMap α β} (h : m₁ ~q m₁')
    : (m₁.unionSup m₂) ~q (m₁'.unionSup m₂) := by
  apply Equiv.of_forall_getElem?_eq
  intro k
  repeat rw [<- get?_eq_getElem?]
  simp
  apply unionSup_get?_of_Equiv_left h k

lemma unionSup_Equiv_right {m₁ m₂ m₂' : Std.HashMap α β} (h : m₂ ~q m₂')
    : (m₁.unionSup m₂) ~q (m₁.unionSup m₂') := by
  apply Equiv.of_forall_getElem?_eq
  intro k
  repeat rw [<- get?_eq_getElem?]
  simp
  apply unionSup_get?_of_Equiv_right h k

lemma unionSup_Equiv {m₁ m₁' m₂ m₂' : Std.HashMap α β} (h₁ : m₁ ~q m₁') (h₂ : m₂ ~q m₂')
    : (m₁.unionSup m₂) ~q (m₁'.unionSup m₂') :=
  Equiv.trans (unionSup_Equiv_left h₁) (unionSup_Equiv_right h₂)

set_option linter.unusedSectionVars false in
lemma unionSup_equiv_assoc (m₁ m₂ m₃ : Std.HashMap α β)
    : (m₁.unionSup m₂).unionSup m₃ ~q m₁.unionSup (m₂.unionSup m₃) := by
  apply Std.HashMap.Equiv.of_forall_getElem?_eq
  intro k
  simp only [Std.HashMap.getElem?_map]
  rw [unionSup_getElem?_eq_merge, unionSup_getElem?_eq_merge,
    unionSup_getElem?_eq_merge, unionSup_getElem?_eq_merge]
  exact Std.Associative.assoc _ _ _

lemma empty_unionSup_equiv_self (m : Std.HashMap α β) : emptyWithCapacity.unionSup m ~q m := by
  refine Std.HashMap.Equiv.of_forall_getElem?_eq ?_
  intro k
  simp
  rw [unionSup_getElem_of_not_contains]
  · simp

lemma unionSup_empty_equiv_self (m : Std.HashMap α β) : m.unionSup emptyWithCapacity ~q m :=
  Equiv.trans (unionSup_equiv_comm m emptyWithCapacity) (empty_unionSup_equiv_self m)

/--
A local join-insertion is extensionally equivalent to inserting the new value and joining the
result with the old map.  The local operation is the executable form used by memoization.
-/
theorem insertSup_equiv_insert_unionSup
    (m : Std.HashMap α β) (k : α) (v : β) :
    insertSup m k v ~q (m.insert k v).unionSup m := by
  apply Std.HashMap.Equiv.of_forall_getElem?_eq
  intro x
  simp only [Std.HashMap.getElem?_map]
  by_cases hxk : x = k
  · subst x
    by_cases hk : k ∈ m
    · rw [unionSup_getElem_both (by simp) hk]
      simp [insertSup, hk, ← Std.HashMap.getElem_eq_getD,
        ← Semilatticeoid.quot_max_eq_max_quot]
    · rw [EquivQuot.getElem?_eq
        (unionSup_equiv_comm (m.insert k v) m)]
      rw [unionSup_getElem_of_not_contains m (m.insert k v) hk]
      have h_get : m.getD k ⊥ = ⊥ :=
        Std.HashMap.getD_eq_fallback hk
      simp only [insertSup, Std.HashMap.getElem?_insert, beq_self_eq_true,
        ↓reduceIte, Option.map_some]
      rw [h_get, ← Semilatticeoid.quot_max_eq_max_quot,
        Semilatticeoid.bot_eq_bot, sup_bot_eq]
  · have hkx : k ≠ x := Ne.symm hxk
    by_cases hx : x ∈ m
    · have hx_insert : x ∈ m.insert k v := by simp [hx]
      rw [unionSup_getElem_both hx_insert hx]
      simp [insertSup, Std.HashMap.getElem_insert, hkx, hx]
    · have hx_insert : x ∉ m.insert k v := by simp [hx, hkx]
      rw [unionSup_getElem_of_not_contains (m.insert k v) m hx_insert]
      simp [insertSup, hkx, hx]

-- The Semilattice induced by unionSup
section Semilattice

def isSetoid : Setoid (HashMap α β) where
  r := Std.HashMap.EquivQuot
  iseqv := {
    refl := EquivQuot.refl
    symm := EquivQuot.symm
    trans := EquivQuot.trans
  }

abbrev QEquiv α β [BEq α] [LawfulBEq α] [DecidableEq α] [Hashable α] [s : Setoid β] [Semilatticeoid β s]
  := @Quotient (HashMap α β) isSetoid

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
      simp
      rw [unionSup_getElem_of_not_contains emptyWithCapacity m]
      simp
    rw [<- h]
    apply SemilatticeSup.le_sup_left

-- HashMaps pointwise extend semilatticeoids.

instance instMax : Max (Std.HashMap α β) where
  max a b := a.unionSup b

instance instBot : Bot (Std.HashMap α β) where
  bot := emptyWithCapacity

instance : Semilatticeoid (Std.HashMap α β) isSetoid where
  quot_max_eq_max_quot := by
    rw [max]
    simp [SemilatticeSup.toMax]
    simp [instSemilatticeSupQEquiv]
    simp [SemilatticeSup.mk']
    simp [max]
  bot_repr := emptyWithCapacity
  quot_bot_eq_bot_quot := by
    simp [Bot.bot]

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

omit [DecidableEq α] in
lemma mem_of_unionSup_mem {m₁ m₂ : Std.DHashMap α β} : k ∈ m₁.unionSup m₂ ↔ k ∈ m₁ ∨ k ∈ m₂ := by
  unfold unionSup unionWith
  simp

omit h_bot h_sup in
lemma unionWith_getElem_both {m₁ m₂ : Std.DHashMap α β} (h₁ : k ∈ m₁) (h₂ : k ∈ m₂)
    : ((m₁.unionWith f z m₂).get? k) = f k (m₁.get k h₁) (m₂.get k h₂) := by
  unfold unionWith
  simp [Std.DHashMap.ofList_eq_insertMany_empty]
  simp [Std.DHashMap.get?_insertMany_list]
  simp [<- List.map_reverse, List.findSome?_map]
  unfold Function.comp
  rw [h_findSome?_eq_some' (l := m₂.keys.reverse)]
  · simp [<- get_eq_getD, h₁, h₂]
  · simp_all

omit h_bot h_sup in
lemma unionWith_getElem_not_contains (m₁ m₂ : Std.DHashMap α β) (h : k ∉ m₁) : (m₁.unionWith f z m₂).get? k = f k (z k) <$> m₂.get? k := by
  unfold unionWith
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

omit h_bot h_sup in
lemma unionWith_getElem_not_contains_right (m₁ m₂ : Std.DHashMap α β) (h : k ∉ m₂) : (m₁.unionWith f z m₂).get? k = (f k · (z k)) <$> m₁.get? k := by
  unfold unionWith
  simp [Std.DHashMap.ofList_eq_insertMany_empty]
  simp [Std.DHashMap.get?_insertMany_list]
  simp [<- List.map_reverse, List.findSome?_map]
  unfold Function.comp
  rw [h_findSome?_eq_none' (l := m₂.keys.reverse)]
  · simp
    by_cases h₂ : k ∈ m₁
    · rw [h_findSome?_eq_some']
      · simp [getD_eq_fallback h]
        simp [get?_eq_some_get, <- get_eq_getD, h₂]
      · simp [h₂]
    · rw [h_findSome?_eq_none']
      · simp [get?_eq_none h₂]
      · simp [h₂]
  · simp [h]

omit h_bot h_sup [DecidableEq α] in
lemma mem_iff_unionWith_mem {m₁ m₂ : Std.DHashMap α β} : k ∈ m₁.unionWith sup bot m₂ ↔ k ∈ m₁ ∨ k ∈ m₂ := by
  unfold unionWith
  simp [Std.DHashMap.mem_ofList]

lemma unionSup_getElem_of_not_contains (m₁ m₂ : Std.DHashMap α β) (h : k ∉ m₁) : (m₁.unionSup m₂).get? k = m₂.get? k := by
  unfold unionSup
  rw [unionWith_getElem_not_contains m₁ m₂ h]
  simp [Functor.map, Option.map]
  split <;> simp_all only

lemma unionSup_getElem_both {m₁ m₂ : Std.DHashMap α β} (h₁ : k ∈ m₁) (h₂ : k ∈ m₂)
    : ((m₁.unionSup m₂).get? k) = (m₁.get k h₁) ⊔ (m₂.get k h₂) := by
  unfold unionSup
  exact unionWith_getElem_both h₁ h₂

private lemma unionSup_get?_eq_merge (m₁ m₂ : Std.DHashMap α β) (k : α) :
    (m₁.unionSup m₂).get? k =
      Option.merge (· ⊔ ·) (m₁.get? k) (m₂.get? k) := by
  by_cases h₁ : k ∈ m₁
  · by_cases h₂ : k ∈ m₂
    · rw [unionSup_getElem_both h₁ h₂, get?_eq_some_get h₁,
        get?_eq_some_get h₂]
      rfl
    · unfold unionSup
      rw [unionWith_getElem_not_contains_right m₁ m₂ h₂,
        get?_eq_some_get h₁, get?_eq_none h₂]
      simp
  · rw [unionSup_getElem_of_not_contains m₁ m₂ h₁,
      get?_eq_none h₁]
    cases m₂.get? k <;> rfl

lemma unionSup_equiv_idem (m : Std.DHashMap α β) : m.unionSup m ~m m := by
  apply Std.DHashMap.Equiv.of_forall_get?_eq
  intro k
  rw [unionSup_get?_eq_merge]
  exact Std.IdempotentOp.idempotent _

lemma unionSup_equiv_comm (m₁ m₂ : Std.DHashMap α β) : m₁.unionSup m₂ ~m m₂.unionSup m₁ := by
  apply Std.DHashMap.Equiv.of_forall_get?_eq
  intro k
  rw [unionSup_get?_eq_merge, unionSup_get?_eq_merge]
  exact Std.Commutative.comm _ _

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

lemma unionSup_equiv_assoc (m₁ m₂ m₃ : Std.DHashMap α β)
    : (m₁.unionSup m₂).unionSup m₃ ~m m₁.unionSup (m₂.unionSup m₃) := by
  apply Std.DHashMap.Equiv.of_forall_get?_eq
  intro k
  rw [unionSup_get?_eq_merge, unionSup_get?_eq_merge,
    unionSup_get?_eq_merge, unionSup_get?_eq_merge]
  exact Std.Associative.assoc _ _ _

end Std.DHashMap.Semilatticeoid
