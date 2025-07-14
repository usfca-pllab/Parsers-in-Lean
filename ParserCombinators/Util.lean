-- Some helper lemmas not proven in the Stdlib

import Mathlib.Data.List.Basic

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
