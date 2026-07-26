/- A monotonic version of the state monad. -/

import Mathlib.Control.Bifunctor
import ParserCombinators.Order
import ParserCombinators.Util

universe u

-- A monotonically-increasing state monad transformer.
-- The increasing data is given by an abstraction function.
def MStateT (σ : Type u) [s : Setoid σ] [Semilatticeoid σ s] (μ : Type u → Type u) [Monad μ] (α : Type u) :=
  (s : σ) → μ (α × {s' : σ // s ≤ s'})

-- A monotonically-increasing state monad
abbrev MState (σ : Type u) [s : Setoid σ] [Semilatticeoid σ s] (α : Type u) := MStateT σ Id α

namespace MStateT

def run [s : Setoid σ] [Semilatticeoid σ s] [Monad μ] (m : MStateT σ μ α) (s : σ) := Bifunctor.snd (fun x => x.val) <$> m s

def merge {σ : Type u} [Monad μ] [s : Setoid σ] [Semilatticeoid σ s]  (a : α) (s : σ) : MStateT σ μ α :=
  fun s' => pure ⟨a, ⟨s ⊔ s', Semilatticeoid.lift_le_sup_right⟩⟩

end MStateT

-- TODO: provide a LawfulMonad instance
instance [Monad μ] (σ : Type u) [s : Setoid σ] [Semilatticeoid σ s] : Monad (MStateT σ μ) where
  pure a s := pure ⟨a, ⟨s, le_refl s⟩⟩
  bind x f s := do
    let (a, s') ← x s
    let (b, s'') ← f a s'
    let h_mono := Preorder.le_trans s s' s'' s'.property s''.property
    pure (b, ⟨s'', h_mono⟩)

instance [Monad μ] (σ : Type u) [s : Setoid σ] [Semilatticeoid σ s] : MonadLift μ (MStateT σ μ) where
  monadLift m s := do
    let a ← m
    pure (a, ⟨s, le_refl s⟩)

-- This is not a lawful monad, set needs to augment the state
--
-- TODO: prove modified versions of MonadState laws
instance [Monad μ] [s : Setoid σ] [Semilatticeoid σ s] : MonadStateOf σ (MStateT σ μ) where
  get s := pure ⟨s, ⟨s, le_refl s⟩⟩
  set := MStateT.merge PUnit.unit
  modifyGet f s :=
    let (a, s') := f s
    MStateT.merge a s' s

abbrev MemoKey (τ : Type u) := List (τ × ℕ)

abbrev MemoEntryKey (τ : Type u) := MemoKey τ × ℕ

-- A semilattice for MemoData
--
-- this fixes the tag type
abbrev MemoData {τ} (typ : τ → Type u) μ [BEq τ] [Hashable τ] [Monad μ] :=
  Std.DHashMap τ (fun t => Std.HashMap (MemoEntryKey τ) (Std.HashMap ℕ (μ (typ t))))
namespace MemoData
variable {τ} {typ : τ → Type u} {μ : Type u → Type u} [BEq τ] [DecidableEq τ] [Hashable τ] [Monad μ]

-- This provides a deliberately coarser equivalence relation over MemoData than `Std.DHashMap.Equiv`.
--
-- We require the values to be equivalent
@[simp]
def Equiv {typ : τ → Type u} [semilat_μ : SemilatticeAlt μ] [∀ t : τ, DecidableEq (typ t)] (a b : MemoData typ μ) : Prop :=
  let f (t : τ) m := Quotient.mk (Std.HashMap.isSetoid
     (α := MemoEntryKey τ)
     (β := (Std.HashMap ℕ (μ (typ t))))
     (s := Std.HashMap.isSetoid (s := semilat_μ.setoid)))
     m
  (a.map f).Equiv $ b.map f

namespace Equiv

instance  [SemilatticeAlt μ] [∀ t : τ, DecidableEq (typ t)] : Equivalence (Equiv (μ := μ) (typ := typ)) where
  refl := by simp
  symm {x y} := by
    simp
    exact Std.DHashMap.Equiv.symm
  trans {x y z} := by
    simp
    exact Std.DHashMap.Equiv.trans

end Equiv

instance setoid (typ : τ → Type u) μ [Monad μ] [SemilatticeAlt μ] [∀ t : τ, DecidableEq (typ t)] : Setoid (MemoData typ μ) where
  r := Equiv
  iseqv := Equiv.instEquivalence

variable [dec_eq : ∀ t : τ, DecidableEq (typ t)] [semilat_μ : SemilatticeAlt μ]

instance  [BEq τ] [LawfulBEq τ] [Hashable τ] [Monad μ]
  (typ : τ → Type u) [∀ t : τ, DecidableEq (typ t)]
    : Max (MemoData typ μ) where
  max a b := a.unionWith (fun _ => Std.HashMap.unionSup (instMax := Std.HashMap.instMax)) (fun _ => Std.HashMap.emptyWithCapacity) b

@[inline]
abbrev hm_quot_mk t := Quotient.mk (Std.HashMap.isSetoid
     (α := MemoEntryKey τ)
     (β := (Std.HashMap ℕ (μ (typ t))))
     (s := Std.HashMap.isSetoid (s := SemilatticeAlt.setoid)))

private lemma unionWith_quotient_lift (k : τ) (a₁ a₂ : MemoData typ μ) [LawfulBEq τ]
    : Option.map (fun m => hm_quot_mk k m) ((a₁ ⊔ a₂).get? k) = ((a₁.map hm_quot_mk).unionSup (a₂.map hm_quot_mk)).get? k := by
  dsimp [max]
  by_cases h₁ : k ∈ a₁
  · by_cases h₂ : k ∈ a₂
    · have hm₁ : k ∈ a₁.map hm_quot_mk := by simpa
      have hm₂ : k ∈ a₂.map hm_quot_mk := by simpa
      rw [Std.DHashMap.unionWith_getElem_both h₁ h₂]
      rw [Std.DHashMap.unionSup_getElem_both hm₁ hm₂]
      simp [hm_quot_mk]
      rfl
    · have hm₂ : k ∉ a₂.map hm_quot_mk := by simpa
      rw [Std.DHashMap.unionWith_getElem_not_contains_right a₁ a₂ h₂]
      rw [Std.DHashMap.Equiv.get?_eq
        (Std.DHashMap.unionSup_equiv_comm
          (a₁.map hm_quot_mk) (a₂.map hm_quot_mk))]
      rw [Std.DHashMap.unionSup_getElem_of_not_contains _ _ hm₂]
      rw [Std.DHashMap.get?_map, Std.DHashMap.get?_eq_some_get h₁]
      simp only [Option.map_some]
      apply congrArg some
      have h' := Std.HashMap.unionSup_empty_equiv_self
        (s := Std.HashMap.isSetoid) (a₁.get k h₁)
      unfold hm_quot_mk
      exact Quotient.eq.mpr h'
  · by_cases h₂ : k ∈ a₂
    · have hm₁ : k ∉ a₁.map hm_quot_mk := by simpa
      rw [Std.DHashMap.unionWith_getElem_not_contains a₁ a₂ h₁]
      rw [Std.DHashMap.unionSup_getElem_of_not_contains _ _ hm₁]
      rw [Std.DHashMap.get?_map, Std.DHashMap.get?_eq_some_get h₂]
      simp only [Option.map_some]
      apply congrArg some
      have h' := Std.HashMap.empty_unionSup_equiv_self
        (s := Std.HashMap.isSetoid) (a₂.get k h₂)
      unfold hm_quot_mk
      exact Quotient.eq.mpr h'
    · have hm₁ : k ∉ a₁.map hm_quot_mk := by simpa
      rw [Std.DHashMap.unionWith_getElem_not_contains a₁ a₂ h₁]
      rw [Std.DHashMap.get?_eq_none h₂]
      rw [Std.DHashMap.unionSup_getElem_of_not_contains _ _ hm₁]
      rw [Std.DHashMap.get?_map, Std.DHashMap.get?_eq_none h₂]
      rfl

private lemma unionWith_quotient_lift' (a₁ a₂ : MemoData typ μ) [LawfulBEq τ]
    : (Std.DHashMap.map hm_quot_mk (a₁ ⊔ a₂)).Equiv ((a₁.map hm_quot_mk).unionSup (a₂.map hm_quot_mk)) := by
  apply Std.DHashMap.Equiv.of_forall_get?_eq
  intro k
  simp
  apply unionWith_quotient_lift k a₁ a₂

omit [DecidableEq τ] dec_eq semilat_μ in
private theorem quot_max_wf [LawfulBEq τ] [SemilatticeAlt μ] [∀ t : τ, DecidableEq (typ t)]
  [DecidableEq τ] (a₁ b₁ a₂ b₂ : MemoData typ μ) (h₁ : a₁.Equiv a₂) (h₂ : b₁.Equiv b₂)
    : (Quotient.mk (setoid typ μ) $ a₁ ⊔ b₁) = (Quotient.mk (setoid typ μ) $ a₂ ⊔ b₂) := by
  simp_all only [setoid, Equiv, Quotient.eq]
  apply Std.DHashMap.Equiv.of_forall_get?_eq
  intro k
  have h := unionWith_quotient_lift (typ := typ) (μ := μ) k
  unfold hm_quot_mk at h
  simp [Std.DHashMap.get?_map]
  repeat rw [h]
  apply Std.DHashMap.Equiv.get?_eq
  exact Std.DHashMap.unionSup_Equiv h₁ h₂

section Order
variable [LawfulBEq τ] (typ : τ → Type u) [∀ t : τ, DecidableEq (typ t)]

omit typ in
instance : Max (Quotient (setoid typ μ)) where
  max q₁ q₂ := by
    refine Quotient.liftOn₂ q₁ q₂ (fun a b => Quotient.mk (setoid typ μ) $ max a b) ?_
    exact id quot_max_wf

instance : SemilatticeSup (Quotient (setoid typ μ)) := by
  have h := unionWith_quotient_lift (typ := typ) (μ := μ)
  have h' := unionWith_quotient_lift' (typ := typ) (μ := μ)
  unfold hm_quot_mk at h
  refine SemilatticeSup.mk' (α := Quotient (setoid typ μ)) ?_ ?_ ?_
  · refine Quotient.ind₂ ?_
    intro a b
    unfold max
    simp [instMaxQuotientSetoid, setoid]
    apply Std.DHashMap.Equiv.of_forall_get?_eq
    intro k
    simp [Std.DHashMap.get?_map]
    repeat rw [h]
    apply Std.DHashMap.Equiv.get?_eq
    apply Std.DHashMap.unionSup_equiv_comm
  · intro q₁ q₂ q₃
    refine Quotient.inductionOn₃ q₁ q₂ q₃ ?_
    intro a b c
    unfold max
    simp [instMaxQuotientSetoid, setoid]
    apply Std.DHashMap.Equiv.of_forall_get?_eq
    intro k
    simp [Std.DHashMap.get?_map]
    repeat rw [h]
    rw [Std.DHashMap.unionSup_get?_of_Equiv_left (h' a b)]
    rw [Std.DHashMap.unionSup_get?_of_Equiv_right (h' b c)]
    apply Std.DHashMap.Equiv.get?_eq
    apply Std.DHashMap.unionSup_equiv_assoc
  · refine Quotient.ind ?_
    intro m
    unfold max
    simp [instMaxQuotientSetoid, setoid]
    apply Std.DHashMap.Equiv.of_forall_get?_eq
    intro k
    rw [Std.DHashMap.get?_map]
    repeat rw [h]
    apply Std.DHashMap.Equiv.get?_eq
    apply Std.DHashMap.unionSup_equiv_idem

instance : OrderBot (Quotient (setoid typ μ)) where
  bot := ⟦Std.DHashMap.emptyWithCapacity⟧
  bot_le := by
    apply Quotient.ind
    intro a
    apply left_eq_sup.mp
    simp [SemilatticeSup.toMax]
    unfold SemilatticeSup.sup
    simp [instSemilatticeSupQuotientSetoid]
    simp only [SemilatticeSup.mk']
    simp [setoid, Max.max]
    apply Std.DHashMap.Equiv.of_forall_get?_eq
    intro k
    simp
    rw [Std.DHashMap.unionWith_getElem_not_contains_right]
    · simp [Functor.map]
      unfold Function.comp
      simp
      apply congrFun
      apply congrArg
      apply funext
      intro m
      simp [Std.HashMap.isSetoid]
      apply Std.HashMap.EquivQuot.symm (s := Std.HashMap.isSetoid)
      have h := Std.HashMap.unionSup_empty_equiv_self (s := Std.HashMap.isSetoid) m
      exact h
    · simp


instance (typ : τ → Type u) [∀ t : τ, DecidableEq (typ t)] : Semilatticeoid (MemoData typ μ) (setoid typ μ) where
  bot_repr := Std.DHashMap.emptyWithCapacity
  quot_max_eq_max_quot := by
    rw [Max.max]
    simp [SemilatticeSup.toMax]
    unfold SemilatticeSup.sup
    simp [instSemilatticeSupQuotientSetoid]
    simp [SemilatticeSup.mk']
    simp [instMaxQuotientSetoid]
  quot_bot_eq_bot_quot := by
    simp [Bot.bot]

end MemoData.Order
