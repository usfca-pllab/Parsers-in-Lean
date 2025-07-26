/- A monotonic version of the state monad. -/

import Mathlib.Order.Lattice
import Aesop
import Mathlib.Control.Bifunctor
import ParserCombinators.Order
import ParserCombinators.Util
import Batteries.Control.AlternativeMonad

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

example {τ} (typ : τ → Type u) μ [BEq τ] [Hashable τ] [Monad μ] :=
  Quotient (Std.DHashMap.isSetoid τ (fun t => Std.HashMap ℕ (μ (typ t))))

-- A semilattice for MemoData
--
-- this fixes the tag type
abbrev MemoData {τ} (typ : τ → Type u) μ [BEq τ] [Hashable τ] [Monad μ] :=
  Std.DHashMap τ (fun t => Std.HashMap ℕ (μ (typ t)))
namespace MemoData
variable {τ} {typ : τ → Type u} {μ : Type u → Type u} [BEq τ] [Hashable τ] [Monad μ]

-- This provides a deliberately coarser equivalence relation over MemoData than `Std.DHashMap.Equiv`.
@[simp]
def Equiv {typ : τ → Type u} (a b : MemoData typ μ) : Prop :=
  let f _ m := Quotient.mk Std.HashMap.isSetoid m
  (a.map f).Equiv $ b.map f

namespace Equiv

instance : Equivalence (Equiv (μ := μ) (typ := typ)) where
  refl := by simp
  symm {x y} := by
    simp
    exact Std.DHashMap.Equiv.symm
  trans {x y z} := by
    simp
    exact Std.DHashMap.Equiv.trans

end Equiv

instance setoid (typ : τ → Type u) μ [Monad μ] : Setoid (MemoData typ μ) where
  r := Equiv
  iseqv := Equiv.instEquivalence

instance  [BEq τ] [LawfulBEq τ] [Hashable τ] [Monad μ] [SemilatticeAlt μ]
  (typ : τ → Type u) [∀ t : τ, DecidableEq (typ t)]
    : Max (MemoData typ μ) where
  max a b := a.unionWith (fun _ => Std.HashMap.unionSup) (fun _ => Std.HashMap.emptyWithCapacity) b

private lemma mem_map_Equiv_left {α : Type u} {β δ : α → Type v} {k : α} {f : (a : α) → β a → δ a} [BEq α] [LawfulBEq α] [Hashable α] {m₁ m₂ : Std.DHashMap α β}
  (h : Std.DHashMap.Equiv (m₁.map f) (m₂.map f)) (h_mem : k ∈ m₁) : k ∈ m₂ := by
  apply Std.DHashMap.mem_of_mem_map
  refine (Std.DHashMap.Equiv.mem_iff h).mp ?_
  exact Std.DHashMap.mem_map.mpr h_mem

private lemma mem_map_Equiv {α : Type u} {β δ : α → Type v} {k : α} {f : (a : α) → β a → δ a} [BEq α] [LawfulBEq α] [Hashable α] {m₁ m₂ : Std.DHashMap α β}
  (h : Std.DHashMap.Equiv (m₁.map f) (m₂.map f)) : k ∈ m₁ ↔ k ∈ m₂ := by
  constructor
  · exact mem_map_Equiv_left h
  · exact mem_map_Equiv_left (Std.DHashMap.Equiv.comm.mp h)

@[inline]
abbrev hm_quot_mk t := Quotient.mk (Std.HashMap.isSetoid (α := ℕ) (β := μ (typ t)))

private lemma unionWith_quotient_lift (k : τ) (a₁ a₂ : MemoData typ μ) [LawfulBEq τ] [DecidableEq τ]
  [Monad μ] [SemilatticeAlt μ] [∀ t : τ, DecidableEq (typ t)]
    : Option.map (fun m => hm_quot_mk k m) ((a₁ ⊔ a₂).get? k) = ((a₁.map hm_quot_mk).unionSup (a₂.map hm_quot_mk)).get? k := by
  dsimp [max]
  by_cases h : k ∈ a₁
  · have h_or : k ∈ a₁ ∨ k ∈ a₂ := Or.inl h
    -- rw [Std.DHashMap.get?_eq_some_get]
    · simp_all [hm_quot_mk]
      by_cases h₂ : k ∈ a₂
      · unfold Std.DHashMap.unionSup  Std.DHashMap.unionWith
        simp [Std.DHashMap.ofList_eq_insertMany_empty]
        simp [Std.DHashMap.get?_insertMany_list]
        simp [<- List.map_reverse, List.findSome?_map]
        unfold Function.comp
        simp only []
        rw [h_findSome?_eq_some']
        · simp only [Option.some_or, Option.map_some]
          rw [h_findSome?_eq_some']
          · simp [hm_quot_mk, Std.DHashMap.getD_map]
            simp [<- Std.DHashMap.get_eq_getD, Std.DHashMap.get?_eq_some_get, h, h₂]
            rfl
          · simp_all
        · simp_all
      · have h_comm := Std.DHashMap.unionSup_equiv_comm (Std.DHashMap.map hm_quot_mk a₁) (Std.DHashMap.map hm_quot_mk a₂)
        rw [Std.DHashMap.Equiv.get?_eq h_comm]
        rw [Std.DHashMap.unionSup_getElem_of_not_contains]
        · rw [Std.DHashMap.get?_map]
          unfold hm_quot_mk
          simp only [Std.DHashMap.unionWith, Std.DHashMap.ofList_eq_insertMany_empty]
          simp [Std.DHashMap.get?_insertMany_list, -Quotient.eq]
          simp only [<- List.map_reverse, List.findSome?_map]
          unfold Function.comp
          simp only []
          have h_keys₂ : k ∉ a₂.keys.reverse := by
            intro h
            simp at h
            contradiction
          simp [Std.HashMap.isSetoid]
          rw [h_findSome?_eq_none']
          rw [h_findSome?_eq_some']
          simp
          rw [Std.DHashMap.get?_eq_some_get (h := h)]
          · simp
            rw [Std.DHashMap.getD_eq_fallback h₂]
            rw [<- Std.DHashMap.get_eq_getD (h := h)]
            refine Std.HashMap.unionSup_empty_equiv_self (Std.DHashMap.get a₁ k h)
          · simp [h]
          · simp [h₂]
        · simp [h₂]
  · by_cases h₂ : k ∈ a₂
    · have h_or : k ∈ a₁ ∨ k ∈ a₂ := Or.inr h₂
      simp_all
      unfold hm_quot_mk
      rw [Std.DHashMap.unionSup_getElem_of_not_contains]
      simp only [Std.DHashMap.unionWith, Std.DHashMap.ofList_eq_insertMany_empty]
      simp [Std.DHashMap.get?_insertMany_list, -Quotient.eq]
      simp only [<- List.map_reverse, List.findSome?_map]
      unfold Function.comp
      simp only []
      have h_keys₁ : k ∉ a₁.keys.reverse := by
        intro h
        simp at h
        contradiction
      simp [Std.HashMap.isSetoid]
      rw [h_findSome?_eq_some']
      rw [h_findSome?_eq_none']
      simp
      rw [Std.DHashMap.get?_eq_some_get (h := h₂)]
      · simp
        rw [Std.DHashMap.getD_eq_fallback h]
        rw [<- Std.DHashMap.get_eq_getD (h := h₂)]
        refine Std.HashMap.empty_unionSup_equiv_self (Std.DHashMap.get a₂ k h₂)
      · simp [h]
      · simp [h₂]
      · simp_all
    · repeat rw [Std.DHashMap.get?_eq_none]
      · simp
      · intro h'
        apply Std.DHashMap.mem_iff_unionWith_mem.mp at h'
        simp_all
      · intro h'
        apply Std.DHashMap.mem_iff_unionWith_mem.mp at h'
        simp_all

private theorem quot_max_wf [LawfulBEq τ] [SemilatticeAlt μ] [∀ t : τ, DecidableEq (typ t)]
  [DecidableEq τ] (a₁ b₁ a₂ b₂ : MemoData typ μ) (h₁ : a₁.Equiv a₂) (h₂ : b₁.Equiv b₂)
    : (Quotient.mk (setoid typ μ) $ a₁ ⊔ b₁) = (Quotient.mk (setoid typ μ) $ a₂ ⊔ b₂) := by
  -- TODO: fix then prove, for speed
  simp_all only [setoid, Equiv, Quotient.eq]
  apply Std.DHashMap.Equiv.of_forall_get?_eq
  intro k
  have h := unionWith_quotient_lift (typ := typ) (μ := μ) k
  unfold hm_quot_mk at h
  simp [Std.DHashMap.get?_map]
  repeat rw [h]
  apply Std.DHashMap.Equiv.get?_eq
  exact Std.DHashMap.unionSup_Equiv h₁ h₂

instance [BEq τ] [LawfulBEq τ] [Hashable τ] [Monad μ] [SemilatticeAlt μ] [DecidableEq τ] [∀ t : τ, DecidableEq (typ t)] : Max (Quotient (setoid typ μ)) where
  max q₁ q₂ := by
    refine Quotient.liftOn₂ q₁ q₂ (fun a b => Quotient.mk (setoid typ μ) $ max a b) ?_
    exact id quot_max_wf

instance  [BEq τ] [LawfulBEq τ] [Hashable τ] [Monad μ] [SemilatticeAlt μ] [DecidableEq τ] (typ : τ → Type u) [∀ t : τ, DecidableEq (typ t)] : SemilatticeSup (Quotient (setoid typ μ)) := by
  refine SemilatticeSup.mk' (α := Quotient (setoid typ μ)) ?_ ?_ ?_
  · sorry -- sup_comm
  · sorry -- sup_assoc
  · simp [max]
    refine Quotient.ind ?_
    intro m
    simp [setoid, Std.DHashMap.isSetoid]
    sorry


instance  [BEq τ] [LawfulBEq τ] [Hashable τ] [Monad μ] [SemilatticeAlt μ] [DecidableEq τ] (typ : τ → Type u) [∀ t : τ, DecidableEq (typ t)] : Semilatticeoid (MemoData typ μ) (setoid typ μ) where
  quot_max_eq_max_quot := by
    dsimp [max]
    sorry

end MemoData
