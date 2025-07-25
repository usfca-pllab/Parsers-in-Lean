/- A monotonic version of the state monad. -/

import Mathlib.Order.Lattice
import Aesop
import Mathlib.Control.Bifunctor
import ParserCombinators.Util
import Batteries.Control.AlternativeMonad

universe u

-- A monotonically-increasing state monad transformer
def MStateT (σ : Type u) [SemilatticeSup σ] (μ : Type u → Type u) [Monad μ] (α : Type u) :=
  (s : σ) → μ (α × {s' : σ // s ≤ s'})

-- A monotonically-increasing state monad
abbrev MState (σ : Type u) [SemilatticeSup σ] (α : Type u) := MStateT σ Id

namespace MStateT

def run [SemilatticeSup σ] [Monad μ] (m : MStateT σ μ α) (s : σ) := Bifunctor.snd (fun x => x.val) <$> m s

def merge {σ : Type u} [Monad μ] [SemilatticeSup σ]  (a : α) (s : σ) : MStateT σ μ α :=
  fun s' => pure ⟨a, ⟨s ⊔ s', le_sup_right⟩⟩

end MStateT

-- TODO: provide a LawfulMonad instance
instance [Monad μ] (σ : Type u) [SemilatticeSup σ] : Monad (MStateT σ μ) where
  pure a s := pure ⟨a, ⟨s, le_refl s⟩⟩
  bind x f s := do
    let (a, s') ← x s
    let (b, s'') ← f a s'
    let h_mono := Preorder.le_trans s s' s'' s'.property s''.property
    pure (b, ⟨s'', h_mono⟩)

instance [Monad μ] (σ : Type u) [SemilatticeSup σ] : MonadLift μ (MStateT σ μ) where
  monadLift m s := do
    let a ← m
    pure (a, ⟨s, le_refl s⟩)

-- This is not a lawful monad, set needs to augment the state
--
-- TODO: prove modified versions of MonadState laws
instance [Monad μ] [SemilatticeSup σ] : MonadStateOf σ (MStateT σ μ) where
  get s := pure ⟨s, ⟨s, le_refl s⟩⟩
  set := MStateT.merge PUnit.unit
  modifyGet f s :=
    let (a, s') := f s
    MStateT.merge a s' s

class abbrev CollectionLike (μ : Type u → Type u) := Monad μ, Alternative μ

instance [Monad μ] [Alternative μ] : CollectionLike μ where
  failure := Alternative.failure
  orElse := Alternative.orElse

-- Alternatives that yield a semilattice structure
class SemilatticeAlt (μ : Type u → Type u) extends Alternative μ, LawfulAlternative μ where
  alt_idem (m : μ α) : (m <|> m) = m
  alt_comm (m₁ m₂ : μ α) : (m₁ <|> m₂) = (m₂ <|> m₁)
  alt_assoc (m₁ m₂ m₃ : μ α) : ((m₁ <|> m₂) <|> m₃) = (m₁ <|> m₂ <|> m₃)
    := symm $ LawfulAlternative.orElse_assoc m₁ m₂ m₃

example {τ} (typ : τ → Type u) μ [BEq τ] [Hashable τ] [CollectionLike μ] :=
  Quotient (Std.DHashMap.isSetoid τ (fun t => Std.HashMap Int (μ (typ t))))

abbrev setoid {τ} (typ : τ → Type u) μ [BEq τ] [Hashable τ] [CollectionLike μ] := Std.DHashMap.isSetoid τ (fun t => Std.HashMap Int (μ (typ t)))

-- A semilattice for the memoized types
instance [Alternative μ] : Max (μ α) where
  max m₁ m₂ := m₁ <|> m₂

instance [SemilatticeAlt μ] : SemilatticeSup (μ α) :=
  SemilatticeSup.mk' SemilatticeAlt.alt_comm SemilatticeAlt.alt_assoc SemilatticeAlt.alt_idem

instance [SemilatticeAlt μ] : OrderBot (μ α) where
  bot := failure
  bot_le a := by
    have h : a = failure ⊔ a := symm $ LawfulAlternative.failure_orElse a
    rw [h]
    exact SemilatticeSup.le_sup_left failure a

-- A semilattice for MemoData
--
-- this fixes the tag type
structure MemoData {τ} (typ : τ → Type u) μ [BEq τ] [Hashable τ] [CollectionLike μ] where
  table : Quotient (setoid typ μ)

set_option diagnostics true
instance  [BEq τ] [LawfulBEq τ] [Hashable τ] [CollectionLike μ] [SemilatticeAlt μ]
  (typ : τ → Type u)
    : Max (MemoData typ μ) where
  max a b := ⟨by
    refine Quotient.liftOn₂ a.table b.table ?_ ?_
    · intro a b
      exact Quotient.mk (setoid typ μ) $ a.unionWith b $ fun t inner₁ inner₂ => inner₁.unionWith inner₂
    · intro a₁ b₁ a₂ b₂ h_a h_b
      unfold setoid Std.DHashMap.isSetoid
      -- simp_all only [Quotient.eq]
      apply Std.DHashMap.Equiv.of_forall_get?_eq
      intro k
      sorry
  ⟩

instance  [BEq τ] [LawfulBEq τ] [Hashable τ] [CollectionLike μ] (typ : τ → Type u) : SemilatticeSup (MemoData typ μ) := by
  refine SemilatticeSup.mk' (α := MemoData typ μ) ?_ ?_ ?_
  · sorry -- sup_comm
  · sorry -- sup_assoc
  · rintro ⟨tbl⟩
    simp [max, Std.DHashMap.unionWith]
