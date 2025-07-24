/- A monotonic version of the state monad. -/

import Mathlib.Order.Lattice
import Aesop
import Mathlib.Control.Bifunctor

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
