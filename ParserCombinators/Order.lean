import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic
import Batteries.Control.AlternativeMonad
import Mathlib.Control.Traversable.Basic
import Mathlib.Order.TypeTags
import Aesop
import Mathlib.Order.BoundedOrder.Lattice

-- Structures related to order theory.

-- A `Semilatticeoid` is a type that can be quotiened into a semilattice structure
--
-- We also require a `Max` implementation that abides by the quotient structure
class Semilatticeoid α (s : Setoid α) extends SemilatticeSup (Quotient s), OrderBot (Quotient s), Max α where
  bot_repr : α
  quot_max_eq_max_quot (a b : α) : (Quotient.mk s a) ⊔ ⟦b⟧ = ⟦a ⊔ b⟧
  quot_bot_eq_bot_quot : Quotient.mk s bot_repr = Bot.bot (α := Quotient s)

instance [s : Setoid α] [l : Semilatticeoid α s] : Bot α where
  bot := l.bot_repr

instance [s : Setoid α] [l : Semilatticeoid α s] : Preorder α where
  le a b := ⟦a⟧ ≤ ⟦b⟧
  le_refl a := Preorder.le_refl ⟦a⟧
  le_trans a b c := Preorder.le_trans (α := Quotient s) ⟦a⟧ ⟦b⟧ ⟦c⟧

namespace Semilatticeoid
-- the semilattice axioms that can be lifted to `Semilatticeoid` structure
variable {s : Setoid α} [Semilatticeoid α s]


theorem bot_eq_bot : Quotient.mk s ⊥ = ⊥ := by {
  dsimp [Bot.bot]
  rw [quot_bot_eq_bot_quot]
}

theorem bot_sup_eq' {a : α} : Quotient.mk s (⊥ ⊔ a) = ⟦a⟧ := by {
  dsimp [Bot.bot]
  rw [<- quot_max_eq_max_quot, quot_bot_eq_bot_quot]
  apply bot_sup_eq
}

theorem lift_le_sup_left {a b : α} : a ≤ a ⊔ b := by {
  dsimp [LE.le]
  rw [<- quot_max_eq_max_quot]
  exact le_sup_left
}

theorem lift_le_sup_right {a b : α} : b ≤ a ⊔ b := by {
  dsimp [LE.le]
  rw [<- quot_max_eq_max_quot]
  exact le_sup_right
}

theorem lift_sup_le {a b c : α} : a ≤ c → b ≤ c → a ⊔ b ≤ c := by {
  dsimp [LE.le]
  rw [<- quot_max_eq_max_quot]
  exact sup_le
}

theorem antisymm_equiv {a b : α} (h₁ : a ≤ b) (h₂ : b ≤ a)
    : a ≈ b := by {
  apply Quotient.exact
  dsimp [LE.le] at h₁ h₂
  exact antisymm h₁ h₂
}

-- additional theorems
theorem lift_sup_comm  {a b : α} : Quotient.mk s (a ⊔ b) = Quotient.mk s (b ⊔ a) := by
  repeat rw [<- quot_max_eq_max_quot]
  exact sup_comm ⟦a⟧ ⟦b⟧

end Semilatticeoid

-- Alternatives that yield a semilattice structure.
-- The definitions we use require decidability, so we don't extend `Alternative` but `Applicative`.
class SemilatticeAlt (μ : Type u → Type u) extends Applicative μ, LawfulApplicative μ where
  failure : μ α
  orElse [DecidableEq α] : μ α → μ α → μ α
  alt_idem [DecidableEq α] (m : μ α) : (orElse m m) = m
  alt_comm [DecidableEq α] (m₁ m₂ : μ α) : (orElse m₁ m₂) = (orElse m₂ m₁)
  alt_assoc [DecidableEq α] (m₁ m₂ m₃ : μ α) : (orElse (orElse m₁ m₂) m₃) = (orElse m₁ (orElse m₂ m₃))
  -- alternative laws
  map_failure (f : α → β) : f <$> failure = failure
  failure_seq (x : μ α) : (failure : μ (α → β)) <*> x = failure
  orElse_failure [DecidableEq α] (x : μ α) : orElse x failure = x
  failure_orElse [DecidableEq α] (y : μ α) : orElse failure y = y
  -- This is a relaxed version of the relevant law: the original law holds if `f` is a bijection.
  -- We phrase it in terms of `orElse` but it's effectively stating that `Functor.map` is monotonic (?)
  -- f <$> x ⊔ f <$> y ≤ f <$> (x ⊔ y)
  map_orElse [DecidableEq α] [DecidableEq β] (x y : μ α) (f : α → β)
    : orElse (orElse (f <$> x) (f <$> y)) (f <$> orElse x y) = (f <$> orElse x y)

namespace SemilatticeAlt
instance (priority := low) (μ : Type u → Type u) [DecidableEq α] [SemilatticeAlt μ] : Max (μ α) where
  max := orElse

instance (priority := low) (μ : Type u → Type u) [DecidableEq α] [SemilatticeAlt μ] : SemilatticeSup (μ α) :=
  SemilatticeSup.mk' alt_comm alt_assoc alt_idem

instance (priority := low) (μ : Type u → Type u) [DecidableEq α] [SemilatticeAlt μ] : OrderBot (μ α) where
  bot := failure
  bot_le a := by
    rw [<- orElse_failure a]
    apply SemilatticeSup.le_sup_right

instance {α : Type u} (μ : Type u → Type u) [DecidableEq α] [SemilatticeAlt μ] : OrElse (μ α) where
  orElse x y := SemilatticeAlt.orElse x (y ())

end SemilatticeAlt

-- The flat lattice structure over a type, i.e. the constant domain.
--
-- It is defined directly rather than using `WithTop` and `WithBot` because we
-- need to construct the `⊔` operator anyway, and prove the associated theorems.
inductive Const (α : Type u) where
  | bot
  | top
  | some (val : α)
  deriving BEq, Hashable, DecidableEq, Repr

namespace Const

instance [ToString α] : ToString (Const α) where
  toString
  | bot => "⊥"
  | top => "⊤"
  | some a => "some " ++ ToString.toString a

instance : Bot (Const α) where
  bot := bot

instance : Top (Const α) where
  top := top

instance [DecidableEq α] : Max (Const α) where
  max
  | bot, x | x, bot => x
  | _, top | top, _ => top
  | some x, some y => if _h : x = y then some x else top

instance [DecidableEq α] : Min (Const α) where
  min
  | bot, _ | _, bot => bot
  | x, top | top, x => x
  | some x, some y => if _h : x = y then some x else bot

instance [DecidableEq α] : Lattice (Const α) := by
  refine Lattice.mk' ?_ ?_ ?_ ?_ ?_ ?_
  · intro a b
    dsimp [max]
    cases a <;> cases b <;> simp_all
    rename_i a b
    by_cases h : a = b <;> simp_all
    · intro h
      subst h
      contradiction
  · intro a b c
    dsimp [max]
    cases a <;> cases b <;> cases c <;> simp_all
    · rename_i x y ; (by_cases h : x = y <;> simp_all)
    · rename_i x y ; (by_cases h : x = y <;> simp_all)
    · rename_i x y ; (by_cases h : x = y <;> simp_all)
    · rename_i x y z
      by_cases h : x = y <;> by_cases h' : y = z <;> simp_all
  · intro a b
    dsimp [min]
    cases a <;> cases b <;> simp_all
    rename_i a b
    by_cases h : a = b <;> simp_all
    · intro h
      subst h
      contradiction
  · intro a b c
    dsimp [min]
    cases a <;> cases b <;> cases c <;> simp_all
    · rename_i x y ; (by_cases h : x = y <;> simp_all)
    · rename_i x y ; (by_cases h : x = y <;> simp_all)
    · rename_i x y ; (by_cases h : x = y <;> simp_all)
    · rename_i x y z
      by_cases h : x = y <;> by_cases h' : y = z <;> simp_all
  · intro a b
    dsimp [min, max]
    cases a <;> cases b <;> simp_all
    rename_i a b
    by_cases h : a = b <;> simp_all
  · intro a b
    dsimp [min, max]
    cases a <;> cases b <;> simp_all
    rename_i a b
    by_cases h : a = b <;> simp_all

instance [DecidableEq α] : OrderBot (Const α) where
  bot_le a := by
    have h : a = ⊥ ⊔ a := by simp [max, Bot.bot]
    rw [h]
    apply SemilatticeSup.le_sup_left

instance [DecidableEq α] : OrderTop (Const α) where
  le_top a := by
    have h : a = ⊤ ⊓ a := by
      simp [min, Top.top]
      cases a <;> simp
    rw [h]
    apply SemilatticeInf.inf_le_left

instance : Monad Const where
  pure := some
  bind
  | bot, _ => bot
  | top, _ => top
  | some a, f => f a

instance : LawfulMonad Const where
  map_const := by simp [Functor.map, Functor.mapConst]
  id_map x := by
    simp [Functor.map]
    cases x <;> simp
  seqLeft_eq x y:= by
    simp [SeqLeft.seqLeft, Functor.map, Seq.seq]
    unfold Function.const Function.comp
    simp only []
    cases x <;> cases y <;> simp_all
  seqRight_eq x y := by
    simp [SeqRight.seqRight, Functor.map, Seq.seq]
    unfold Function.const Function.comp
    cases x <;> cases y <;> simp_all
  pure_seq g x := by simp [Seq.seq, Functor.map]
  bind_pure_comp f x := by
    simp [Bind.bind, Functor.map, Pure.pure]
    rfl
  bind_map := by
    simp [Bind.bind, Functor.map, Seq.seq]
  pure_bind x f :=  by simp [Bind.bind]
  bind_assoc x f g := by
    simp [Bind.bind]
    cases x <;> simp

instance : SemilatticeAlt Const where
  failure := bot
  orElse := max
  alt_idem := sup_idem
  alt_comm := sup_comm
  alt_assoc := sup_assoc
  map_failure f := by simp [Functor.map]
  failure_seq x := by simp [Seq.seq]
  orElse_failure x := by apply sup_bot_eq
  failure_orElse x := by apply bot_sup_eq
  map_orElse {α β} [DecidableEq α] [DecidableEq β] x y (f : α → β) := by
    simp [Functor.map]
    unfold Function.comp
    cases x <;> cases y <;> simp_all <;> try apply bot_le
    · apply le_top
    · apply le_top
    · rename_i x y
      dsimp [max]
      by_cases h : x = y <;> simp_all
      constructor <;> apply le_top

instance : Traversable Const where
  traverse f
  | bot => pure bot
  | top => pure top
  | some x => some <$> f x

instance : LawfulTraversable Const where
  id_traverse x := by
    simp [traverse, Pure.pure, Functor.map]
    cases x <;> simp_all
  comp_traverse f g x := by
    simp [traverse, Pure.pure, Functor.map, Functor.Comp.mk, Functor.Comp.map]
    cases x <;> simp
  traverse_eq_map_id f x := by
    simp [traverse, Pure.pure, Functor.map]
    cases x <;> simp
  naturality η α β f x := by
    simp [traverse]
    cases x <;> simp
    · apply η.preserves_pure'
    · apply η.preserves_pure'
    · simp [η.preserves_map]

end Const
