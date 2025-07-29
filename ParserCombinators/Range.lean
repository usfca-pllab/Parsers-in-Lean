import Mathlib.Order.Defs.PartialOrder
/-
Integer ranges.

We use a custom data type rather than `Interval` from mathlib because we want to distinguish between
empty intervals depending on starting point.

The definition below is practically the same as `NonemptyInterval` in mathlib but the interpretation
is different: `⟨a, b, ⋯⟩` represents the half-open interval `[a, b)`.
-/
structure Range (α : Type) [LE α] extends α × α where
  fst_le_snd : fst ≤ snd
deriving DecidableEq, Hashable

def range [LE α] (fst snd : α) (h : fst ≤ snd) : Range α := ⟨(fst, snd), h⟩

namespace Range
-- Create an empty range at given value
def empty [Preorder α] (a : α) : Range α := ⟨(a, a), le_rfl⟩
end Range
