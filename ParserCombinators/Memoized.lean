-- A sketch of the port of the memoized combinators from Haskell, without the
-- CPS transformation

import Std.Data.DHashMap.Basic
import Std.Data.HashMap.Basic
import Std.Data.HashMap.AdditionalOperations
import Std.Data.HashMap.Lemmas
import Mathlib.Control.Traversable.Basic
import Mathlib.Control.Fold
import Mathlib.Data.ENat.Basic
import Mathlib.Data.ENat.Defs
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Multiset.DershowitzManna
import Mathlib.Order.OrderIsoNat
import Batteries.Control.AlternativeMonad
import ParserCombinators.MState
import ParserCombinators.Util
import Aesop

-- β is the alphabet: parsers work over Array β
universe u v
variable {τ} { α β : Type u } {tag : τ → Type u} { μ : Type u → Type u } [BEq τ] [LawfulBEq τ] [Hashable τ] [DecidableEq τ] [semilat_μ : SemilatticeAlt μ] [h_eq : ∀ t : τ, DecidableEq (tag t)]

def startState {μ} [Monad μ] : MemoData tag μ :=
  Std.DHashMap.emptyWithCapacity

abbrev UChar := ULift Char
abbrev UString := ULift String

@[inline]
def liftA2 {F : Type u → Type v} [Applicative F] {α β γ : Type u} (f : α → β → γ) (fa : F α) (fb : F β) : F γ :=
  f <$> fa <*> fb

@[inline]
abbrev ResultMap (μ : Type u → Type u) α := (Std.HashMap ℕ (μ α))

def joinUnderCache {γ} [DecidableEq γ] [Monad μ] (s1 s2 : MStateT (MemoData tag μ) (ReaderM (Array β)) (ResultMap μ γ))
    : MStateT (MemoData tag μ) (ReaderM (Array β)) (ResultMap μ γ) :=
  liftA2 (fun m1 m2 => Std.HashMap.unionSup m1 m2) s1 s2

-- Some of the α's here should become existential/hidden
abbrev Parser
  {τ} {tag : τ → Type u} [BEq τ] [LawfulBEq τ] [Hashable τ] [DecidableEq τ] [∀ t : τ, DecidableEq (tag t)]
  (β : Type u) (μ : Type u → Type u) [Monad μ] [SemilatticeAlt μ] (α : Type u) :=
  ℕ → MStateT (MemoData tag μ) (ReaderM (Array β)) (ResultMap μ α)
namespace Parser
variable [Monad μ] [Traversable μ]
def bind [DecidableEq β'] (x : Parser (tag := tag) β μ α) (f : α → Parser (tag := tag) β μ β')
  := fun pos => do
    let pivotToResult ← x pos
    let actions : List (μ (MStateT (MemoData tag μ) (ReaderM (Array β)) (ResultMap μ β'))) :=
      pivotToResult.toList.map (fun ((j : ℕ), ma) => (fun a => f a j) <$> ma)
    actions.foldl
      (Traversable.foldl joinUnderCache)
      (pure Std.HashMap.emptyWithCapacity)

def failure : Parser (tag := tag) β μ α := fun _pos => pure Std.HashMap.emptyWithCapacity

def orElse [DecidableEq α] (r1 r2 : Parser (tag := tag) β μ α) pos :=
    joinUnderCache (r1 pos) (r2 pos)
end Parser

instance [Monad μ] : Functor (Parser (tag := tag) β μ) where
  map f x := Functor.map (Std.HashMap.map (fun _ => Functor.map f)) ∘ x

-- N.B. Have to define `pure` separately so that we can use it in `seq`
-- Defines the ability to create the simplest parser possible
instance [Monad μ] : Pure (Parser (tag := tag) β μ) where
  pure a := fun pos => pure {(pos, pure a)}

-- Deep embedding of Monad for parsers.
--
-- From Sculthorpe, et al. <https://dl.acm.org/doi/10.1145/2500365.2500602>
--
-- We adapt it to force calculating the join as soon as possible.
inductive ParserM (β : Type u) (μ : Type u → Type u) [Monad μ] [SemilatticeAlt μ] (α : Type u) where
  | Return (a : α)
  | Bind (p : Parser (tag := tag) β μ α') (f : α' → ParserM β μ α)

namespace ParserM
variable [Monad μ] [SemilatticeAlt μ]
def bind [Monad μ] [Traversable μ] : (ParserM (tag := tag) β μ α') → (α' → ParserM (tag := tag) β μ α) → ParserM (tag := tag) β μ α
  | ParserM.Return a, k => k a
  | ParserM.Bind p f, k => ParserM.Bind p (fun x => bind (f x) k)

instance [Monad μ] [Traversable μ] : Monad (ParserM (tag := tag) β μ) where
  pure := ParserM.Return
  bind := ParserM.bind

def lift (p : Parser (tag := tag) β μ α) : ParserM (tag := tag) β μ α := ParserM.Bind p ParserM.Return

instance [Monad μ] [Traversable μ] [DecidableEq α] : Bot (ParserM (tag := tag) β μ α) where
  bot := lift Parser.failure

variable [Monad μ] [Traversable μ] [DecidableEq α]
def lower : ParserM (tag := tag) β μ α →  Parser (tag := tag) β μ α
  | ParserM.Return x => pure x
  | ParserM.Bind x k => Parser.bind x (fun x => lower (k x))

open ParserM in
instance [Monad μ] [Traversable μ] [DecidableEq α] : Max (ParserM (tag := tag) β μ α) where
  max
  | Return x, Return y => ParserM.Bind (Parser.orElse (Pure.pure x) (Pure.pure y)) Return
  | Return x, ParserM.Bind y k => lift $ Parser.orElse (pure x) (y.bind (lower ∘ k))
  | ParserM.Bind x k, Return y => lift $ Parser.orElse (x.bind (lower ∘ k)) (pure y)
  | ParserM.Bind p₁ k₁, ParserM.Bind p₂ k₂ => lift $ Parser.orElse (p₁.bind (lower ∘ k₁)) (p₂.bind (lower ∘ k₂))

end ParserM

-- TODO: prove that the relevant laws hold for the monad instance
-- TODO: prove that ParserM is a `SemilatticeSup` + `OrderBot`
-- TODO: prove that the relevant laws hold for lower/lift

open ParserM (lift lower)

def epsilon [Monad μ] : ParserM (tag := tag) β μ PUnit := lift $ fun pos => pure {(pos, pure $ PUnit.unit)}

def terminal [Monad μ] (s : String) : ParserM (tag := tag) UChar μ UString := lift $ fun pos => do
  let input ← read
  if pos >= 0 && (s.data.map ULift.up).toArray.isPrefixOf (input.extract pos) then
    let endPos := pos + s.length
    pure {(endPos, pure $ ULift.up s)}
  else
    pure Std.HashMap.emptyWithCapacity

def terminal' [Monad μ] [DecidableEq β] (t: β) : ParserM (tag := tag) β μ β := lift $ fun pos => do
  let input ← read
  if pos >= 0 && some t = input[pos]? then
    pure {(pos + 1, pure t)}
  else
    pure Std.HashMap.emptyWithCapacity

/--
Recursion budget counters for `memoize`. Keeps track of the remaining recursion
budget for each tag.

If the budget for a tag does not exist, it will be initialized to a finite
number on first use (e.g., by `dec`).

This allows us to form a `WellFoundedRelation` for finite types.
-/
def Counter τ [Hashable τ] [BEq τ] := Std.HashMap τ ℕ

namespace Counter
variable [Hashable τ] [BEq τ] [LawfulBEq τ] [LawfulHashable τ]

def empty : Counter τ := Std.HashMap.emptyWithCapacity

def unwrap : Counter τ → Std.HashMap τ ℕ := id

/-- The generator of the less-than relation: `a.PLessThan b` if they differ by only one value. -/
@[simp]
def PLessThan (a b : Counter τ) : Prop :=
  ∃ t : τ, (∃ h_a : t ∈ a.unwrap, (h_b : t ∈ b.unwrap) → a.unwrap[t] < b.unwrap[t]) ∧
    ∀ t' : τ, t ≠ t' → a.unwrap[t']? = b.unwrap[t']?

/-- Convert the counters to a multiset of extended naturals (missing elements are mapped to `⊤`). -/
noncomputable def toMultiset [fintype : Fintype τ] (a : Counter τ) : Multiset ℕ∞ :=
  (Multiset.ofList fintype.elems.toList).map (fun t => (NatCast.natCast <$> a.get? t).getD ⊤)

variable [Fintype τ]

instance : LT (Counter τ) where
  lt := Relation.TransGen PLessThan

instance (priority := high) wf : WellFoundedRelation (Counter τ) where
  rel := LT.lt
  wf := by
    apply WellFounded.transGen
    apply Subrelation.wf ?_ (InvImage.wf toMultiset Multiset.instWellFoundedisDershowitzMannaLT.wf)
    simp [Subrelation, WellFoundedRelation.rel]
    unfold InvImage
    unfold unwrap id
    intro a b t h_a h_lt h_eq
    unfold Multiset.IsDershowitzMannaLT
    use a.toMultiset - {NatCast.natCast a.unwrap[t]}
    use {NatCast.natCast a.unwrap[t]}
    have h_multiset_a : a.toMultiset = a.toMultiset.erase ↑a.unwrap[t] + {↑a.unwrap[t]} := by
      rw [add_comm]
      simp
      rw [Multiset.cons_erase]
      simp [toMultiset, Fintype.complete]
      use t
      simp [h_a, unwrap]
    have h_a_get_t : (fun x ↦ (Option.map NatCast.natCast a.unwrap[x]?).getD ⊤) t = ENat.instNatCast.natCast a.unwrap[t] := by
      simp [unwrap, h_a]
    unfold unwrap id at h_a_get_t
    by_cases h_b : t ∈ b.unwrap <;> simp [unwrap] at h_b
    · use {NatCast.natCast b.unwrap[t]}
      have h_b_get_t : (fun x ↦ (Option.map NatCast.natCast b.unwrap[x]?).getD ENat.instOrderTop.top) t = ↑b.unwrap[t] := by
        simp [unwrap, h_b]
      unfold unwrap id at h_b_get_t
      simp
      constructor
      · assumption
      · constructor
        · rw [<- Multiset.add_sub_cancel (s := b.toMultiset) (t := {↑ b.unwrap[t]})]
          · simp [toMultiset, unwrap]
            rw [<- h_a_get_t]
            rw [<- h_b_get_t]
            repeat rw [<- Multiset.map_erase_of_mem] <;> try simp [Fintype.complete]
            apply Multiset.map_congr (by rfl)
            intro t'
            intro h_t'_neq_t
            rw [<- Finset.erase_val, Finset.mem_val] at h_t'_neq_t
            simp at h_t'_neq_t
            have a_get_t'_eq_b_get_t' := h_eq t' $ h_t'_neq_t.left.imp symm
            rw [a_get_t'_eq_b_get_t']
          · simp [toMultiset]
            use t
            simp [Fintype.complete, h_b, unwrap]
        · exact h_lt h_b
    · use {⊤}
      have h_b_get_t : (fun x ↦ (Option.map NatCast.natCast b.unwrap[x]?).getD ⊤) t = ENat.instOrderTop.top := by
        simp [unwrap, h_b]
      unfold unwrap id at h_b_get_t
      simp
      constructor
      · assumption
      · rw [<- Multiset.add_sub_cancel (s := b.toMultiset) (t := {⊤})]
        · simp [toMultiset, unwrap]
          rw [<- h_a_get_t]
          nth_rw 2 [<- h_b_get_t]
          repeat rw [<- Multiset.map_erase_of_mem] <;> try simp [Fintype.complete]
          apply Multiset.map_congr (by rfl)
          intro t'
          intro h_t'_neq_t
          rw [<- Finset.erase_val, Finset.mem_val] at h_t'_neq_t
          simp at h_t'_neq_t
          have a_get_t'_eq_b_get_t' := h_eq t' $ h_t'_neq_t.left.imp symm
          rw [a_get_t'_eq_b_get_t']
        · simp [toMultiset]
          use t
          simp [Fintype.complete, h_b]

/-- Decrement the value for the given tag if it exists, otherwise insert given default budget. -/
def dec (counter : Counter τ) (t : τ) (default : ℕ) : Counter τ :=
  counter.insert t (counter.getD t default - 1)

set_option linter.unusedSectionVars false in
omit [DecidableEq τ] [Fintype τ] in
theorem dec_lt_if_not_zero {t : τ} {m : Counter τ} (h : m.unwrap[t]? ≠ some 0) : m.dec t n < m := by
  simp [dec, LT.lt]
  apply Relation.TransGen.single
  simp_all [unwrap]
  use t
  constructor
  · use Or.symm (Or.inr rfl)
    · intro h_mem
      simp [h_mem] at h
      simp [<- Std.HashMap.getElem_eq_getD, h_mem]
      exact Nat.zero_lt_of_ne_zero h
  · intro t' h_neq
    simp [Std.HashMap.getElem?_insert, h_neq]

instance : GetElem? (Counter τ) τ ℕ (fun m k => k ∈ m.unwrap) where
  getElem m k h := m.unwrap[k]
  getElem? m k := m.unwrap[k]?

end Counter

-- NOTE: There is a counter for each tag and we saturate it in N steps where N = remaining string
-- length.  This definition is similar to `withFuel`, and it should work on non-cyclic grammars
-- as seen in Frost and Hafiz <https://dl.acm.org/doi/10.1145/1149982.1149988>.  This is how we
-- guarantee that `memoize` terminates.

-- Ideally, we could try for a fixpoint-like approach where our initial results are empty and we
-- gradually re-run the parser until it saturates? This might get tricky, though.

--
-- We need one more ingredient:
--
-- 1. Each tag has correct data, e.g. t ∈ memo → memo.get? t ⊆ memoize g pos
--
-- (1) will ensure that we always produce correct results.
def memoize [Monad μ] [Traversable μ] [DecidableEq α] [Fintype τ]
  (counter : Counter τ := Counter.empty)
  (g : ((t : τ) → ParserM (tag := tag) β μ (tag t)) → (t : τ) → ParserM (tag := tag) β μ (tag t)) (t : τ)
    : ParserM (tag := tag) β μ (tag t) :=
  if h : counter[t]? = some 0 then ⊥
  else
    lift $ fun pos => do
      let positionMap := (← get).getD t ⊥
      -- Check if we have cached results for this tag and position
      match positionMap[pos]? with
      | some cachedResult => pure cachedResult
      | none =>
        -- No cached result for this position, compute and cache
        let results ← lower (g (memoize (counter.dec t ((← read).size - pos)) g) t) pos
        -- Cache the new results
        modifyGet $ fun memo =>
          let positionMap := memo.getD t ⊥
          let results := results ⊔ positionMap.getD pos ⊥
          -- TODO: use alter
          (results, memo.insert t $ positionMap.insert pos results)
termination_by counter
decreasing_by
  apply Counter.dec_lt_if_not_zero h

-- Testing

-- Will use `Const` as the concrete monad (some is success, ⊥ is failure, ⊤ is ambiguity)

-- TODO: prove that runParser "commutes" with the parser combinators
def runParser [Monad μ] [Traversable μ] [DecidableEq α] (p : ParserM (tag := tag) β μ α) (input : Array β) (pos : ℕ := 0) : (Std.HashMap ℕ (μ α)) × MemoData tag μ :=
  let stateTResult := (p.lower pos).run startState
  let readerResult := stateTResult.run input
  readerResult

def runParser' [Monad μ] [Traversable μ] [DecidableEq α] (p : ParserM (tag := tag) UChar μ α) (input : String) (pos : ℕ := 0) : (Std.HashMap ℕ (μ α)) × MemoData tag μ :=
  runParser p (input.toList.map ULift.up).toArray pos

def emptyTag : PUnit → Type := fun _ => PUnit

instance (t : PUnit) : DecidableEq (emptyTag t) := by
  dsimp [emptyTag]
  infer_instance

def runParserO {μ : Type → Type} {α : Type} [Monad μ] [SemilatticeAlt μ]
  [Traversable μ] [DecidableEq α]
  (p : ParserM (tag := emptyTag) UChar μ α) (input : String) (pos : ℕ := 0)
    : (Std.HashMap ℕ (μ α)) × MemoData emptyTag μ :=
  runParser'.{0} p input pos

-- Checking to make sure that runParser has correct type
#guard (runParserO (μ := Const) epsilon "test").1.toList == [(0, Const.some PUnit.unit)]

-- Testing running the parsers (had to extract just the hashmap
-- because Lean couldn't extract a string from the full return type)
#guard (runParserO (μ := Const) (terminal "hello") "hello world").1.toList == [(5, Const.some $ ULift.up "hello")]
#guard (runParserO (μ := Const) (terminal "wo") "hello world" 6).1.toList == [(8, Const.some $ ULift.up "wo")]

-- Failure
#guard (runParserO (μ := Const) (terminal "llo") "hello world" 5).1.isEmpty

-- Edge case for empty string
#guard (runParserO (μ := Const) (terminal "") "hello world" 6).1.toList == [(6, Const.some $ ULift.up "")]


-- Testing instances:

-- Functor (`<$>`)
def funcParser : ParserM (tag := emptyTag) UChar Const String := (fun _ => "matched!") <$> terminal "hello"
def funcParser2 : ParserM (tag := emptyTag) UChar Const ℕ := (fun x => x * 3) <$> terminal "hello" $> 2

-- TODO: (Madi) Just beef this up by testing edge cases
#guard (runParserO (μ := Const) funcParser "hello world").1.toList == [(5, Const.some "matched!")]
#guard (runParserO (μ := Const) funcParser "hell").1.toList == []
#guard (runParserO (μ := Const) funcParser2 "hello").1.toList == [(5, Const.some 6)]

-- Alternative (`⊔`)
def altParser [Monad μ] [Traversable μ] : ParserM (tag := tag) UChar μ UString :=
  terminal "hello" ⊔ terminal "goodbye"

#guard (runParserO (μ := Const) altParser "hello").1.toList == [(5, Const.some $ ULift.up "hello")]
#guard (runParserO (μ := Const) altParser "goodbye").1.toList == [(7, Const.some $ ULift.up "goodbye")]
-- #guard (runParserO (μ := List) altParser "hello").1.toList == [(5, [ULift.up "hello"])]
-- #guard (runParserO (μ := List) altParser "goodbye").1.toList == [(7, [ULift.up "goodbye"])]

-- Concatenation via bind (`>>=`)
def concatParser {μ : Type → Type} [Monad μ] [Traversable μ] [SemilatticeAlt μ] : ParserM (tag := emptyTag) UChar μ (Int × Int) :=
  (terminal "hello" $> 1) >>= (fun a => terminal "goodbye" $> (a, 2))
-- NOTE(maemre): the commented-out tests crash
#guard (runParserO (μ := Const) concatParser "hello").1.toList == []
#guard (runParserO (μ := Const) concatParser "goodbye").1.toList == []
#guard (runParserO (μ := Const) concatParser "hellogoodbye").1.toList == [(12, Const.some (1, 2))]
-- #guard (runParser.{0} (μ := List) concatParser "hello").1.toList == []
-- #guard (runParserO (μ := List) concatParser "goodbye").1.toList == []
-- #guard (runParser.{0} (μ := List) (concatParser ()) "hellogoodbye").1.toList == [(12, Const.some (1, 2))]

-- An ambiguous ε-free parser
def concatParser2 [Monad μ] [Traversable μ] : ParserM (tag := tag) UChar μ PUnit :=
  let p1 := terminal "a" ⊔ terminal "aa"
  p1 >>= fun _ => p1 $> PUnit.unit

-- Ambiguity under Const vs. List
#guard (runParserO (μ := Const) concatParser2 "").1.toList == []
#guard (runParserO (μ := Const) concatParser2 "a").1.toList == []
#guard (runParserO (μ := Const) concatParser2 "aa").1.toList == [(2, Const.some PUnit.unit)]
#guard (runParserO (μ := Const) concatParser2 "aaa").1.toList == [(2, Const.some PUnit.unit), (3, Const.some PUnit.unit)]

-- #guard (runParserO (μ := List) concatParser2 "").1.toList == []
-- NOTE(maemre): The code below crashes for some reason
-- #eval (runParser.{0} (μ := List) concatParser2 "a").1.toList == []
-- #eval (runParser.{0} (μ := List) concatParser2 "aa").1.toList

@[inline]
def concat [Monad μ] [Traversable μ] [Append α] (p₁ p₂ : ParserM (tag := tag) β μ α)
    : ParserM (tag := tag) β μ α := liftA2 Append.append p₁ p₂

instance [Append α] : Append (ULift α) where
  append a b := ULift.up $ a.down ++ b.down

-- recursion via the inner parser function
partial def recursiveParser [Monad μ] [Traversable μ] : ParserM (tag := tag) UChar μ UString :=
  let p1 : ParserM (tag := tag) UChar μ UString := terminal "a"
  let p2 : ParserM (tag := tag) UChar μ UString := terminal "b"
  (concat p1 recursiveParser ⊔ p2)

-- #guard (runParserO (μ := Const) recursiveParser "ab").1.toList == [(2, Const.some $ ULift.up "ab")]

-- bounded recursion for a single parser
def withFuel [Monad μ] [Traversable μ] [DecidableEq α] (g : ParserM (tag := tag) β μ α → ParserM (tag := tag) β μ α) : ℕ → ParserM (tag := tag) β μ α
  | 0 => ⊥
  | Nat.succ fuel => g (withFuel g fuel)

def fueledParser [Monad μ] [Traversable μ] : ℕ → ParserM (tag := tag) UChar μ UString := withFuel $ fun recur =>
  let p1 : ParserM (tag := tag) UChar μ UString := terminal "a"
  let p2 : ParserM (tag := tag) UChar μ UString := terminal "b"
  (concat p1 recur ⊔ p2)

#guard (runParserO (μ := Const) (fueledParser 4) "aaab").1.toList = [(4, Const.some { down := "aaab" })]
#guard (runParserO (μ := Const) (fueledParser 3) "aaab").1.toList = []

-- bounded recursion for parser families
def withFuel' {τ'} [Monad μ] [Traversable μ] [DecidableEq α] (g : (τ' → ParserM (tag := tag) β μ α) → τ' → ParserM (tag := tag) β μ α) : ℕ → (t : τ') → ParserM (tag := tag) β μ α
  | 0 => fun _ => ⊥
  | Nat.succ fuel => g (withFuel' g fuel)

/-
X₀ -> a X₁ | c
X₁ -> b X₀

X₀ =>⋆ (ab⋆)c
-/
def mutualRec : ℕ → ParserM (tag := tag) UChar Const UString := flip (withFuel' (τ' := Fin 2) $ fun recur t =>
  match t with
    | 0 =>
      -- A
      concat (terminal "a") (recur 1) ⊔ terminal "c"
    | 1 =>
      -- B
      concat (terminal "b") (recur 0)
  ) (0 : Fin 2)

#guard (runParserO (mutualRec 5) "ababc").1.toList == [(5, Const.some { down := "ababc" })]
#guard (runParserO (mutualRec 4) "ababc").1.toList == []

-- Induction theorem for bounded recursion
theorem withFuel'_induction {τ} [Monad μ] [Traversable μ] [DecidableEq α] {g : (τ → ParserM (tag := tag) β μ α) → τ → ParserM (tag := tag) β μ α}
  {p : (τ → ParserM (tag := tag) β μ α) → Prop}
  (h_base : p (fun _ => ⊥))
  (h_recur : ∀ recur, p recur -> p (g recur))
  (n : ℕ)
    : p (withFuel' g n) := by induction n with
  | zero =>
    unfold withFuel'
    exact h_base
  | succ n' ih =>
    unfold withFuel'
    exact h_recur (withFuel' g n') ih

-- want something this:
def memo [Monad μ] [Traversable μ] (g : ParserM (tag := tag) β μ α → ParserM (tag := tag) β μ α) : ParserM (tag := tag) β μ α :=
  sorry

def memo' {τ} [Monad μ] [Traversable μ] (g : (τ → ParserM (tag := tag) β μ α) → τ → ParserM (tag := tag) β μ α) : τ → ParserM (tag := tag) β μ α :=
  sorry

-- this just defines a subset-like relation on the parse results, the details of implementation
-- aren't that crucial
def subsumed [Monad μ] [Traversable μ] [DecidableEq α] (a b : ResultMap μ α) : Prop :=
  ∀ k (h : k ∈ a), (a[k]'h ⊔ b[k]?.getD ⊥) = b[k]?.getD ⊥

infix:50 " ≼ " => subsumed

-- then, we want:
theorem memo_sound [Monad μ] [Traversable μ] [DecidableEq α] (g : ParserM (tag := tag) β μ α → ParserM (tag := tag) β μ α) n s
    : (runParser (withFuel g n) s).1 ≼ (runParser (μ := μ) (memo g) s).1 := by
  sorry

theorem memo_complete [Monad μ] [Traversable μ] [DecidableEq α] (g : ParserM (tag := tag) β μ α → ParserM (tag := tag) β μ α) s
    : ∃ n, (runParser (μ := μ) (memo g) s).1 ≼ (runParser (withFuel g n) s).1 := by
  sorry

def mutualRecMemo : ParserM (τ := Fin 2) (tag := fun _ => UString) UChar Const UString := (memoize (τ := Fin 2) (α := UString) Counter.empty $ fun recur t =>
  match t with
    | 0 => by
      -- A
      refine concat (terminal "a") (recur 1) ⊔ terminal "c"
    | 1 => by
      -- B
      refine concat (terminal "b") (recur 0)
  ) (0 : Fin 2)

#guard (runParser' mutualRecMemo "ababc").1.toList == [(5, Const.some { down := "ababc" })]


-- S -> S a | a
def leftRecMemo : ParserM (τ := Unit) (tag := fun _ => UString) UChar Const UString := (memoize (τ := Unit) (α := UString) Counter.empty $ fun recur (_: Unit) =>
  concat (recur ()) (terminal "a") ⊔ terminal "a"
  ) ()

-- this still causes stack overflow because we don't have left recursion detection
-- #guard (runParser' leftRecMemo "aaa").1.toList == [(5, Const.some { down := "aaa" })]
