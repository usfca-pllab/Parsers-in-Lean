-- Some potential lemmas we can use to prove correctness theorems for the parser generator.

import ParserCombinators.Memoized

universe u v
variable {τ} { α β : Type u } {tag : τ → Type u} { μ : Type u → Type u } [Fintype τ] [BEq τ] [LawfulBEq τ] [Hashable τ] [DecidableEq τ] [Monad μ] [Traversable μ] [semilat_μ : SemilatticeAlt μ] [h_eq : ∀ t : τ, DecidableEq (tag t)]

axiom memoize_induction
  (g : ((t : τ) → ParserM (tag := tag) β μ (tag t)) → (t : τ) → ParserM (tag := tag) β μ (tag t))
  (p : ((t : τ) → ParserM (tag := tag) β μ (tag t)) → Prop)
  (h_failure : p (fun _ => ⊥))
  (h_induction : ∀ parser, p parser → p (g parser))
    : p (memoize Counter.empty g)


variable (parser₁ parser₂ : ParserM (tag := tag) β μ α) (input : Array β) [DecidableEq α]

axiom runParser_sup_eq_sup_runParser
  : ∀ start : ℕ, (runParser (parser₁ ⊔ parser₂) input start).1.EquivQuot ((runParser parser₁ input start).1 ⊔ (runParser parser₂ input start).1)

axiom runParser_map
  [DecidableEq α']
  (f : α → α')
  {start : ℕ}
  : (runParser (f <$> parser₁) input start).1.Equiv ((runParser parser₁ input start).1.map fun _ => Functor.map f)

omit [Fintype τ] in
lemma runParser_map_getElem?_eq
  [DecidableEq α']
  (f : α → α')
  {start : ℕ}
  (endPos : ℕ)
  : (runParser (f <$> parser₁) input start).1[endPos]? = ((runParser parser₁ input start).1.map fun _ => Functor.map f)[endPos]? := by
  apply Std.HashMap.Equiv.getElem?_eq
  apply runParser_map

axiom runParser_pure
  (a : α)
  (start n : ℕ)
  : (runParser (tag := tag) (pure a) input start).1[n]? = if n = start then some (pure (f := μ) a) else none

/-
-- The axiom below is incorrect
axiom mem_runParser_bind_iff_eq_bind_mem_runParser
  [DecidableEq α']
  (parser₂ : α → ParserM (tag := tag) β μ α')
  {start end_pos : ℕ}
  {r : μ α'}
    : ((runParser (parser₁ >>= parser₂) input start).1[end_pos]? = some r) ↔  -- would be "←"
  ∃ split : ℕ, ∃ s : μ α, (runParser parser₁ input start).1[split]? = some s ∧
    (s >>= (fun x => sequence (runParser (parser₂ x) input split).1[end_pos]?)) = r  -- would be "≤ r" instead of = r
-/

axiom mem_runParser_bind_iff_eq_bind_mem_runParser
  [DecidableEq α']
  (parser₁ : ParserM (tag := tag) β List α)
  (parser₂ : α → ParserM (tag := tag) β List α')
  {start end_pos : ℕ}
  {r : List α'}
  {x : α'}
    : ((runParser (parser₁ >>= parser₂) input start).1[end_pos]? = some r ∧ x ∈ r) ↔
  ∃ split : ℕ, ∃ s : List α, (runParser parser₁ input start).1[split]? = some s ∧
  x ∈ s >>= (fun x => (runParser (parser₂ x) input split).1[end_pos]?.toList.flatten)

omit [Fintype τ] in
theorem runParser_traverse_preserves_length (xs: List (ParserM (tag := tag) β List α))
  (start end_pos : ℕ)
  (result : List α)
  (h: result ∈ (runParser (List.traverse id xs) input start).1.getD end_pos [])
  : result.length = xs.length
  := by
  revert h
  rw [Std.HashMap.getD_eq_getD_getElem?]
  induction xs generalizing start end_pos result with
    | nil =>
      rw [List.traverse, runParser_pure]
      by_cases h : end_pos = start <;> simp [h]
    | cons head tail ih =>
      rw [List.traverse, seq_eq_bind]
      simp_all
      intro h
      have h_endPos_mem_resultMap : end_pos ∈ (runParser
            (head >>= fun a =>
              List.cons a <$> List.traverse id tail)
            input start).1 := by
        unfold Option.getD at h
        cases h_opt : (runParser
            (head >>= fun a =>
              List.cons a <$> List.traverse id tail)
          input start).1[end_pos]?
        · simp [h_opt] at h
        · have ⟨h_mem, h_opt⟩ := Std.HashMap.getElem?_eq_some_iff.mp h_opt
          exact h_mem
      rw [Std.HashMap.getElem?_eq_some_getElem h_endPos_mem_resultMap] at h
      simp at h

      let r := (runParser
        (head >>= fun a => List.cons a <$> List.traverse id tail)
        input start).1[end_pos]

      have h_split := by
        apply (mem_runParser_bind_iff_eq_bind_mem_runParser input head (fun (a : α) => List.cons a <$> List.traverse id tail) (x := result) (r := r) (start := start) (end_pos := end_pos)).mp (And.intro _ _)
        · apply Std.HashMap.getElem?_eq_some_getElem
        · exact h
      replace ⟨split, s, h_split, h_result⟩ := h_split
      simp [runParser_map_getElem?_eq] at h_result
      cases result with
      | nil =>
        simp at h_result
      | cons _ t_result =>
        simp
        apply ih split end_pos t_result
        simp at h_result
        replace ⟨_, _, results, h_result, h_t_result, _⟩ := h_result
        simp [h_result]
        exact h_t_result
