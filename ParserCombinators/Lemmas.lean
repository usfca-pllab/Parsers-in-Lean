-- Some potential lemmas we can use to prove correctness theorems for the parser generator.

import ParserCombinators.Memoized

universe u v
variable {τ} { α β : Type u } {tag : τ → Type u} { μ : Type u → Type u } [Fintype τ] [BEq τ] [LawfulBEq τ] [Hashable τ] [DecidableEq τ] [Monad μ] [Traversable μ] [semilat_μ : SemilatticeAlt μ] [h_eq : ∀ t : τ, DecidableEq (tag t)]

theorem memoize_counter_induction
  (g : ((t : τ) → ParserM (tag := tag) β μ (tag t)) →
      (t : τ) → ParserM (tag := tag) β μ (tag t))
  (P : (counter : Counter τ) →
      ((t : τ) → ParserM (tag := tag) β μ (tag t)) → Prop)
  (h_step :
    ∀ counter,
      (∀ t fuel,
        counter[t]? ≠ some 0 →
        P (counter.dec t fuel) (memoize (counter.dec t fuel) g)) →
      P counter (memoize counter g)) :
    P Counter.empty (memoize Counter.empty g) := by
  let Q (counter : Counter τ) : Prop := P counter (memoize counter g)
  have h_all : ∀ counter : Counter τ, Q counter := by
    intro counter
    refine (inferInstanceAs (WellFoundedRelation (Counter τ))).wf.induction
      (a := counter) ?_
    intro counter ih
    exact h_step counter (fun t fuel h_nonzero =>
      ih (counter.dec t fuel)
        (Counter.dec_lt_if_not_zero (m := counter) (t := t) (n := fuel)
          h_nonzero))
  exact h_all Counter.empty


variable (parser₁ parser₂ : ParserM (tag := tag) β μ α) (input : Array β) [DecidableEq α]


omit [Fintype τ] in
theorem runParser_fst_eq_lower
  (p : ParserM (tag := tag) β μ α) (input : Array β) (start : ℕ) :
    (runParser p input start).1 = ((p.lower start) startState input).1 := by
  unfold runParser MStateT.run
  rfl

set_option linter.unusedSectionVars false in
omit [Fintype τ] [BEq τ] [LawfulBEq τ] [Hashable τ] [DecidableEq τ]
  [Monad μ] [Traversable μ] [SemilatticeAlt μ]
  [∀ t : τ, DecidableEq (tag t)] [DecidableEq α] in
theorem resultMap_toList_value_split_witness
  (resultMap : ResultMap List α)
  {split : ℕ} {values : List α} {a : α}
  (h_get : resultMap[split]? = some values)
  (h_mem : a ∈ values) :
    ∃ prePairs postPairs preValues postValues,
      resultMap.toList = prePairs ++ (split, values) :: postPairs ∧
      values = preValues ++ a :: postValues := by
  have h_pair_mem : (split, values) ∈ resultMap.toList := by
    rw [Std.HashMap.mem_toList_iff_getElem?_eq_some]
    exact h_get
  obtain ⟨prePairs, postPairs, h_toList⟩ :=
    List.mem_iff_append.mp h_pair_mem
  obtain ⟨preValues, postValues, h_values⟩ :=
    List.mem_iff_append.mp h_mem
  exact ⟨prePairs, postPairs, preValues, postValues, h_toList, h_values⟩


omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_lower_return_iff
  (a x : α) (memo : MemoData tag List) (input : Array β) (start end_pos : ℕ) :
    x ∈ (((ParserM.Return (tag := tag) (β := β) (μ := List) a).lower start)
      memo input).1.getD end_pos [] ↔
      end_pos = start ∧ x = a := by
  unfold ParserM.lower
  rw [Std.HashMap.getD_eq_getD_getElem?]
  change x ∈ ((Std.HashMap.emptyWithCapacity.insert start [a] : Std.HashMap ℕ (List α))[end_pos]?).getD [] ↔
    end_pos = start ∧ x = a
  by_cases h : end_pos = start
  · subst end_pos
    simp
  · simp [h, Ne.symm h]

omit [Fintype τ] [DecidableEq τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ]
  [∀ t : τ, DecidableEq (tag t)] in
theorem hashMap_emptyWithCapacity_toList_eq_nil
  {κ : Type u} {δ : Type v} [BEq κ] [LawfulBEq κ] [Hashable κ] :
    (@Std.HashMap.emptyWithCapacity κ δ _ _).toList = [] := by
  apply List.isEmpty_iff.mp
  simp [Std.HashMap.isEmpty_emptyWithCapacity, Std.HashMap.isEmpty_toList]


omit [Fintype τ] [BEq τ] [LawfulBEq τ] [Hashable τ] [DecidableEq τ]
  [Monad μ] [Traversable μ] [SemilatticeAlt μ]
  [∀ t : τ, DecidableEq (tag t)] in
theorem readerT_pure_fst
  {ρ α β : Type u} (x : α) (y : β) (r : ρ) :
    (ReaderT.pure (ρ := ρ) (m := Id) (x, y) r).1 = x := by
  rfl

omit [Fintype τ] [BEq τ] [LawfulBEq τ] [Hashable τ] [DecidableEq τ]
  [Monad μ] [Traversable μ] [SemilatticeAlt μ]
  [∀ t : τ, DecidableEq (tag t)] in
theorem readerT_pure_snd
  {ρ α β : Type u} (x : α) (y : β) (r : ρ) :
    (ReaderT.pure (ρ := ρ) (m := Id) (x, y) r).2 = y := by
  rfl

omit [Fintype τ] [BEq τ] [LawfulBEq τ] [Hashable τ] [DecidableEq τ]
  [Monad μ] [Traversable μ] [SemilatticeAlt μ]
  [∀ t : τ, DecidableEq (tag t)] in
theorem hashMap_insert_emptyWithCapacity_toList_eq_singleton
  {κ : Type u} {δ : Type v}
  [BEq κ] [LawfulBEq κ] [Hashable κ] [EquivBEq κ] [LawfulHashable κ]
  (k : κ) (v : δ) :
    ((Std.HashMap.emptyWithCapacity : Std.HashMap κ δ).insert k v).toList = [(k, v)] := by
  let m : Std.HashMap κ δ := (Std.HashMap.emptyWithCapacity : Std.HashMap κ δ).insert k v
  have h_len : m.toList.length = 1 := by
    simp [m, Std.HashMap.length_toList, Std.HashMap.size_insert,
      Std.HashMap.size_emptyWithCapacity, Std.HashMap.mem_iff_contains,
      Std.HashMap.contains_emptyWithCapacity]
  have h_mem : (k, v) ∈ m.toList := by
    rw [Std.HashMap.mem_toList_iff_getElem?_eq_some]
    simp [m]
  obtain ⟨head, h_head⟩ := List.length_eq_one_iff.mp h_len
  simp [h_head] at h_mem
  subst head
  exact h_head

omit [Fintype τ] [BEq τ] [LawfulBEq τ] [Hashable τ] [DecidableEq τ]
  [Monad μ] [Traversable μ] [SemilatticeAlt μ]
  [∀ t : τ, DecidableEq (tag t)] in
theorem hashMap_singleton_toList_eq_singleton
  {κ : Type u} {δ : Type v}
  [BEq κ] [LawfulBEq κ] [Hashable κ] [EquivBEq κ] [LawfulHashable κ]
  (k : κ) (v : δ) :
    ({(k, v)} : Std.HashMap κ δ).toList = [(k, v)] := by
  change ((Std.HashMap.emptyWithCapacity : Std.HashMap κ δ).insert k v).toList = [(k, v)]
  exact hashMap_insert_emptyWithCapacity_toList_eq_singleton k v


omit [Fintype τ] [BEq τ] [LawfulBEq τ] [Hashable τ] [DecidableEq τ]
  [Monad μ] [Traversable μ] [SemilatticeAlt μ]
  [∀ t : τ, DecidableEq (tag t)] in
theorem traversable_foldl_cons
  {σ α : Type u} (f : σ → α → σ) (init : σ) (x : α) (xs : List α) :
    Traversable.foldl f init (x :: xs) =
      Traversable.foldl f (f init x) xs := by
  rfl

omit [Fintype τ] [BEq τ] [LawfulBEq τ] [Hashable τ] [DecidableEq τ]
  [Monad μ] [Traversable μ] [SemilatticeAlt μ]
  [∀ t : τ, DecidableEq (tag t)] in
theorem traversable_foldl_nil
  {σ α : Type u} (f : σ → α → σ) (init : σ) :
    Traversable.foldl f init ([] : List α) = init := by
  rfl

omit [Fintype τ] [BEq τ] [LawfulBEq τ] [Hashable τ] [DecidableEq τ]
  [Monad μ] [Traversable μ] [SemilatticeAlt μ]
  [∀ t : τ, DecidableEq (tag t)] in
theorem traversable_foldl_append
  {σ α : Type u} (f : σ → α → σ) (init : σ) (xs ys : List α) :
    Traversable.foldl f init (xs ++ ys) =
      Traversable.foldl f (Traversable.foldl f init xs) ys := by
  simpa only [Traversable.foldl_toList, Traversable.toList_eq_self] using
    (@List.foldl_append α σ f init xs ys)


set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem joinUnderCache_snd_eq
  [DecidableEq α]
  (s1 s2 : MStateT (MemoData tag List) (ReaderM (Array β)) (ResultMap List α))
  (memo : MemoData tag List) (input : Array β) :
    (joinUnderCache s1 s2 memo input).2 =
      let left := s1 memo input
      let right := s2 (↑left.2) input
      ⟨↑right.2,
        Preorder.le_trans memo (↑left.2) (↑right.2)
          left.2.property right.2.property⟩ := by
  unfold joinUnderCache liftA2
  simp only [ReaderT.instFunctorOfMonad, ReaderT.instApplicativeOfMonad,
    ReaderT.instMonad, Id.instMonad, Function.comp_apply]
  rfl

set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem joinUnderCache_snd_val_eq_of
  [DecidableEq α] [DecidableEq α']
  (acc act : MStateT (MemoData tag List) (ReaderM (Array β)) (ResultMap List α))
  (acc' act' : MStateT (MemoData tag List) (ReaderM (Array β)) (ResultMap List α'))
  (memo : MemoData tag List) (input : Array β)
  (h_acc : ∀ memo input, (acc memo input).2.val = (acc' memo input).2.val)
  (h_act : ∀ memo input, (act memo input).2.val = (act' memo input).2.val) :
    (joinUnderCache acc act memo input).2.val =
      (joinUnderCache acc' act' memo input).2.val := by
  rw [joinUnderCache_snd_eq (s1 := acc) (s2 := act),
    joinUnderCache_snd_eq (s1 := acc') (s2 := act')]
  change (act (↑((acc memo input).2)) input).2.val =
    (act' (↑((acc' memo input).2)) input).2.val
  rw [← h_acc memo input]
  exact h_act (↑((acc memo input).2)) input

set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem traversable_foldl_joinUnderCache_snd_val_eq_of_forall
  [DecidableEq α] [DecidableEq α']
  (actions : List (MStateT (MemoData tag List) (ReaderM (Array β)) (ResultMap List α)))
  (actions' : List (MStateT (MemoData tag List) (ReaderM (Array β)) (ResultMap List α')))
  (acc : MStateT (MemoData tag List) (ReaderM (Array β)) (ResultMap List α))
  (acc' : MStateT (MemoData tag List) (ReaderM (Array β)) (ResultMap List α'))
  (memo : MemoData tag List) (input : Array β)
  (h_acc : ∀ memo input, (acc memo input).2.val = (acc' memo input).2.val)
  (h_actions : List.Forall₂
    (fun action action' => ∀ memo input,
      (action memo input).2.val = (action' memo input).2.val)
    actions actions') :
    ((Traversable.foldl joinUnderCache acc actions) memo input).2.val =
      ((Traversable.foldl joinUnderCache acc' actions') memo input).2.val := by
  induction h_actions generalizing acc acc' with
  | nil =>
      simpa [traversable_foldl_nil] using h_acc memo input
  | cons h_head h_tail ih =>
      rw [traversable_foldl_cons, traversable_foldl_cons]
      exact ih
        (acc := joinUnderCache acc _)
        (acc' := joinUnderCache acc' _)
        (fun memo input => joinUnderCache_snd_val_eq_of
          (acc := acc) (act := _) (acc' := acc') (act' := _)
          (memo := memo) (input := input) h_acc h_head)

set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem list_foldl_traversable_joinUnderCache_snd_val_eq_of_forall
  [DecidableEq α] [DecidableEq α']
  (groups :
    List (List (MStateT (MemoData tag List) (ReaderM (Array β)) (ResultMap List α))))
  (groups' :
    List (List (MStateT (MemoData tag List) (ReaderM (Array β)) (ResultMap List α'))))
  (acc : MStateT (MemoData tag List) (ReaderM (Array β)) (ResultMap List α))
  (acc' : MStateT (MemoData tag List) (ReaderM (Array β)) (ResultMap List α'))
  (memo : MemoData tag List) (input : Array β)
  (h_acc : ∀ memo input, (acc memo input).2.val = (acc' memo input).2.val)
  (h_groups : List.Forall₂
    (List.Forall₂
      (fun action action' => ∀ memo input,
        (action memo input).2.val = (action' memo input).2.val))
    groups groups') :
    ((List.foldl (Traversable.foldl joinUnderCache) acc groups) memo input).2.val =
      ((List.foldl (Traversable.foldl joinUnderCache) acc' groups') memo input).2.val := by
  induction h_groups generalizing acc acc' with
  | nil =>
      simpa using h_acc memo input
  | cons h_head h_tail ih =>
      simp only [List.foldl_cons]
      exact ih
        (acc := Traversable.foldl joinUnderCache acc _)
        (acc' := Traversable.foldl joinUnderCache acc' _)
        (fun memo input => traversable_foldl_joinUnderCache_snd_val_eq_of_forall
          _ _ (acc := acc) (acc' := acc') (memo := memo) (input := input)
          h_acc h_head)

set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_joinUnderCache_left
  [DecidableEq α]
  (s1 s2 : MStateT (MemoData tag List) (ReaderM (Array β)) (ResultMap List α))
  (memo : MemoData tag List) (input : Array β)
  (end_pos : ℕ) (x : α)
  (h : x ∈ (s1 memo input).1.getD end_pos []) :
    x ∈ (joinUnderCache s1 s2 memo input).1.getD end_pos [] := by
  unfold joinUnderCache liftA2
  let left := s1 memo input
  let right := s2 (↑left.2) input
  change x ∈ (left.1.unionSup right.1).getD end_pos []
  by_cases h_left_key : end_pos ∈ left.1
  · by_cases h_right_key : end_pos ∈ right.1
    · have h_union := Std.HashMap.unionSup_getD_both
        (s := List.memSetoid α)
        (semi := List.instSemilatticeAlt.instSemilatticeoidInstSetoid)
        h_left_key h_right_key
      simp [List.memSetoid] at h_union
      apply h_union.2
      simp [Max.max, SemilatticeAlt.orElse]
      left
      simpa [left, Std.HashMap.getElem_eq_getD (fallback := [])] using h
    · have h_union := Std.HashMap.unionSup_getD_of_right_not_contains
        (s := List.memSetoid α)
        (semi := List.instSemilatticeAlt.instSemilatticeoidInstSetoid)
        (fallback := []) left.1 right.1 h_right_key
      simp [List.memSetoid] at h_union
      exact h_union.2 (by simpa [left] using h)
  · simp [left, Std.HashMap.getD_eq_fallback h_left_key] at h

set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_joinUnderCache_right
  [DecidableEq α]
  (s1 s2 : MStateT (MemoData tag List) (ReaderM (Array β)) (ResultMap List α))
  (memo : MemoData tag List) (input : Array β)
  (end_pos : ℕ) (x : α)
  (h : x ∈ (s2 (↑(s1 memo input).2) input).1.getD end_pos []) :
    x ∈ (joinUnderCache s1 s2 memo input).1.getD end_pos [] := by
  unfold joinUnderCache liftA2
  let left := s1 memo input
  let right := s2 (↑left.2) input
  change x ∈ (left.1.unionSup right.1).getD end_pos []
  by_cases h_left_key : end_pos ∈ left.1
  · by_cases h_right_key : end_pos ∈ right.1
    · have h_union := Std.HashMap.unionSup_getD_both
        (s := List.memSetoid α)
        (semi := List.instSemilatticeAlt.instSemilatticeoidInstSetoid)
        h_left_key h_right_key
      simp [List.memSetoid] at h_union
      apply h_union.2
      simp [Max.max, SemilatticeAlt.orElse]
      right
      simpa [right, left, Std.HashMap.getElem_eq_getD (fallback := [])] using h
    · simp [right, left, Std.HashMap.getD_eq_fallback h_right_key] at h
  · have h_union := Std.HashMap.unionSup_getD_of_not_contains
      (s := List.memSetoid α)
      (semi := List.instSemilatticeAlt.instSemilatticeoidInstSetoid)
      (fallback := []) left.1 right.1 h_left_key
    simp [List.memSetoid] at h_union
    exact h_union.2 (by simpa [right, left] using h)

set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_joinUnderCache_or
  [DecidableEq α]
  (s1 s2 : MStateT (MemoData tag List) (ReaderM (Array β)) (ResultMap List α))
  (memo : MemoData tag List) (input : Array β)
  (end_pos : ℕ) (x : α)
  (h : x ∈ (joinUnderCache s1 s2 memo input).1.getD end_pos []) :
    x ∈ (s1 memo input).1.getD end_pos [] ∨
    x ∈ (s2 (↑((s1 memo input).2)) input).1.getD end_pos [] := by
  unfold joinUnderCache liftA2 at h
  let left := s1 memo input
  let right := s2 (↑left.2) input
  change x ∈ (left.1.unionSup right.1).getD end_pos [] at h
  by_cases h_left_key : end_pos ∈ left.1
  · by_cases h_right_key : end_pos ∈ right.1
    · have h_union := Std.HashMap.unionSup_getD_both
        (s := List.memSetoid α)
        (semi := List.instSemilatticeAlt.instSemilatticeoidInstSetoid)
        h_left_key h_right_key
      simp [List.memSetoid] at h_union
      have h_mem := h_union.1 h
      simp [Max.max, SemilatticeAlt.orElse] at h_mem
      cases h_mem with
      | inl h_left =>
          left
          simpa [left, Std.HashMap.getElem_eq_getD (fallback := [])] using h_left
      | inr h_right =>
          right
          simpa [left, right, Std.HashMap.getElem_eq_getD (fallback := [])] using h_right
    · have h_union := Std.HashMap.unionSup_getD_of_right_not_contains
        (s := List.memSetoid α)
        (semi := List.instSemilatticeAlt.instSemilatticeoidInstSetoid)
        (fallback := []) left.1 right.1 h_right_key
      simp [List.memSetoid] at h_union
      left
      exact h_union.1 h
  · have h_union := Std.HashMap.unionSup_getD_of_not_contains
      (s := List.memSetoid α)
      (semi := List.instSemilatticeAlt.instSemilatticeoidInstSetoid)
      (fallback := []) left.1 right.1 h_left_key
    simp [List.memSetoid] at h_union
    right
    exact h_union.1 h

set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_traversable_foldl_joinUnderCache_of_acc
  [DecidableEq α]
  (actions : List (MStateT (MemoData tag List) (ReaderM (Array β)) (ResultMap List α)))
  (acc : MStateT (MemoData tag List) (ReaderM (Array β)) (ResultMap List α))
  (memo : MemoData tag List) (input : Array β)
  (end_pos : ℕ) (x : α)
  (h : x ∈ (acc memo input).1.getD end_pos []) :
    x ∈ ((Traversable.foldl joinUnderCache acc actions) memo input).1.getD end_pos [] := by
  rw [Traversable.foldl_toList, Traversable.toList_eq_self]
  exact List.foldlRecOn actions joinUnderCache h (by
    intro current h_current action _
    exact mem_joinUnderCache_left
      current action memo input end_pos x h_current)

set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_traversable_foldl_joinUnderCache_of_head
  [DecidableEq α]
  (action : MStateT (MemoData tag List) (ReaderM (Array β)) (ResultMap List α))
  (rest : List (MStateT (MemoData tag List) (ReaderM (Array β)) (ResultMap List α)))
  (acc : MStateT (MemoData tag List) (ReaderM (Array β)) (ResultMap List α))
  (memo : MemoData tag List) (input : Array β)
  (end_pos : ℕ) (x : α)
  (h : x ∈ (action (↑(acc memo input).2) input).1.getD end_pos []) :
    x ∈ ((Traversable.foldl joinUnderCache acc (action :: rest)) memo input).1.getD end_pos [] := by
  rw [traversable_foldl_cons]
  exact mem_traversable_foldl_joinUnderCache_of_acc rest (joinUnderCache acc action)
    memo input end_pos x
    (mem_joinUnderCache_right acc action memo input end_pos x h)

set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_traversable_foldl_joinUnderCache_of_split
  [DecidableEq α]
  (pre post : List (MStateT (MemoData tag List) (ReaderM (Array β)) (ResultMap List α)))
  (action : MStateT (MemoData tag List) (ReaderM (Array β)) (ResultMap List α))
  (acc : MStateT (MemoData tag List) (ReaderM (Array β)) (ResultMap List α))
  (memo : MemoData tag List) (input : Array β)
  (end_pos : ℕ) (x : α)
  (h : x ∈
    (action (↑((Traversable.foldl joinUnderCache acc pre) memo input).2) input).1.getD
      end_pos []) :
    x ∈ ((Traversable.foldl joinUnderCache acc (pre ++ action :: post)) memo input).1.getD
      end_pos [] := by
  rw [traversable_foldl_append]
  exact mem_traversable_foldl_joinUnderCache_of_head action post
    (Traversable.foldl joinUnderCache acc pre) memo input end_pos x h

set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_traversable_foldl_joinUnderCache_or_action
  [DecidableEq α]
  (actions : List (MStateT (MemoData tag List) (ReaderM (Array β)) (ResultMap List α)))
  (acc : MStateT (MemoData tag List) (ReaderM (Array β)) (ResultMap List α))
  (memo : MemoData tag List) (input : Array β)
  (end_pos : ℕ) (x : α)
  (h : x ∈ ((Traversable.foldl joinUnderCache acc actions) memo input).1.getD end_pos []) :
    x ∈ (acc memo input).1.getD end_pos [] ∨
    ∃ pre action post,
      actions = pre ++ action :: post ∧
      x ∈ (action (↑((Traversable.foldl joinUnderCache acc pre) memo input).2)
        input).1.getD end_pos [] := by
  induction actions generalizing acc memo with
  | nil =>
      simp [Traversable.foldl] at h
      exact Or.inl h
  | cons action rest ih =>
      rw [traversable_foldl_cons] at h
      have h_rest := ih (acc := joinUnderCache acc action) (memo := memo) h
      cases h_rest with
      | inl h_join =>
          have h_or := mem_joinUnderCache_or
            (tag := tag) (β := β)
            acc action memo input end_pos x h_join
          cases h_or with
          | inl h_acc =>
              exact Or.inl h_acc
          | inr h_action =>
              exact Or.inr ⟨[], action, rest, by simp, by simpa using h_action⟩
      | inr h_action_rest =>
          rcases h_action_rest with ⟨pre, action', post, h_eq, h_mem⟩
          refine Or.inr ⟨action :: pre, action', post, ?_, ?_⟩
          · simp [h_eq]
          · simpa [traversable_foldl_cons] using h_mem

set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_list_foldl_traversable_joinUnderCache_of_acc
  [DecidableEq α]
  (actionGroups : List (List (MStateT (MemoData tag List) (ReaderM (Array β)) (ResultMap List α))))
  (acc : MStateT (MemoData tag List) (ReaderM (Array β)) (ResultMap List α))
  (memo : MemoData tag List) (input : Array β)
  (end_pos : ℕ) (x : α)
  (h : x ∈ (acc memo input).1.getD end_pos []) :
    x ∈ ((List.foldl (Traversable.foldl joinUnderCache) acc actionGroups)
      memo input).1.getD end_pos [] := by
  exact List.foldlRecOn actionGroups
    (Traversable.foldl joinUnderCache) h (by
      intro current h_current actions _
      exact mem_traversable_foldl_joinUnderCache_of_acc
        actions current memo input end_pos x h_current)

set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_list_foldl_traversable_joinUnderCache_of_split
  [DecidableEq α]
  (pre post : List (List (MStateT (MemoData tag List) (ReaderM (Array β)) (ResultMap List α))))
  (group : List (MStateT (MemoData tag List) (ReaderM (Array β)) (ResultMap List α)))
  (acc : MStateT (MemoData tag List) (ReaderM (Array β)) (ResultMap List α))
  (memo : MemoData tag List) (input : Array β)
  (end_pos : ℕ) (x : α)
  (h : x ∈ ((Traversable.foldl joinUnderCache
      (List.foldl (Traversable.foldl joinUnderCache) acc pre) group)
      memo input).1.getD end_pos []) :
    x ∈ ((List.foldl (Traversable.foldl joinUnderCache) acc (pre ++ group :: post))
      memo input).1.getD end_pos [] := by
  rw [List.foldl_append]
  simp [List.foldl]
  exact mem_list_foldl_traversable_joinUnderCache_of_acc post
    (Traversable.foldl joinUnderCache
      (List.foldl (Traversable.foldl joinUnderCache) acc pre) group)
    memo input end_pos x h


set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_list_foldl_traversable_joinUnderCache_or_action
  [DecidableEq α]
  (actionGroups : List (List (MStateT (MemoData tag List) (ReaderM (Array β)) (ResultMap List α))))
  (acc : MStateT (MemoData tag List) (ReaderM (Array β)) (ResultMap List α))
  (memo : MemoData tag List) (input : Array β)
  (end_pos : ℕ) (x : α)
  (h : x ∈ ((List.foldl (Traversable.foldl joinUnderCache) acc actionGroups)
    memo input).1.getD end_pos []) :
    x ∈ (acc memo input).1.getD end_pos [] ∨
    ∃ preGroups preActions action postActions postGroups,
      actionGroups = preGroups ++ (preActions ++ action :: postActions) :: postGroups ∧
      x ∈ (action (↑((Traversable.foldl joinUnderCache
        (List.foldl (Traversable.foldl joinUnderCache) acc preGroups)
        preActions) memo input).2) input).1.getD end_pos [] := by
  induction actionGroups generalizing acc memo with
  | nil =>
      simp at h
      exact Or.inl h
  | cons group rest ih =>
      simp [List.foldl] at h
      have h_rest := ih
        (acc := Traversable.foldl joinUnderCache acc group)
        (memo := memo) h
      cases h_rest with
      | inl h_group =>
          have h_group_action := mem_traversable_foldl_joinUnderCache_or_action
            (tag := tag) (β := β)
            group acc memo input end_pos x h_group
          cases h_group_action with
          | inl h_acc =>
              exact Or.inl h_acc
          | inr h_action =>
              rcases h_action with ⟨preActions, action, postActions, h_group_eq, h_mem⟩
              refine Or.inr ⟨[], preActions, action, postActions, rest, ?_, ?_⟩
              · simp [h_group_eq]
              · simpa using h_mem
      | inr h_later =>
          rcases h_later with
            ⟨preGroups, preActions, action, postActions, postGroups, h_eq, h_mem⟩
          refine Or.inr
            ⟨group :: preGroups, preActions, action, postActions, postGroups, ?_, ?_⟩
          · simp [h_eq]
          · simpa [List.foldl] using h_mem

set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_traversable_foldl_lower_return_of_mem
  [DecidableEq α]
  (values : List α) (j : ℕ)
  (acc : MStateT (MemoData tag List) (ReaderM (Array β)) (ResultMap List α))
  (memo : MemoData tag List) (input : Array β)
  (x : α)
  (h : x ∈ values) :
    x ∈ (((Traversable.foldl joinUnderCache acc
      (List.map (fun a => (ParserM.Return (tag := tag) (β := β) (μ := List) a).lower j) values))
      memo input).1.getD j []) := by
  obtain ⟨pre, post, h_values⟩ := List.mem_iff_append.mp h
  subst h_values
  simp only [List.map_append, List.map_cons]
  apply mem_traversable_foldl_joinUnderCache_of_split
    (pre := ((fun a => (ParserM.Return (tag := tag) (β := β) (μ := List) a).lower j) <$> pre))
    (post := ((fun a => (ParserM.Return (tag := tag) (β := β) (μ := List) a).lower j) <$> post))
    (action := (ParserM.Return (tag := tag) (β := β) (μ := List) x).lower j)
    (acc := acc) (memo := memo) (input := input)
    (end_pos := j) (x := x)
  exact (mem_lower_return_iff (tag := tag) (β := β)
    (a := x) (x := x)
    (memo := ↑((Traversable.foldl joinUnderCache acc
      ((fun a => (ParserM.Return (tag := tag) (β := β) (μ := List) a).lower j) <$> pre))
      memo input).2)
    (input := input) (start := j) (end_pos := j)).mpr ⟨rfl, rfl⟩

set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_list_foldl_lower_returns_of_resultMap
  [DecidableEq α]
  (resultMap : Std.HashMap ℕ (List α))
  (acc : MStateT (MemoData tag List) (ReaderM (Array β)) (ResultMap List α))
  (memo : MemoData tag List) (input : Array β)
  (end_pos : ℕ) (x : α)
  (h : x ∈ resultMap.getD end_pos []) :
    x ∈ ((List.foldl (Traversable.foldl joinUnderCache) acc
      (List.map
        (fun pair : ℕ × List α =>
          match pair with
          | (j, values) =>
              List.map
                (fun a => (ParserM.Return (tag := tag) (β := β) (μ := List) a).lower j)
                values)
        resultMap.toList))
      memo input).1.getD end_pos [] := by
  let Action := MStateT (MemoData tag List) (ReaderM (Array β)) (ResultMap List α)
  let pairAction : ℕ × List α → List Action :=
    fun pair =>
      match pair with
      | (j, values) =>
          List.map
            (fun a => (ParserM.Return (tag := tag) (β := β) (μ := List) a).lower j)
            values
  change x ∈ ((List.foldl (Traversable.foldl joinUnderCache) acc
      (List.map pairAction resultMap.toList)) memo input).1.getD end_pos []
  rw [Std.HashMap.getD_eq_getD_getElem?] at h
  cases h_opt : resultMap[end_pos]? with
  | none =>
      simp [h_opt] at h
  | some values =>
      simp [h_opt] at h
      have h_pair_mem : (end_pos, values) ∈ resultMap.toList := by
        rw [Std.HashMap.mem_toList_iff_getElem?_eq_some]
        exact h_opt
      obtain ⟨pre, post, h_toList⟩ := List.mem_iff_append.mp h_pair_mem
      rw [h_toList]
      simp only [List.map_append, List.map_cons]
      apply mem_list_foldl_traversable_joinUnderCache_of_split
        (pre := List.map pairAction pre)
        (post := List.map pairAction post)
        (group := pairAction (end_pos, values))
        (acc := acc) (memo := memo) (input := input)
        (end_pos := end_pos) (x := x)
      simp [pairAction]
      exact mem_traversable_foldl_lower_return_of_mem values end_pos
        (List.foldl (Traversable.foldl joinUnderCache) acc (List.map pairAction pre))
        memo input x h

set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_bindContinue_return_of_mem
  [DecidableEq α]
  (resultMap : ResultMap List α)
  (memo : MemoData tag List) (input : Array β)
  (end_pos : ℕ) (x : α)
  (h : x ∈ resultMap.getD end_pos []) :
    x ∈ (Parser.bindContinue (tag := tag) (β := β)
      resultMap
      (fun a => (ParserM.Return (tag := tag) (β := β) (μ := List) a).lower)
      memo input).1.getD end_pos [] := by
  unfold Parser.bindContinue Parser.bindActions
  exact mem_list_foldl_lower_returns_of_resultMap (tag := tag) (β := β)
    (resultMap := resultMap)
    (acc := pure Std.HashMap.emptyWithCapacity)
    (memo := memo) (input := input)
    (end_pos := end_pos) (x := x) h

set_option linter.unusedSectionVars false in
omit α [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] [DecidableEq α] in
theorem mem_bindContinue_of_action_mem
  [DecidableEq α']
  {δ : Type u}
  (pivotToResult : ResultMap List δ)
  (f : δ → Parser (tag := tag) β List α')
  (prePairs postPairs : List (ℕ × List δ))
  (split : ℕ) (values preValues postValues : List δ) (a : δ)
  (memo : MemoData tag List) (input : Array β)
  (end_pos : ℕ) (x : α')
  (h_toList : pivotToResult.toList = prePairs ++ (split, values) :: postPairs)
  (h_values : values = preValues ++ a :: postValues)
  (h :
    x ∈ (f a split
      (↑((Traversable.foldl joinUnderCache
        (List.foldl (Traversable.foldl joinUnderCache)
          (pure Std.HashMap.emptyWithCapacity)
          (List.map
            (fun pair : ℕ × List δ =>
              match pair with
              | (j, values) => List.map (fun a => f a j) values)
            prePairs))
        (List.map (fun a => f a split) preValues))
        memo input).2)
      input).1.getD end_pos []) :
    x ∈ (Parser.bindContinue (tag := tag) (β := β)
      pivotToResult f memo input).1.getD end_pos [] := by
  unfold Parser.bindContinue Parser.bindActions
  let pairAction : ℕ × List δ →
      List (MStateT (MemoData tag List) (ReaderM (Array β)) (ResultMap List α')) :=
    fun pair =>
      match pair with
      | (j, values) => List.map (fun a => f a j) values
  change x ∈ ((List.foldl (Traversable.foldl joinUnderCache)
      (pure Std.HashMap.emptyWithCapacity)
      (List.map pairAction pivotToResult.toList)) memo input).1.getD end_pos []
  rw [h_toList]
  simp only [List.map_append, List.map_cons]
  apply mem_list_foldl_traversable_joinUnderCache_of_split
    (pre := List.map pairAction prePairs)
    (post := List.map pairAction postPairs)
    (group := pairAction (split, values))
    (acc := pure Std.HashMap.emptyWithCapacity)
    (memo := memo) (input := input) (end_pos := end_pos) (x := x)
  simp [pairAction, h_values]
  apply mem_traversable_foldl_joinUnderCache_of_split
    (pre := List.map (fun a => f a split) preValues)
    (post := List.map (fun a => f a split) postValues)
    (action := f a split)
    (acc := List.foldl (Traversable.foldl joinUnderCache)
      (pure Std.HashMap.emptyWithCapacity)
      (List.map pairAction prePairs))
    (memo := memo) (input := input) (end_pos := end_pos) (x := x)
  simpa [pairAction] using h

set_option linter.unusedSectionVars false in
omit α [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] [DecidableEq α] in
theorem mem_bindContinue_exists_action
  [DecidableEq α']
  {δ : Type u}
  (pivotToResult : ResultMap List δ)
  (f : δ → Parser (tag := tag) β List α')
  (memo : MemoData tag List) (input : Array β)
  (end_pos : ℕ) (x : α')
  (h :
    x ∈ (Parser.bindContinue (tag := tag) (β := β)
      pivotToResult f memo input).1.getD end_pos []) :
    ∃ preGroups preActions action postActions postGroups,
      Parser.bindActions (tag := tag) (β := β) pivotToResult f =
        preGroups ++ (preActions ++ action :: postActions) :: postGroups ∧
      x ∈ (action (↑((Traversable.foldl joinUnderCache
        (List.foldl (Traversable.foldl joinUnderCache)
          (pure Std.HashMap.emptyWithCapacity)
          preGroups)
        preActions) memo input).2) input).1.getD end_pos [] := by
  unfold Parser.bindContinue at h
  have h_action := mem_list_foldl_traversable_joinUnderCache_or_action
    (tag := tag) (β := β)
    (actionGroups := Parser.bindActions (tag := tag) (β := β) pivotToResult f)
    (acc := pure Std.HashMap.emptyWithCapacity)
    (memo := memo) (input := input) (end_pos := end_pos) (x := x) h
  cases h_action with
  | inl h_empty =>
      change x ∈ (Std.HashMap.emptyWithCapacity : ResultMap List α').getD end_pos [] at h_empty
      simp at h_empty
  | inr h_action =>
      exact h_action

set_option linter.unusedSectionVars false in
omit α [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] [DecidableEq α] in
theorem bindActions_action_origin
  [DecidableEq α']
  {δ : Type u}
  (pivotToResult : ResultMap List δ)
  (f : δ → Parser (tag := tag) β List α')
  (preGroups postGroups : List (List (MStateT (MemoData tag List) (ReaderM (Array β)) (ResultMap List α'))))
  (preActions postActions : List (MStateT (MemoData tag List) (ReaderM (Array β)) (ResultMap List α')))
  (action : MStateT (MemoData tag List) (ReaderM (Array β)) (ResultMap List α'))
  (h_eq :
    Parser.bindActions (tag := tag) (β := β) pivotToResult f =
      preGroups ++ (preActions ++ action :: postActions) :: postGroups) :
    ∃ split values a,
      pivotToResult[split]? = some values ∧
      a ∈ values ∧
      action = f a split := by
  have h_group_mem :
      preActions ++ action :: postActions ∈
        Parser.bindActions (tag := tag) (β := β) pivotToResult f := by
    rw [h_eq]
    simp
  unfold Parser.bindActions at h_group_mem
  obtain ⟨pair, h_pair_mem, h_pair_eq⟩ := List.mem_map.mp h_group_mem
  rcases pair with ⟨split, values⟩
  have h_get : pivotToResult[split]? = some values := by
    rw [Std.HashMap.mem_toList_iff_getElem?_eq_some] at h_pair_mem
    exact h_pair_mem
  have h_action_mem : action ∈ List.map (fun a => f a split) values := by
    have h_mem : action ∈ preActions ++ action :: postActions := by simp
    rw [← h_pair_eq] at h_mem
    exact h_mem
  obtain ⟨a, h_a_mem, h_action_eq⟩ := List.mem_map.mp h_action_mem
  exact ⟨split, values, a, h_get, h_a_mem, h_action_eq.symm⟩

set_option linter.unusedSectionVars false in
omit α [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] [DecidableEq α] in
theorem bindActions_action_split_origin
  [DecidableEq α']
  {δ : Type u}
  (pivotToResult : ResultMap List δ)
  (f : δ → Parser (tag := tag) β List α')
  (preGroups postGroups : List (List (MStateT (MemoData tag List) (ReaderM (Array β)) (ResultMap List α'))))
  (preActions postActions : List (MStateT (MemoData tag List) (ReaderM (Array β)) (ResultMap List α')))
  (action : MStateT (MemoData tag List) (ReaderM (Array β)) (ResultMap List α'))
  (h_eq :
    Parser.bindActions (tag := tag) (β := β) pivotToResult f =
      preGroups ++ (preActions ++ action :: postActions) :: postGroups) :
    ∃ prePairs postPairs split values preValues postValues a,
      pivotToResult.toList = prePairs ++ (split, values) :: postPairs ∧
      values = preValues ++ a :: postValues ∧
      preGroups =
        List.map
          (fun pair : ℕ × List δ =>
            match pair with
            | (j, values) => List.map (fun a => f a j) values)
          prePairs ∧
      preActions = List.map (fun a => f a split) preValues ∧
      action = f a split := by
  unfold Parser.bindActions at h_eq
  let pairAction : ℕ × List δ →
      List (MStateT (MemoData tag List) (ReaderM (Array β)) (ResultMap List α')) :=
    fun pair =>
      match pair with
      | (j, values) => List.map (fun a => f a j) values
  change List.map pairAction pivotToResult.toList =
      preGroups ++ (preActions ++ action :: postActions) :: postGroups at h_eq
  obtain ⟨prePairs, restPairs, h_toList, h_preGroups, h_rest⟩ :=
    (List.map_eq_append_iff.mp h_eq)
  cases restPairs with
  | nil =>
      simp at h_rest
  | cons pair postPairs =>
      rcases pair with ⟨split, values⟩
      simp only [List.map_cons, List.cons.injEq] at h_rest
      rcases h_rest with ⟨h_group, _h_postGroups⟩
      change List.map (fun a => f a split) values =
        preActions ++ action :: postActions at h_group
      obtain ⟨preValues, restValues, h_values, h_preActions, h_restValues⟩ :=
        (List.map_eq_append_iff.mp h_group)
      cases restValues with
      | nil =>
          simp at h_restValues
      | cons a postValues =>
          simp only [List.map_cons, List.cons.injEq] at h_restValues
          rcases h_restValues with ⟨h_action, _h_postActions⟩
          refine ⟨prePairs, postPairs, split, values, preValues, postValues, a,
            ?_, ?_, ?_, ?_, ?_⟩
          · simp [h_toList]
          · simp [h_values]
          · exact h_preGroups.symm
          · exact h_preActions.symm
          · exact h_action.symm

set_option linter.unusedSectionVars false in
omit α [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] [DecidableEq α] in
theorem mem_bindContinue_exists_getElem_action_mem
  [DecidableEq α']
  {δ : Type u}
  (pivotToResult : ResultMap List δ)
  (f : δ → Parser (tag := tag) β List α')
  (memo : MemoData tag List) (input : Array β)
  (end_pos : ℕ) (x : α')
  (h :
    x ∈ (Parser.bindContinue (tag := tag) (β := β)
      pivotToResult f memo input).1.getD end_pos []) :
    ∃ split values a preGroups preActions postActions postGroups,
      pivotToResult[split]? = some values ∧
      a ∈ values ∧
      Parser.bindActions (tag := tag) (β := β) pivotToResult f =
        preGroups ++ (preActions ++ f a split :: postActions) :: postGroups ∧
      x ∈ ((f a split)
        (↑((Traversable.foldl joinUnderCache
          (List.foldl (Traversable.foldl joinUnderCache)
            (pure Std.HashMap.emptyWithCapacity)
            preGroups)
          preActions) memo input).2)
        input).1.getD end_pos [] := by
  obtain ⟨preGroups, preActions, action, postActions, postGroups,
    h_actions, h_action_mem⟩ :=
    mem_bindContinue_exists_action
      (tag := tag) (β := β)
      (pivotToResult := pivotToResult) (f := f)
      (memo := memo) (input := input) (end_pos := end_pos) (x := x) h
  obtain ⟨split, values, a, h_get, h_a_mem, h_action_eq⟩ :=
    bindActions_action_origin
      (tag := tag) (β := β)
      (pivotToResult := pivotToResult) (f := f)
      (preGroups := preGroups) (postGroups := postGroups)
      (preActions := preActions) (postActions := postActions)
      (action := action) h_actions
  cases h_action_eq
  exact ⟨split, values, a, preGroups, preActions, postActions, postGroups,
    h_get, h_a_mem, h_actions, h_action_mem⟩

set_option linter.unusedSectionVars false in
omit α [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] [DecidableEq α] in
theorem bindActions_forall₂_snd_val_eq
  [DecidableEq α'] [DecidableEq α'']
  {δ : Type u}
  (pivotToResult : ResultMap List δ)
  (f : δ → Parser (tag := tag) β List α')
  (g : δ → Parser (tag := tag) β List α'')
  (h : ∀ a start memo input,
    (f a start memo input).2.val = (g a start memo input).2.val) :
    List.Forall₂
      (List.Forall₂
        (fun action action' => ∀ memo input,
          (action memo input).2.val = (action' memo input).2.val))
      (Parser.bindActions (tag := tag) (β := β) pivotToResult f)
      (Parser.bindActions (tag := tag) (β := β) pivotToResult g) := by
  unfold Parser.bindActions
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff,
    List.forall₂_same]
  rintro ⟨split, values⟩ _
  change List.Forall₂ _ (values.map fun a => f a split)
    (values.map fun a => g a split)
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff,
    List.forall₂_same]
  exact fun a _ => h a split

set_option linter.unusedSectionVars false in
omit α [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] [DecidableEq α] in
theorem bindContinue_snd_val_eq_of_forall
  [DecidableEq α'] [DecidableEq α'']
  {δ : Type u}
  (pivotToResult : ResultMap List δ)
  (f : δ → Parser (tag := tag) β List α')
  (g : δ → Parser (tag := tag) β List α'')
  (memo : MemoData tag List) (input : Array β)
  (h : ∀ a start memo input,
    (f a start memo input).2.val = (g a start memo input).2.val) :
    (Parser.bindContinue (tag := tag) (β := β) pivotToResult f memo input).2.val =
      (Parser.bindContinue (tag := tag) (β := β) pivotToResult g memo input).2.val := by
  unfold Parser.bindContinue
  apply list_foldl_traversable_joinUnderCache_snd_val_eq_of_forall
  · intro memo input
    rfl
  · exact bindActions_forall₂_snd_val_eq
      (tag := tag) (β := β)
      (pivotToResult := pivotToResult) (f := f) (g := g) h

set_option linter.unusedSectionVars false in
omit α [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] [DecidableEq α] in
theorem bindActionPrefix_snd_val_eq_of_forall
  [DecidableEq α'] [DecidableEq α'']
  {δ : Type u}
  (k : δ → ParserM (tag := tag) β List α')
  (g : δ → ParserM (tag := tag) β List α'')
  (prePairs : List (ℕ × List δ))
  (preValues : List δ)
  (split : ℕ)
  (memo : MemoData tag List) (input : Array β)
  (h : ∀ a start memo input,
    (((k a).lower start) memo input).2.val =
      (((g a).lower start) memo input).2.val) :
    ((Traversable.foldl joinUnderCache
      (List.foldl (Traversable.foldl joinUnderCache)
        (pure Std.HashMap.emptyWithCapacity)
        (List.map
          (fun pair : ℕ × List δ =>
            match pair with
            | (j, values) => List.map (fun a => (k a).lower j) values)
          prePairs))
      (List.map (fun a => (k a).lower split) preValues))
      memo input).2.val =
    ((Traversable.foldl joinUnderCache
      (List.foldl (Traversable.foldl joinUnderCache)
        (pure Std.HashMap.emptyWithCapacity)
        (List.map
          (fun pair : ℕ × List δ =>
            match pair with
            | (j, values) => List.map (fun a => (g a).lower j) values)
          prePairs))
      (List.map (fun a => (g a).lower split) preValues))
      memo input).2.val := by
  apply traversable_foldl_joinUnderCache_snd_val_eq_of_forall
  · intro memo input
    apply list_foldl_traversable_joinUnderCache_snd_val_eq_of_forall
    · intro memo input
      rfl
    · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff,
        List.forall₂_same]
      rintro ⟨j, values⟩ _
      change List.Forall₂ _ (values.map fun a => (k a).lower j)
        (values.map fun a => (g a).lower j)
      rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff,
        List.forall₂_same]
      exact fun a _ => h a j
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff,
      List.forall₂_same]
    exact fun a _ => h a split

set_option linter.unusedSectionVars false in
omit α [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] [DecidableEq α] in
theorem parser_bind_fst_eq_bindContinue
  [DecidableEq α']
  {δ : Type u}
  (p : Parser (tag := tag) β List δ)
  (f : δ → Parser (tag := tag) β List α')
  (memo : MemoData tag List) (input : Array β)
  (start : ℕ) :
    ((Parser.bind p f start) memo input).1 =
      (Parser.bindContinue (tag := tag) (β := β)
        ((p start) memo input).1 f
        (↑((p start) memo input).2) input).1 := by
  unfold Parser.bind
  rfl

set_option linter.unusedSectionVars false in
omit α [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] [DecidableEq α] in
theorem parser_bind_snd_val_eq_bindRun
  [DecidableEq α']
  {δ : Type u}
  (p : Parser (tag := tag) β List δ)
  (f : δ → Parser (tag := tag) β List α')
  (memo : MemoData tag List) (input : Array β)
  (start : ℕ) :
    ((Parser.bind p f start) memo input).2.val =
      (Parser.bindRun (tag := tag) (β := β) p f start memo input).2 := by
  rfl

set_option linter.unusedSectionVars false in
omit α [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] [DecidableEq α] in
theorem bindRun_snd_eq_bindContinue
  [DecidableEq α']
  {δ : Type u}
  (p : Parser (tag := tag) β List δ)
  (f : δ → Parser (tag := tag) β List α')
  (memo : MemoData tag List) (input : Array β)
  (start : ℕ) :
    (Parser.bindRun (tag := tag) (β := β) p f start memo input).2 =
      (Parser.bindContinue (tag := tag) (β := β)
        ((p start) memo input).1 f
        (↑((p start) memo input).2) input).2.val := by
  unfold Parser.bindRun
  rfl

set_option linter.unusedSectionVars false in
omit α [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] [DecidableEq α] in
theorem parser_bind_snd_val_eq_of_forall
  [DecidableEq α'] [DecidableEq α'']
  {δ : Type u}
  (p : Parser (tag := tag) β List δ)
  (f : δ → Parser (tag := tag) β List α')
  (g : δ → Parser (tag := tag) β List α'')
  (memo : MemoData tag List) (input : Array β)
  (start : ℕ)
  (h : ∀ a start memo input,
    (f a start memo input).2.val = (g a start memo input).2.val) :
    ((Parser.bind p f start) memo input).2.val =
      ((Parser.bind p g start) memo input).2.val := by
  rw [parser_bind_snd_val_eq_bindRun (tag := tag) (β := β)
    (p := p) (f := f) (memo := memo) (input := input) (start := start)]
  rw [parser_bind_snd_val_eq_bindRun (tag := tag) (β := β)
    (p := p) (f := g) (memo := memo) (input := input) (start := start)]
  rw [bindRun_snd_eq_bindContinue (tag := tag) (β := β)
    (p := p) (f := f) (memo := memo) (input := input) (start := start)]
  rw [bindRun_snd_eq_bindContinue (tag := tag) (β := β)
    (p := p) (f := g) (memo := memo) (input := input) (start := start)]
  exact bindContinue_snd_val_eq_of_forall
    (tag := tag) (β := β)
    (pivotToResult := ((p start) memo input).1)
    (f := f) (g := g)
    (memo := ↑((p start) memo input).2)
    (input := input) h

set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem lower_map_snd_val_eq
  [DecidableEq α] [DecidableEq α']
  (p : ParserM (tag := tag) β List α)
  (f : α → α')
  (memo : MemoData tag List) (input : Array β)
  (start : ℕ) :
    (((f <$> p).lower start) memo input).2.val =
      ((p.lower start) memo input).2.val := by
  induction p generalizing memo start input with
  | Return a =>
      rfl
  | Bind p k ih =>
      change ((Parser.bind p (fun a => ((f <$> k a).lower)) start) memo input).2.val =
        ((Parser.bind p (fun a => ((k a).lower)) start) memo input).2.val
      exact parser_bind_snd_val_eq_of_forall
        (tag := tag) (β := β)
        (p := p)
        (f := fun a => ((f <$> k a).lower))
        (g := fun a => ((k a).lower))
        (memo := memo) (input := input) (start := start)
        (by
          intro a start memo input
          exact ih a memo input start)

set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem lower_return_snd_val_eq
  [DecidableEq α]
  (a : α) (memo : MemoData tag List) (input : Array β)
  (start : ℕ) :
    (((ParserM.Return (tag := tag) (β := β) (μ := List) a).lower start)
      memo input).2.val = memo := by
  rfl

set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem traversable_foldl_joinUnderCache_snd_val_eq_self
  [DecidableEq α]
  (actions :
    List (MStateT (MemoData tag List) (ReaderM (Array β))
      (ResultMap List α)))
  (acc :
    MStateT (MemoData tag List) (ReaderM (Array β))
      (ResultMap List α))
  (memo : MemoData tag List) (input : Array β)
  (h_acc : ∀ memo input, (acc memo input).2.val = memo)
  (h_actions :
    ∀ action ∈ actions, ∀ memo input, (action memo input).2.val = memo) :
    ((Traversable.foldl joinUnderCache acc actions) memo input).2.val =
      memo := by
  rw [Traversable.foldl_toList, Traversable.toList_eq_self]
  exact (List.foldlRecOn
    (motive := fun current =>
      ∀ memo input, (current memo input).2.val = memo)
    actions joinUnderCache h_acc (by
      intro current h_current action h_action memo input
      rw [joinUnderCache_snd_eq]
      change (action (↑((current memo input).2)) input).2.val = memo
      rw [h_actions action h_action (↑((current memo input).2)) input]
      exact h_current memo input)) memo input

set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem list_foldl_traversable_joinUnderCache_snd_val_eq_self
  [DecidableEq α]
  (groups :
    List (List (MStateT (MemoData tag List) (ReaderM (Array β))
      (ResultMap List α))))
  (acc :
    MStateT (MemoData tag List) (ReaderM (Array β))
      (ResultMap List α))
  (memo : MemoData tag List) (input : Array β)
  (h_acc : ∀ memo input, (acc memo input).2.val = memo)
  (h_groups :
    ∀ group ∈ groups, ∀ action ∈ group,
      ∀ memo input, (action memo input).2.val = memo) :
    ((List.foldl (Traversable.foldl joinUnderCache) acc groups)
      memo input).2.val = memo := by
  exact (List.foldlRecOn
    (motive := fun current =>
      ∀ memo input, (current memo input).2.val = memo)
    groups (Traversable.foldl joinUnderCache) h_acc (by
      intro current h_current group h_group memo input
      exact traversable_foldl_joinUnderCache_snd_val_eq_self
        (tag := tag) (β := β)
        (actions := group) (acc := current)
        (memo := memo) (input := input)
        h_current (h_groups group h_group))) memo input

set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem bindContinue_return_snd_val_eq
  [DecidableEq α]
  (resultMap : ResultMap List α)
  (memo : MemoData tag List) (input : Array β) :
    (Parser.bindContinue (tag := tag) (β := β)
      resultMap
      (fun a => (ParserM.Return (tag := tag) (β := β) (μ := List) a).lower)
      memo input).2.val = memo := by
  unfold Parser.bindContinue Parser.bindActions
  exact list_foldl_traversable_joinUnderCache_snd_val_eq_self
    (tag := tag) (β := β)
    (groups :=
      resultMap.toList.map
        (fun x =>
          (fun a => (ParserM.Return (tag := tag) (β := β) (μ := List) a).lower x.1)
            <$> x.2))
    (acc := pure Std.HashMap.emptyWithCapacity)
    (memo := memo) (input := input)
    (by intro memo input; rfl)
    (by
      intro group h_group action h_action memo input
      rw [List.mem_map] at h_group
      rcases h_group with ⟨pair, _h_pair, rfl⟩
      rcases pair with ⟨j, values⟩
      simp at h_action
      rcases h_action with ⟨a, _h_a, rfl⟩
      exact lower_return_snd_val_eq
        (tag := tag) (β := β)
        (a := a) (memo := memo) (input := input) (start := j))

set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem lower_lift_snd_val_eq
  [DecidableEq α]
  (p : Parser (tag := tag) β List α)
  (memo : MemoData tag List) (input : Array β)
  (start : ℕ) :
    (((ParserM.lift p).lower start) memo input).2.val =
      ((p start) memo input).2.val := by
  unfold ParserM.lift ParserM.lower
  rw [parser_bind_snd_val_eq_bindRun
    (tag := tag) (β := β)
    (p := p)
    (f := fun a =>
      (ParserM.Return (tag := tag) (β := β) (μ := List) a).lower)
    (memo := memo) (input := input) (start := start)]
  rw [bindRun_snd_eq_bindContinue
    (tag := tag) (β := β)
    (p := p)
    (f := fun a =>
      (ParserM.Return (tag := tag) (β := β) (μ := List) a).lower)
    (memo := memo) (input := input) (start := start)]
  exact bindContinue_return_snd_val_eq
    (tag := tag) (β := β)
    (resultMap := ((p start) memo input).1)
    (memo := ↑((p start) memo input).2)
    (input := input)

set_option linter.unusedSectionVars false in
omit α [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] [DecidableEq α] in
theorem mem_lower_bind_of_action_mem
  [DecidableEq α']
  {δ : Type u}
  (p : Parser (tag := tag) β List δ)
  (k : δ → ParserM (tag := tag) β List α')
  (prePairs postPairs : List (ℕ × List δ))
  (split : ℕ) (values preValues postValues : List δ) (a : δ)
  (memo : MemoData tag List) (input : Array β)
  (start end_pos : ℕ) (x : α')
  (h_toList : ((p start) memo input).1.toList =
      prePairs ++ (split, values) :: postPairs)
  (h_values : values = preValues ++ a :: postValues)
  (h :
    x ∈ ((k a).lower split
      (↑((Traversable.foldl joinUnderCache
        (List.foldl (Traversable.foldl joinUnderCache)
          (pure Std.HashMap.emptyWithCapacity)
          (List.map
            (fun pair : ℕ × List δ =>
              match pair with
              | (j, values) => List.map (fun a => (k a).lower j) values)
            prePairs))
        (List.map (fun a => (k a).lower split) preValues))
        (↑((p start) memo input).2) input).2)
      input).1.getD end_pos []) :
    x ∈ (((ParserM.Bind p k).lower start) memo input).1.getD end_pos [] := by
  change x ∈ ((Parser.bind p (fun a => (k a).lower) start) memo input).1.getD end_pos []
  rw [parser_bind_fst_eq_bindContinue]
  exact mem_bindContinue_of_action_mem
    (tag := tag) (β := β)
    (pivotToResult := ((p start) memo input).1)
    (f := fun a => (k a).lower)
    (prePairs := prePairs) (postPairs := postPairs)
    (split := split) (values := values)
    (preValues := preValues) (postValues := postValues)
    (a := a)
    (memo := ↑((p start) memo input).2)
    (input := input) (end_pos := end_pos) (x := x)
    h_toList h_values h


set_option linter.unusedSectionVars false in
omit α [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] [DecidableEq α] in
theorem mem_lower_bind_of_getElem_action_mem
  [DecidableEq α']
  {δ : Type u}
  (p : Parser (tag := tag) β List δ)
  (k : δ → ParserM (tag := tag) β List α')
  (split : ℕ) (values : List δ) (a : δ)
  (memo : MemoData tag List) (input : Array β)
  (start end_pos : ℕ) (x : α')
  (h_get : ((p start) memo input).1[split]? = some values)
  (h_value : a ∈ values)
  (h_action :
    ∀ prePairs postPairs preValues postValues,
      ((p start) memo input).1.toList =
        prePairs ++ (split, values) :: postPairs →
      values = preValues ++ a :: postValues →
      x ∈ ((k a).lower split
        (↑((Traversable.foldl joinUnderCache
          (List.foldl (Traversable.foldl joinUnderCache)
            (pure Std.HashMap.emptyWithCapacity)
            (List.map
              (fun pair : ℕ × List δ =>
                match pair with
                | (j, values) => List.map (fun a => (k a).lower j) values)
              prePairs))
          (List.map (fun a => (k a).lower split) preValues))
          (↑((p start) memo input).2) input).2)
        input).1.getD end_pos []) :
    x ∈ (((ParserM.Bind p k).lower start) memo input).1.getD end_pos [] := by
  obtain ⟨prePairs, postPairs, preValues, postValues, h_toList, h_values⟩ :=
    resultMap_toList_value_split_witness
      (((p start) memo input).1) h_get h_value
  exact mem_lower_bind_of_action_mem
    (tag := tag) (β := β) (p := p) (k := k)
    (prePairs := prePairs) (postPairs := postPairs)
    (split := split) (values := values)
    (preValues := preValues) (postValues := postValues)
    (a := a) (memo := memo) (input := input) (start := start)
    (end_pos := end_pos) (x := x)
    h_toList h_values
    (h_action prePairs postPairs preValues postValues h_toList h_values)

set_option linter.unusedSectionVars false in
omit α [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] [DecidableEq α] in
theorem mem_lower_bind_exists_getElem_action_mem
  [DecidableEq α']
  {δ : Type u}
  (p : Parser (tag := tag) β List δ)
  (k : δ → ParserM (tag := tag) β List α')
  (memo : MemoData tag List) (input : Array β)
  (start end_pos : ℕ) (x : α')
  (h :
    x ∈ (((ParserM.Bind p k).lower start) memo input).1.getD end_pos []) :
    ∃ split values a preGroups preActions postActions postGroups,
      ((p start) memo input).1[split]? = some values ∧
      a ∈ values ∧
      Parser.bindActions (tag := tag) (β := β)
        ((p start) memo input).1
        (fun a => (k a).lower) =
        preGroups ++ (preActions ++ (k a).lower split :: postActions) :: postGroups ∧
      x ∈ (((k a).lower split)
        (↑((Traversable.foldl joinUnderCache
          (List.foldl (Traversable.foldl joinUnderCache)
            (pure Std.HashMap.emptyWithCapacity)
            preGroups)
          preActions)
          (↑((p start) memo input).2) input).2)
        input).1.getD end_pos [] := by
  change x ∈ ((Parser.bind p (fun a => (k a).lower) start) memo input).1.getD end_pos [] at h
  rw [parser_bind_fst_eq_bindContinue] at h
  exact mem_bindContinue_exists_getElem_action_mem
    (tag := tag) (β := β)
    (pivotToResult := ((p start) memo input).1)
    (f := fun a => (k a).lower)
    (memo := ↑((p start) memo input).2)
    (input := input) (end_pos := end_pos) (x := x) h

set_option maxHeartbeats 1000000 in
set_option linter.unusedSectionVars false in
omit α [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] [DecidableEq α] in
theorem mem_lower_bind_exists_action_split_mem
  [DecidableEq α']
  {δ : Type u}
  (p : Parser (tag := tag) β List δ)
  (k : δ → ParserM (tag := tag) β List α')
  (memo : MemoData tag List) (input : Array β)
  (start end_pos : ℕ) (x : α')
  (h :
    x ∈ (((ParserM.Bind p k).lower start) memo input).1.getD end_pos []) :
    ∃ prePairs postPairs split values preValues postValues a,
      ((p start) memo input).1.toList =
        prePairs ++ (split, values) :: postPairs ∧
      values = preValues ++ a :: postValues ∧
      x ∈ (((k a).lower split)
        (↑((Traversable.foldl joinUnderCache
          (List.foldl (Traversable.foldl joinUnderCache)
            (pure Std.HashMap.emptyWithCapacity)
            (List.map
              (fun pair : ℕ × List δ =>
                match pair with
                | (j, values) => List.map (fun a => (k a).lower j) values)
              prePairs))
          (List.map (fun a => (k a).lower split) preValues))
          (↑((p start) memo input).2) input).2)
        input).1.getD end_pos [] := by
  obtain ⟨split₀, _values₀, a₀, preGroups, preActions,
    postActions, postGroups, _h_get₀, _h_value₀, h_actions, h_action⟩ :=
    mem_lower_bind_exists_getElem_action_mem
      (tag := tag) (β := β)
      (p := p) (k := k)
      (memo := memo) (input := input)
      (start := start) (end_pos := end_pos)
      (x := x) h
  obtain ⟨prePairs, postPairs, split, values, preValues, postValues, a,
    h_toList, h_values, h_preGroups, h_preActions, h_action_eq⟩ :=
    bindActions_action_split_origin
      (tag := tag) (β := β)
      (pivotToResult := ((p start) memo input).1)
      (f := fun a => (k a).lower)
      (preGroups := preGroups) (postGroups := postGroups)
      (preActions := preActions) (postActions := postActions)
      (action := (k a₀).lower split₀) h_actions
  rw [h_action_eq, h_preGroups, h_preActions] at h_action
  exact ⟨prePairs, postPairs, split, values, preValues, postValues, a,
    h_toList, h_values, h_action⟩


set_option maxHeartbeats 1000000 in
set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_lower_map_of_mem
  [DecidableEq α] [DecidableEq α']
  (p : ParserM (tag := tag) β List α)
  (f : α → α')
  (memo : MemoData tag List) (input : Array β)
  (start end_pos : ℕ) (x : α)
  (h : x ∈ ((p.lower start) memo input).1.getD end_pos []) :
    f x ∈ (((f <$> p).lower start) memo input).1.getD end_pos [] := by
  induction p generalizing memo start input end_pos x with
  | Return a =>
      change f x ∈
        (((ParserM.Return (tag := tag) (β := β) (μ := List) (f a)).lower start)
          memo input).1.getD end_pos []
      rw [mem_lower_return_iff] at h ⊢
      exact ⟨h.1, congrArg f h.2⟩
  | Bind p k ih =>
      change f x ∈
        (((ParserM.Bind p (fun a => f <$> k a)).lower start) memo input).1.getD end_pos []
      change x ∈ (((ParserM.Bind p k).lower start) memo input).1.getD end_pos [] at h
      obtain ⟨split₀, _values₀, a₀, preGroups, preActions,
        postActions, postGroups, _h_get₀, _h_value₀, h_actions, h_action⟩ :=
        mem_lower_bind_exists_getElem_action_mem
          (tag := tag) (β := β)
          (p := p) (k := k)
          (memo := memo) (input := input)
          (start := start) (end_pos := end_pos) (x := x) h
      obtain ⟨prePairs, postPairs, split, values, preValues, postValues, a,
        h_toList, h_values, h_preGroups, h_preActions, h_action_eq⟩ :=
        bindActions_action_split_origin
          (tag := tag) (β := β)
          (pivotToResult := ((p start) memo input).1)
          (f := fun a => (k a).lower)
          (preGroups := preGroups) (postGroups := postGroups)
          (preActions := preActions) (postActions := postActions)
          (action := (k a₀).lower split₀) h_actions
      rw [h_action_eq, h_preGroups, h_preActions] at h_action
      let origPrefix :=
        Traversable.foldl joinUnderCache
          (List.foldl (Traversable.foldl joinUnderCache)
            (pure Std.HashMap.emptyWithCapacity)
            (List.map
              (fun pair =>
                match pair with
                | (j, values) => List.map (fun a => (k a).lower j) values)
              prePairs))
          (List.map (fun a => (k a).lower split) preValues)
      let mappedPrefix :=
        Traversable.foldl joinUnderCache
          (List.foldl (Traversable.foldl joinUnderCache)
            (pure Std.HashMap.emptyWithCapacity)
            (List.map
              (fun pair =>
                match pair with
                | (j, values) => List.map (fun a => ((f <$> k a).lower j)) values)
              prePairs))
          (List.map (fun a => ((f <$> k a).lower split)) preValues)
      have h_prefix_state :
          (mappedPrefix (↑((p start) memo input).2) input).2.val =
            (origPrefix (↑((p start) memo input).2) input).2.val := by
        exact bindActionPrefix_snd_val_eq_of_forall
          (tag := tag) (β := β)
          (k := fun a => f <$> k a)
          (g := k)
          (prePairs := prePairs)
          (preValues := preValues)
          (split := split)
          (memo := ↑((p start) memo input).2)
          (input := input)
          (by
            intro a start memo input
            exact lower_map_snd_val_eq
              (tag := tag) (β := β)
              (p := k a) (f := f)
              (memo := memo) (input := input) (start := start))
      have h_mapped_action :
          f x ∈ (((f <$> k a).lower split)
            (↑((mappedPrefix (↑((p start) memo input).2) input).2))
            input).1.getD end_pos [] := by
        rw [h_prefix_state]
        exact ih a
          (memo := ↑((origPrefix (↑((p start) memo input).2) input).2))
          (input := input) (start := split) (end_pos := end_pos)
          (x := x) h_action
      exact mem_lower_bind_of_action_mem
        (tag := tag) (β := β)
        (p := p) (k := fun a => f <$> k a)
        (prePairs := prePairs) (postPairs := postPairs)
        (split := split) (values := values)
        (preValues := preValues) (postValues := postValues)
        (a := a) (memo := memo) (input := input)
        (start := start) (end_pos := end_pos) (x := f x)
        h_toList h_values
        (by
          simpa [mappedPrefix] using h_mapped_action)

set_option maxHeartbeats 1000000 in
set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_lower_map_exists_of_mem
  [DecidableEq α] [DecidableEq α']
  (p : ParserM (tag := tag) β List α)
  (f : α → α')
  (memo : MemoData tag List) (input : Array β)
  (start end_pos : ℕ) (y : α')
  (h : y ∈ (((f <$> p).lower start) memo input).1.getD end_pos []) :
    ∃ x, x ∈ ((p.lower start) memo input).1.getD end_pos [] ∧ f x = y := by
  induction p generalizing memo start input end_pos y with
  | Return a =>
      change y ∈
        (((ParserM.Return (tag := tag) (β := β) (μ := List) (f a)).lower start)
          memo input).1.getD end_pos [] at h
      rw [mem_lower_return_iff] at h
      refine ⟨a, ?_, h.2.symm⟩
      rw [mem_lower_return_iff]
      exact ⟨h.1, rfl⟩
  | Bind p k ih =>
      change y ∈
        (((ParserM.Bind p (fun a => f <$> k a)).lower start) memo input).1.getD end_pos [] at h
      obtain ⟨split₀, _values₀, a₀, preGroups, preActions,
        postActions, postGroups, _h_get₀, _h_value₀, h_actions, h_action⟩ :=
        mem_lower_bind_exists_getElem_action_mem
          (tag := tag) (β := β)
          (p := p) (k := fun a => f <$> k a)
          (memo := memo) (input := input)
          (start := start) (end_pos := end_pos) (x := y) h
      obtain ⟨prePairs, postPairs, split, values, preValues, postValues, a,
        h_toList, h_values, h_preGroups, h_preActions, h_action_eq⟩ :=
        bindActions_action_split_origin
          (tag := tag) (β := β)
          (pivotToResult := ((p start) memo input).1)
          (f := fun a => ((f <$> k a).lower))
          (preGroups := preGroups) (postGroups := postGroups)
          (preActions := preActions) (postActions := postActions)
          (action := ((f <$> k a₀).lower split₀)) h_actions
      rw [h_action_eq, h_preGroups, h_preActions] at h_action
      let origPrefix :=
        Traversable.foldl joinUnderCache
          (List.foldl (Traversable.foldl joinUnderCache)
            (pure Std.HashMap.emptyWithCapacity)
            (List.map
              (fun pair =>
                match pair with
                | (j, values) => List.map (fun a => (k a).lower j) values)
              prePairs))
          (List.map (fun a => (k a).lower split) preValues)
      let mappedPrefix :=
        Traversable.foldl joinUnderCache
          (List.foldl (Traversable.foldl joinUnderCache)
            (pure Std.HashMap.emptyWithCapacity)
            (List.map
              (fun pair =>
                match pair with
                | (j, values) => List.map (fun a => ((f <$> k a).lower j)) values)
              prePairs))
          (List.map (fun a => ((f <$> k a).lower split)) preValues)
      have h_prefix_state :
          (mappedPrefix (↑((p start) memo input).2) input).2.val =
            (origPrefix (↑((p start) memo input).2) input).2.val := by
        exact bindActionPrefix_snd_val_eq_of_forall
          (tag := tag) (β := β)
          (k := fun a => f <$> k a)
          (g := k)
          (prePairs := prePairs)
          (preValues := preValues)
          (split := split)
          (memo := ↑((p start) memo input).2)
          (input := input)
          (by
            intro a start memo input
            exact lower_map_snd_val_eq
              (tag := tag) (β := β)
              (p := k a) (f := f)
              (memo := memo) (input := input) (start := start))
      obtain ⟨x, h_orig_at_mapped, h_fx⟩ :=
        ih a
          (memo := ↑((mappedPrefix (↑((p start) memo input).2) input).2))
          (input := input) (start := split) (end_pos := end_pos)
          (y := y) h_action
      have h_orig_action :
          x ∈ (((k a).lower split)
            (↑((origPrefix (↑((p start) memo input).2) input).2))
            input).1.getD end_pos [] := by
        rw [h_prefix_state] at h_orig_at_mapped
        exact h_orig_at_mapped
      refine ⟨x, ?_, h_fx⟩
      exact mem_lower_bind_of_action_mem
        (tag := tag) (β := β)
        (p := p) (k := k)
        (prePairs := prePairs) (postPairs := postPairs)
        (split := split) (values := values)
        (preValues := preValues) (postValues := postValues)
        (a := a) (memo := memo) (input := input)
        (start := start) (end_pos := end_pos) (x := x)
        h_toList h_values
        (by
          simpa [origPrefix] using h_orig_action)


set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_parser_bind_return_exists_of_mem
  [DecidableEq α]
  (p : Parser (tag := tag) β List α)
  (memo : MemoData tag List) (input : Array β)
  (start end_pos : ℕ) (x : α)
  (h : x ∈ ((Parser.bind p
      (fun a => (ParserM.Return (tag := tag) (β := β) (μ := List) a).lower)
      start) memo input).1.getD end_pos []) :
    x ∈ ((p start) memo input).1.getD end_pos [] := by
  rw [parser_bind_fst_eq_bindContinue] at h
  obtain ⟨split, values, a, _preGroups, _preActions, _postActions, _postGroups,
    h_get, h_a_mem, _h_actions, h_action⟩ :=
    mem_bindContinue_exists_getElem_action_mem
      (tag := tag) (β := β)
      (pivotToResult := ((p start) memo input).1)
      (f := fun a => (ParserM.Return (tag := tag) (β := β) (μ := List) a).lower)
      (memo := ↑((p start) memo input).2)
      (input := input) (end_pos := end_pos) (x := x) h
  rw [mem_lower_return_iff] at h_action
  rcases h_action with ⟨rfl, rfl⟩
  rw [Std.HashMap.getD_eq_getD_getElem?]
  simp [h_get, h_a_mem]

set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_lower_lift_exists_of_mem
  [DecidableEq α]
  (p : Parser (tag := tag) β List α)
  (memo : MemoData tag List) (input : Array β)
  (start end_pos : ℕ) (x : α)
  (h : x ∈ (((ParserM.lift p).lower start) memo input).1.getD end_pos []) :
    x ∈ ((p start) memo input).1.getD end_pos [] := by
  unfold ParserM.lift ParserM.lower at h
  exact mem_parser_bind_return_exists_of_mem (tag := tag) (β := β)
    (p := p) (memo := memo) (input := input)
    (start := start) (end_pos := end_pos) (x := x) h

set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_parser_bind_return_of_mem
  [DecidableEq α]
  (p : Parser (tag := tag) β List α)
  (memo : MemoData tag List) (input : Array β)
  (start end_pos : ℕ) (x : α)
  (h : x ∈ ((p start) memo input).1.getD end_pos []) :
    x ∈ ((Parser.bind p
      (fun a => (ParserM.Return (tag := tag) (β := β) (μ := List) a).lower)
      start) memo input).1.getD end_pos [] := by
  rw [parser_bind_fst_eq_bindContinue]
  exact mem_bindContinue_return_of_mem (tag := tag) (β := β)
    (resultMap := ((p start) memo input).1)
    (memo := ↑((p start) memo input).2)
    (input := input) (end_pos := end_pos) (x := x) h

set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_lower_lift_of_mem
  [DecidableEq α]
  (p : Parser (tag := tag) β List α)
  (memo : MemoData tag List) (input : Array β)
  (start end_pos : ℕ) (x : α)
  (h : x ∈ ((p start) memo input).1.getD end_pos []) :
    x ∈ (((ParserM.lift p).lower start) memo input).1.getD end_pos [] := by
  unfold ParserM.lift ParserM.lower
  exact mem_parser_bind_return_of_mem (tag := tag) (β := β)
    (p := p) (memo := memo) (input := input)
    (start := start) (end_pos := end_pos) (x := x) h

set_option linter.unusedSectionVars false in
omit [Monad μ] [Traversable μ] [SemilatticeAlt μ] [DecidableEq α] in
theorem mem_memoizeStep_of_compute_mem
  (counter : Counter τ)
  (g : ((t : τ) → ParserM (tag := tag) β List (tag t)) →
      (t : τ) → ParserM (tag := tag) β List (tag t))
  (next : ℕ → (t : τ) → ParserM (tag := tag) β List (tag t))
  (t : τ) (memo : MemoData tag List) (input : Array β)
  (start end_pos : ℕ) (x : tag t)
  (h_no_cache :
    (memo.getD t ⊥)[(Counter.toKey counter, start)]? = none)
  (h :
    x ∈ (((g (next (input.size - start + 1)) t).lower start)
      memo input).1.getD end_pos []) :
    x ∈ ((memoizeStep counter g t next start memo input).1.getD end_pos []) := by
  unfold memoizeStep
  simp [h_no_cache]
  exact h

set_option linter.unusedSectionVars false in
omit [Monad μ] [Traversable μ] [SemilatticeAlt μ] [DecidableEq α] in
theorem memoizeStep_compute_fst_eq
  (counter : Counter τ)
  (g : ((t : τ) → ParserM (tag := tag) β List (tag t)) →
      (t : τ) → ParserM (tag := tag) β List (tag t))
  (next : ℕ → (t : τ) → ParserM (tag := tag) β List (tag t))
  (t : τ) (memo : MemoData tag List) (input : Array β)
  (start : ℕ)
  (h_no_cache :
    (memo.getD t ⊥)[(Counter.toKey counter, start)]? = none) :
    (memoizeStep counter g t next start memo input).1 =
      (((g (next (input.size - start + 1)) t).lower start) memo input).1 := by
  unfold memoizeStep
  simp [h_no_cache]

set_option linter.unusedSectionVars false in
omit [Monad μ] [Traversable μ] [SemilatticeAlt μ] [DecidableEq α] in
theorem memoizeStep_compute_snd_val_eq
  (counter : Counter τ)
  (g : ((t : τ) → ParserM (tag := tag) β List (tag t)) →
      (t : τ) → ParserM (tag := tag) β List (tag t))
  (next : ℕ → (t : τ) → ParserM (tag := tag) β List (tag t))
  (t : τ) (memo : MemoData tag List) (input : Array β)
  (start : ℕ)
  (h_no_cache :
    (memo.getD t ⊥)[(Counter.toKey counter, start)]? = none) :
    (memoizeStep counter g t next start memo input).2.val =
      let result :=
        (((g (next (input.size - start + 1)) t).lower start) memo input)
      let key : MemoEntryKey τ := (Counter.toKey counter, start)
      let updatedPositionMap := result.2.val.getD t ⊥
      let updatedMemo := result.2.val.insert t (updatedPositionMap.insert key result.1)
      updatedMemo ⊔ result.2.val := by
  unfold memoizeStep
  simp [h_no_cache]


set_option linter.unusedSectionVars false in
omit [Monad μ] [Traversable μ] [SemilatticeAlt μ] [DecidableEq α] in
theorem memoizeStep_cache_fst_eq
  (counter : Counter τ)
  (g : ((t : τ) → ParserM (tag := tag) β List (tag t)) →
      (t : τ) → ParserM (tag := tag) β List (tag t))
  (next : ℕ → (t : τ) → ParserM (tag := tag) β List (tag t))
  (t : τ) (memo : MemoData tag List) (input : Array β)
  (start : ℕ) (cached : ResultMap List (tag t))
  (h_cache :
    (memo.getD t ⊥)[(Counter.toKey counter, start)]? = some cached) :
    (memoizeStep counter g t next start memo input).1 = cached := by
  unfold memoizeStep
  simp [h_cache]

set_option linter.unusedSectionVars false in
omit [Monad μ] [Traversable μ] [SemilatticeAlt μ] [DecidableEq α] in
theorem memoizeStep_cache_snd_val_eq
  (counter : Counter τ)
  (g : ((t : τ) → ParserM (tag := tag) β List (tag t)) →
      (t : τ) → ParserM (tag := tag) β List (tag t))
  (next : ℕ → (t : τ) → ParserM (tag := tag) β List (tag t))
  (t : τ) (memo : MemoData tag List) (input : Array β)
  (start : ℕ) (cached : ResultMap List (tag t))
  (h_cache :
    (memo.getD t ⊥)[(Counter.toKey counter, start)]? = some cached) :
    (memoizeStep counter g t next start memo input).2.val = memo := by
  unfold memoizeStep
  simp [h_cache]

set_option linter.unusedSectionVars false in
omit [Monad μ] [Traversable μ] [SemilatticeAlt μ] [DecidableEq α] in
theorem mem_memoizeStep_of_cache_mem
  (counter : Counter τ)
  (g : ((t : τ) → ParserM (tag := tag) β List (tag t)) →
      (t : τ) → ParserM (tag := tag) β List (tag t))
  (next : ℕ → (t : τ) → ParserM (tag := tag) β List (tag t))
  (t : τ) (memo : MemoData tag List) (input : Array β)
  (start end_pos : ℕ) (x : tag t) (cached : ResultMap List (tag t))
  (h_cache :
    (memo.getD t ⊥)[(Counter.toKey counter, start)]? = some cached)
  (h :
    x ∈ cached.getD end_pos []) :
    x ∈ ((memoizeStep counter g t next start memo input).1.getD end_pos []) := by
  rw [memoizeStep_cache_fst_eq
    (counter := counter) (g := g) (next := next) (t := t)
    (memo := memo) (input := input) (start := start)
    (cached := cached) h_cache]
  exact h


set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_parser_orElse_left_of_mem
  [DecidableEq α]
  (p q : Parser (tag := tag) β List α)
  (memo : MemoData tag List) (input : Array β)
  (start end_pos : ℕ) (x : α)
  (h : x ∈ ((p start) memo input).1.getD end_pos []) :
    x ∈ ((Parser.orElse p q start) memo input).1.getD end_pos [] := by
  unfold Parser.orElse
  exact mem_joinUnderCache_left (tag := tag) (β := β)
    (p start) (q start) memo input end_pos x h

set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_parser_orElse_right_after_left_of_mem
  [DecidableEq α]
  (p q : Parser (tag := tag) β List α)
  (memo : MemoData tag List) (input : Array β)
  (start end_pos : ℕ) (x : α)
  (h : x ∈ ((q start) (↑((p start) memo input).2) input).1.getD end_pos []) :
    x ∈ ((Parser.orElse p q start) memo input).1.getD end_pos [] := by
  unfold Parser.orElse
  exact mem_joinUnderCache_right (tag := tag) (β := β)
    (p start) (q start) memo input end_pos x h

set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_parser_orElse_or
  [DecidableEq α]
  (p q : Parser (tag := tag) β List α)
  (memo : MemoData tag List) (input : Array β)
  (start end_pos : ℕ) (x : α)
  (h : x ∈ ((Parser.orElse p q start) memo input).1.getD end_pos []) :
    x ∈ ((p start) memo input).1.getD end_pos [] ∨
    x ∈ ((q start) (↑((p start) memo input).2) input).1.getD end_pos [] := by
  unfold Parser.orElse at h
  exact mem_joinUnderCache_or (tag := tag) (β := β)
    (p start) (q start) memo input end_pos x h


set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_lower_sup_left
  [DecidableEq α]
  (p q : ParserM (tag := tag) β List α)
  (memo : MemoData tag List) (input : Array β)
  (start end_pos : ℕ) (x : α)
  (h : x ∈ ((p.lower start) memo input).1.getD end_pos []) :
    x ∈ (((p ⊔ q).lower start) memo input).1.getD end_pos [] := by
  cases p <;> cases q <;>
    unfold Max.max ParserM.instMaxOfTraversableOfDecidableEq ParserM.lift
      ParserM.lower Parser.bind <;>
    apply mem_parser_bind_return_of_mem <;>
    apply mem_parser_orElse_left_of_mem <;>
    assumption

set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_lower_sup_right_after_left_of_mem
  [DecidableEq α]
  (p q : ParserM (tag := tag) β List α)
  (memo : MemoData tag List) (input : Array β)
  (start end_pos : ℕ) (x : α)
  (h : x ∈ ((q.lower start) (↑(((p.lower start) memo input).2)) input).1.getD end_pos []) :
    x ∈ (((p ⊔ q).lower start) memo input).1.getD end_pos [] := by
  cases p <;> cases q <;>
    unfold Max.max ParserM.instMaxOfTraversableOfDecidableEq ParserM.lift
      ParserM.lower Parser.bind <;>
    apply mem_parser_bind_return_of_mem <;>
    apply mem_parser_orElse_right_after_left_of_mem <;>
    assumption

set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_lower_sup_or
  [DecidableEq α]
  (p q : ParserM (tag := tag) β List α)
  (memo : MemoData tag List) (input : Array β)
  (start end_pos : ℕ) (x : α)
  (h : x ∈ (((p ⊔ q).lower start) memo input).1.getD end_pos []) :
    x ∈ ((p.lower start) memo input).1.getD end_pos [] ∨
    x ∈ ((q.lower start) (↑(((p.lower start) memo input).2)) input).1.getD end_pos [] := by
  cases p with
  | Return a =>
      cases q with
      | Return b =>
          unfold Max.max ParserM.instMaxOfTraversableOfDecidableEq ParserM.lower Parser.bind at h
          have h_or := mem_parser_orElse_or (tag := tag) (β := β)
            (pure a) (pure b) memo input start end_pos x
            (mem_parser_bind_return_exists_of_mem (tag := tag) (β := β)
              (p := Parser.orElse (pure a) (pure b))
              (memo := memo) (input := input)
              (start := start) (end_pos := end_pos) (x := x) h)
          cases h_or with
          | inl h_left =>
              left
              simpa [ParserM.lower] using h_left
          | inr h_right =>
              right
              simpa [ParserM.lower] using h_right
      | Bind q k =>
          unfold Max.max ParserM.instMaxOfTraversableOfDecidableEq ParserM.lift ParserM.lower at h
          have h_or := mem_parser_orElse_or (tag := tag) (β := β)
            (pure a) (q.bind (ParserM.lower ∘ k)) memo input start end_pos x
            (mem_lower_lift_exists_of_mem (tag := tag) (β := β)
              (p := Parser.orElse (pure a) (q.bind (ParserM.lower ∘ k)))
              (memo := memo) (input := input)
              (start := start) (end_pos := end_pos) (x := x) h)
          cases h_or with
          | inl h_left =>
              left
              simpa [ParserM.lower] using h_left
          | inr h_right =>
              right
              simpa [ParserM.lower, Function.comp_apply] using h_right
  | Bind p k =>
      cases q with
      | Return b =>
          unfold Max.max ParserM.instMaxOfTraversableOfDecidableEq ParserM.lift ParserM.lower at h
          have h_or := mem_parser_orElse_or (tag := tag) (β := β)
            (p.bind (ParserM.lower ∘ k)) (pure b) memo input start end_pos x
            (mem_lower_lift_exists_of_mem (tag := tag) (β := β)
              (p := Parser.orElse (p.bind (ParserM.lower ∘ k)) (pure b))
              (memo := memo) (input := input)
              (start := start) (end_pos := end_pos) (x := x) h)
          cases h_or with
          | inl h_left =>
              left
              simpa [ParserM.lower, Function.comp_apply] using h_left
          | inr h_right =>
              right
              simpa [ParserM.lower] using h_right
      | Bind q kq =>
          unfold Max.max ParserM.instMaxOfTraversableOfDecidableEq ParserM.lift ParserM.lower at h
          have h_or := mem_parser_orElse_or (tag := tag) (β := β)
            (p.bind (ParserM.lower ∘ k)) (q.bind (ParserM.lower ∘ kq))
            memo input start end_pos x
            (mem_lower_lift_exists_of_mem (tag := tag) (β := β)
              (p := Parser.orElse
                (p.bind (ParserM.lower ∘ k))
                (q.bind (ParserM.lower ∘ kq)))
              (memo := memo) (input := input)
              (start := start) (end_pos := end_pos) (x := x) h)
          cases h_or with
          | inl h_left =>
              left
              simpa [ParserM.lower, Function.comp_apply] using h_left
          | inr h_right =>
              right
              simpa [ParserM.lower, Function.comp_apply] using h_right

set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_lower_sup_iff_after_left
  [DecidableEq α]
  (p q : ParserM (tag := tag) β List α)
  (memo : MemoData tag List) (input : Array β)
  (start end_pos : ℕ) (x : α) :
    x ∈ (((p ⊔ q).lower start) memo input).1.getD end_pos [] ↔
      x ∈ ((p.lower start) memo input).1.getD end_pos [] ∨
      x ∈ ((q.lower start)
        (↑(((p.lower start) memo input).2)) input).1.getD end_pos [] := by
  constructor
  · exact mem_lower_sup_or (tag := tag) (β := β)
      p q memo input start end_pos x
  · intro h
    exact h.elim
      (mem_lower_sup_left (tag := tag) (β := β)
        p q memo input start end_pos x)
      (mem_lower_sup_right_after_left_of_mem (tag := tag) (β := β)
        p q memo input start end_pos x)


omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
def terminalPrimitive [DecidableEq β] (a : β) :
    Parser (tag := tag) β List β :=
  fun pos => do
    let input ← read
    if pos >= 0 && some a = input[pos]? then
      pure ({(pos + 1, pure a)} : ResultMap List β)
    else
      pure Std.HashMap.emptyWithCapacity

omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem terminalPrimitive_snd_val_eq
  [DecidableEq β]
  (a : β) (input : Array β) (start : ℕ)
  (memo : MemoData tag List) :
    ((terminalPrimitive (tag := tag) a start) memo input).2.val = memo := by
  unfold terminalPrimitive
  simp only [ge_iff_le, Nat.zero_le, decide_true, Bool.true_and, readThe,
    MonadReader.read, MonadReaderOf.read, ReaderT.read, liftM, monadLift,
    MonadLift.monadLift, instMonadMStateT, ReaderT.instMonad, ReaderT.bind,
    Id.instMonad, Pure.pure, ReaderT.pure]
  split <;> simp [readerT_pure_snd]

omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem terminal'_eq_lift_terminalPrimitive
  [DecidableEq β] (a : β) :
    terminal' (tag := tag) (μ := List) a =
      ParserM.lift (terminalPrimitive (tag := tag) a) := by
  rfl

omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_terminalPrimitive_iff
  [DecidableEq β]
  (a x : β) (input : Array β) (start end_pos : ℕ)
  (memo : MemoData tag List) :
    x ∈ ((terminalPrimitive (tag := tag) a start) memo input).1.getD end_pos [] ↔
      some a = input[start]? ∧ end_pos = start + 1 ∧ x = a := by
  unfold terminalPrimitive
  simp only [ge_iff_le, Nat.zero_le, decide_true, Bool.true_and, readThe,
    MonadReader.read, MonadReaderOf.read, ReaderT.read, liftM, monadLift,
    MonadLift.monadLift, instMonadMStateT, ReaderT.instMonad, ReaderT.bind,
    Id.instMonad, Pure.pure, ReaderT.pure]
  by_cases h_match : some a = input[start]?
  · simp only [h_match, decide_true, if_true, readerT_pure_fst,
      Std.HashMap.getD_eq_getD_getElem?]
    by_cases h_end : end_pos = start + 1
    · subst end_pos
      simp
    · simp [h_end, Ne.symm h_end]
  · simp [h_match, readerT_pure_fst, Std.HashMap.getD_eq_getD_getElem?]

omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_lower_terminal_iff
  [DecidableEq β]
  (a x : β) (input : Array β) (start end_pos : ℕ)
  (memo : MemoData tag List) :
    x ∈ (((terminal' (tag := tag) (μ := List) a).lower start)
      memo input).1.getD end_pos [] ↔
      some a = input[start]? ∧ end_pos = start + 1 ∧ x = a := by
  rw [terminal'_eq_lift_terminalPrimitive]
  constructor
  · intro h
    apply (mem_terminalPrimitive_iff (tag := tag) (a := a) (x := x)
      (input := input) (start := start) (end_pos := end_pos) (memo := memo)).mp
    exact mem_lower_lift_exists_of_mem (tag := tag) (β := β)
      (p := terminalPrimitive (tag := tag) a) (memo := memo) (input := input)
      (start := start) (end_pos := end_pos) (x := x) h
  · intro h
    apply mem_lower_lift_of_mem (tag := tag) (β := β)
      (p := terminalPrimitive (tag := tag) a) (memo := memo) (input := input)
      (start := start) (end_pos := end_pos) (x := x)
    exact (mem_terminalPrimitive_iff (tag := tag) (a := a) (x := x)
      (input := input) (start := start) (end_pos := end_pos) (memo := memo)).mpr h


set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_lower_cons_map_exists_of_cons
  [DecidableEq α]
  (tail : List (ParserM (tag := tag) β List α))
  (head_result : α)
  (memo : MemoData tag List) (input : Array β)
  (split end_pos : ℕ)
  {result_head : α} {result_tail : List α}
  (h :
    result_head :: result_tail ∈
      (((List.cons head_result <$> List.traverse id tail).lower split)
        memo input).1.getD end_pos []) :
    result_head = head_result ∧
      result_tail ∈
        (((List.traverse id tail).lower split) memo input).1.getD end_pos [] := by
  obtain ⟨tail_result, h_tail_mem, h_eq⟩ :=
    mem_lower_map_exists_of_mem
      (tag := tag) (β := β)
      (p := List.traverse id tail)
      (f := List.cons head_result)
      (memo := memo) (input := input)
      (start := split) (end_pos := end_pos)
      (y := result_head :: result_tail) h
  cases h_eq
  exact ⟨rfl, h_tail_mem⟩

set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem not_mem_lower_cons_map_nil
  [DecidableEq α]
  (tail : List (ParserM (tag := tag) β List α))
  (head_result : α)
  (memo : MemoData tag List) (input : Array β)
  (split end_pos : ℕ)
  (h :
    ([] : List α) ∈
      (((List.cons head_result <$> List.traverse id tail).lower split)
        memo input).1.getD end_pos []) :
    False := by
  obtain ⟨tail_result, _h_tail_mem, h_eq⟩ :=
    mem_lower_map_exists_of_mem
      (tag := tag) (β := β)
      (p := List.traverse id tail)
      (f := List.cons head_result)
      (memo := memo) (input := input)
      (start := split) (end_pos := end_pos)
      (y := ([] : List α)) h
  cases h_eq

set_option maxHeartbeats 1000000 in
set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_lower_traverse_preserves_length
  [DecidableEq α]
  (xs : List (ParserM (tag := tag) β List α))
  (memo : MemoData tag List) (input : Array β)
  (start end_pos : ℕ) (result : List α)
  (h :
    result ∈
      (((List.traverse id xs).lower start) memo input).1.getD end_pos []) :
    result.length = xs.length := by
  induction xs generalizing memo start end_pos result with
  | nil =>
      have h_return := (mem_lower_return_iff
        (tag := tag) (β := β)
        (a := ([] : List α)) (x := result)
        (memo := memo) (input := input)
        (start := start) (end_pos := end_pos)).mp (by
          simpa [List.traverse] using h)
      simp [h_return.2]
  | cons head tail ih =>
      rw [List.traverse, seq_eq_bind] at h
      simp at h
      have h_cons :
          ∀ (head : ParserM (tag := tag) β List α)
            (memo : MemoData tag List) (start end_pos : ℕ)
            (result : List α),
            result ∈
              (((head >>= fun a => List.cons a <$> List.traverse id tail).lower start)
                memo input).1.getD end_pos [] →
            result.length = tail.length + 1 := by
        intro head
        induction head with
        | Return a =>
            intro memo start end_pos result h_result
            change result ∈
              (((List.cons a <$> List.traverse id tail).lower start)
                memo input).1.getD end_pos [] at h_result
            cases result with
            | nil =>
                exact False.elim
                  (not_mem_lower_cons_map_nil
                    (tag := tag) (β := β)
                    (tail := tail) (head_result := a)
                    (memo := memo) (input := input)
                    (split := start) (end_pos := end_pos) h_result)
            | cons result_head result_tail =>
                obtain ⟨h_head_eq, h_tail_mem⟩ :=
                  mem_lower_cons_map_exists_of_cons
                    (tag := tag) (β := β)
                    (tail := tail) (head_result := a)
                    (memo := memo) (input := input)
                    (split := start) (end_pos := end_pos) h_result
                cases h_head_eq
                simp
                exact ih
                  (memo := memo) (start := start) (end_pos := end_pos)
                  (result := result_tail) h_tail_mem
        | Bind p k ih_head =>
            intro memo start end_pos result h_result
            change result ∈
              (((ParserM.Bind p
                (fun a => k a >>= fun a => List.cons a <$> List.traverse id tail)).lower start)
                memo input).1.getD end_pos [] at h_result
            obtain ⟨split, _values, a, _preGroups, _preActions,
              _postActions, _postGroups, _h_get, _h_value, _h_actions, h_action⟩ :=
              mem_lower_bind_exists_getElem_action_mem
                (tag := tag) (β := β)
                (p := p)
                (k := fun a => k a >>= fun a => List.cons a <$> List.traverse id tail)
                (memo := memo) (input := input)
                (start := start) (end_pos := end_pos)
                (x := result) h_result
            exact ih_head a
              (memo := _)
              (start := split) (end_pos := end_pos)
              (result := result) h_action
      exact h_cons head memo start end_pos result h


set_option maxHeartbeats 1000000 in
set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_lower_traverse_cons_lift_exists_head_tail
  (p : Parser (tag := tag) β List α)
  (tail : List (ParserM (tag := tag) β List α))
  (memo : MemoData tag List) (input : Array β)
  (start end_pos : ℕ)
  {result_head : α} {result_tail : List α}
  (h :
    result_head :: result_tail ∈
      (((List.traverse id (ParserM.lift p :: tail)).lower start)
        memo input).1.getD end_pos []) :
    ∃ split memo_tail,
      result_head ∈ ((p start) memo input).1.getD split [] ∧
      result_tail ∈
        (((List.traverse id tail).lower split) memo_tail input).1.getD end_pos [] := by
  rw [List.traverse, seq_eq_bind] at h
  simp at h
  change result_head :: result_tail ∈
    (((ParserM.Bind p
      (fun a => List.cons a <$> List.traverse id tail)).lower start)
      memo input).1.getD end_pos [] at h
  obtain ⟨prePairs, postPairs, split, values, preValues, postValues, a,
    h_toList, h_values, h_action⟩ :=
    mem_lower_bind_exists_action_split_mem
      (tag := tag) (β := β)
      (p := p)
      (k := fun a => List.cons a <$> List.traverse id tail)
      (memo := memo) (input := input)
      (start := start) (end_pos := end_pos)
      (x := result_head :: result_tail) h
  obtain ⟨h_head_eq, h_tail_mem⟩ :=
    mem_lower_cons_map_exists_of_cons
      (tag := tag) (β := β)
      (tail := tail) (head_result := a)
      (memo := _) (input := input)
      (split := split) (end_pos := end_pos)
      h_action
  cases h_head_eq
  refine ⟨split, _, ?_, h_tail_mem⟩
  rw [Std.HashMap.getD_eq_getD_getElem?]
  have h_get : ((p start) memo input).1[split]? = some values := by
    rw [← Std.HashMap.mem_toList_iff_getElem?_eq_some]
    rw [h_toList]
    simp
  simp [h_get, h_values]


set_option maxHeartbeats 1000000 in
set_option linter.unusedSectionVars false in
omit α [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] [DecidableEq α] in
theorem mem_lower_traverse_complete_cons_of_bind_getElem_action_mem
  [DecidableEq α']
  {δ : Type u}
  (p : Parser (tag := tag) β List δ)
  (k : δ → ParserM (tag := tag) β List α')
  (tail : List (ParserM (tag := tag) β List α'))
  (split : ℕ) (values : List δ) (a : δ)
  (memo : MemoData tag List) (input : Array β)
  (start end_pos : ℕ) (x : α') (xs : List α')
  (h_get : ((p start) memo input).1[split]? = some values)
  (h_value : a ∈ values)
  (h_action :
    ∀ prePairs postPairs preValues postValues,
      ((p start) memo input).1.toList =
        prePairs ++ (split, values) :: postPairs →
      values = preValues ++ a :: postValues →
      x :: xs ∈
        (((k a >>= fun a => List.cons a <$> List.traverse id tail).lower split)
          (↑((Traversable.foldl joinUnderCache
            (List.foldl (Traversable.foldl joinUnderCache)
              (pure Std.HashMap.emptyWithCapacity)
              (List.map
                (fun pair : ℕ × List δ =>
                  match pair with
                  | (j, values) =>
                      List.map
                        (fun a =>
                          ((k a >>= fun a => List.cons a <$> List.traverse id tail).lower j))
                        values)
                prePairs))
            (List.map
              (fun a => ((k a >>= fun a => List.cons a <$> List.traverse id tail).lower split))
              preValues))
            (↑((p start) memo input).2) input).2)
          input).1.getD end_pos []) :
    x :: xs ∈
      (((List.traverse id ((ParserM.Bind p k) :: tail)).lower start)
        memo input).1.getD end_pos [] := by
  rw [List.traverse, seq_eq_bind]
  simp
  change x :: xs ∈
    (((ParserM.Bind p
      (fun a => k a >>= fun a => List.cons a <$> List.traverse id tail)).lower start)
      memo input).1.getD end_pos []
  exact mem_lower_bind_of_getElem_action_mem
    (tag := tag) (β := β)
    (p := p)
    (k := fun a => k a >>= fun a => List.cons a <$> List.traverse id tail)
    (split := split) (values := values) (a := a)
    (memo := memo) (input := input)
    (start := start) (end_pos := end_pos)
    (x := x :: xs)
    h_get h_value h_action
