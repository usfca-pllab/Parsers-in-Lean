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

omit [Fintype τ] [Traversable μ] [DecidableEq α] in
theorem parser_map_fst_eq
  [DecidableEq α']
  (p : Parser (tag := tag) β μ α)
  (f : α → α')
  (memo : MemoData tag μ) (input : Array β)
  (start : ℕ) :
    (((f <$> p) start) memo input).1 =
      Std.HashMap.map (fun _ => @Functor.map μ semilat_μ.toFunctor α α' f)
        ((p start) memo input).1 := by
  unfold instFunctorParser
  simp only [Function.comp_apply]
  unfold Functor.map
  simp only [instMonadMStateT]
  simp only [ReaderT.instMonad, ReaderT.bind, Id.instMonad]
  simp only [Pure.pure]
  unfold ReaderT.pure
  rfl

omit [Fintype τ] [BEq τ] [LawfulBEq τ] [Hashable τ] [DecidableEq τ]
  [Monad μ] [Traversable μ] [SemilatticeAlt μ]
  [∀ t : τ, DecidableEq (tag t)] [DecidableEq α] in
theorem mstateT_reader_map_snd_eq
  {σ ρ γ δ : Type u} [Setoid σ] [Semilatticeoid σ ‹Setoid σ›]
  (m : MStateT σ (ReaderM ρ) γ) (f : γ → δ)
  (s : σ) (r : ρ) :
    ((f <$> m) s r).2 = (m s r).2 := by
  unfold Functor.map
  simp only [instMonadMStateT, ReaderT.instMonad, ReaderT.bind, Id.instMonad]
  cases h : m s r with
  | mk a s' =>
      simp [Pure.pure, ReaderT.pure]

omit [Fintype τ] [Traversable μ] [DecidableEq α] in
theorem parser_map_snd_eq
  [DecidableEq α']
  (p : Parser (tag := tag) β μ α)
  (f : α → α')
  (memo : MemoData tag μ) (input : Array β)
  (start : ℕ) :
    (((f <$> p) start) memo input).2 =
      ((p start) memo input).2 := by
  exact mstateT_reader_map_snd_eq
    (m := p start)
    (f := Std.HashMap.map (fun _ => @Functor.map μ semilat_μ.toFunctor α α' f))
    (s := memo) (r := input)

set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_parser_map_of_mem
  [DecidableEq α] [DecidableEq α']
  (p : Parser (tag := tag) β List α)
  (f : α → α')
  (memo : MemoData tag List) (input : Array β)
  (start end_pos : ℕ) (x : α)
  (h : x ∈ ((p start) memo input).1.getD end_pos []) :
    f x ∈ (((f <$> p) start) memo input).1.getD end_pos [] := by
  rw [parser_map_fst_eq (tag := tag) (β := β)
    (p := p) (f := f) (memo := memo) (input := input) (start := start)]
  rw [Std.HashMap.getD_map]
  rw [Std.HashMap.getD_eq_getD_getElem?] at h
  cases h_opt : ((p start) memo input).1[end_pos]? <;> simp [h_opt] at h ⊢
  exact ⟨x, h, rfl⟩

set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_parser_map_exists_of_mem
  [DecidableEq α] [DecidableEq α']
  (p : Parser (tag := tag) β List α)
  (f : α → α')
  (memo : MemoData tag List) (input : Array β)
  (start end_pos : ℕ) (y : α')
  (h : y ∈ (((f <$> p) start) memo input).1.getD end_pos []) :
    ∃ x, x ∈ ((p start) memo input).1.getD end_pos [] ∧ f x = y := by
  rw [parser_map_fst_eq (tag := tag) (β := β)
    (p := p) (f := f) (memo := memo) (input := input) (start := start)] at h
  rw [Std.HashMap.getD_map] at h
  rw [Std.HashMap.getD_eq_getD_getElem?]
  cases h_opt : ((p start) memo input).1[end_pos]? <;> simp [h_opt] at h ⊢
  obtain ⟨x, h_x, h_eq⟩ := h
  exact ⟨x, h_x, h_eq⟩

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

set_option linter.unusedSectionVars false in
omit [Fintype τ] [BEq τ] [LawfulBEq τ] [Hashable τ] [DecidableEq τ]
  [Monad μ] [Traversable μ] [SemilatticeAlt μ]
  [∀ t : τ, DecidableEq (tag t)] [DecidableEq α] in
theorem mem_resultMap_getD_of_mem_getElem?_toList_flatten
  (resultMap : ResultMap List α) {end_pos : ℕ} {x : α}
  (h : x ∈ resultMap[end_pos]?.toList.flatten) :
    x ∈ resultMap.getD end_pos [] := by
  rw [Std.HashMap.getD_eq_getD_getElem?]
  cases h_opt : resultMap[end_pos]? <;> simp [h_opt] at h ⊢
  exact h

set_option linter.unusedSectionVars false in
omit [Fintype τ] [BEq τ] [LawfulBEq τ] [Hashable τ] [DecidableEq τ]
  [Monad μ] [Traversable μ] [SemilatticeAlt μ]
  [∀ t : τ, DecidableEq (tag t)] [DecidableEq α] in
theorem mem_resultMap_getElem?_toList_flatten_of_mem_getD
  (resultMap : ResultMap List α) {end_pos : ℕ} {x : α}
  (h : x ∈ resultMap.getD end_pos []) :
    x ∈ resultMap[end_pos]?.toList.flatten := by
  rw [Std.HashMap.getD_eq_getD_getElem?] at h
  cases h_opt : resultMap[end_pos]? <;> simp [h_opt] at h ⊢
  exact h

omit [Fintype τ] in
theorem runParser_pure
  (a : α)
  (start n : ℕ)
  : (runParser (tag := tag) (pure a) input start).1[n]? =
      if n = start then some (pure (f := μ) a) else none := by
  change (Std.HashMap.emptyWithCapacity.insert start (pure (f := μ) a))[n]? =
    if n = start then some (pure (f := μ) a) else none
  by_cases h : n = start
  · simp [h]
  · have h' : start ≠ n := by
      intro h_start
      exact h h_start.symm
    simp [h, h']

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
  · subst h
    simp
  · have h_key : start ≠ end_pos := by
      intro h_eq
      exact h h_eq.symm
    simp [h, h_key]

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
theorem prod_fst_bifunctor_snd
  {α : Type u} {β γ : Type v}
  (f : β → γ) (x : α × β) :
    (Bifunctor.snd f x).1 = x.1 := by
  cases x
  rfl

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
  cases h_list : m.toList with
  | nil => simp [h_list] at h_len
  | cons head tail =>
      cases tail with
      | nil =>
          simp [h_list] at h_mem
          subst head
          rfl
      | cons _ _ =>
          simp [h_list] at h_len

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
theorem traversable_foldl_singleton
  {σ α : Type u} (f : σ → α → σ) (init : σ) (x : α) :
    Traversable.foldl f init ([x] : List α) = f init x := by
  simp only [Traversable.foldl, Traversable.foldMap, instTraversableList,
    instApplicativeConstOfOneOfMul, Functor.Const.functor,
    Monoid.Foldl.get, MulOpposite.instMul]
  simp only [List.traverse, Functor.Const.map, MulOpposite.unop_mul]
  simp only [Functor.Const.mk', Monoid.Foldl.mk, Function.comp_apply,
    MulOpposite.unop_op]
  unfold instHMul
  simp only [CategoryTheory.End.mul, CategoryTheory.types, Function.comp_apply]
  change f init x = f init x
  rfl

omit [Fintype τ] [BEq τ] [LawfulBEq τ] [Hashable τ] [DecidableEq τ]
  [Monad μ] [Traversable μ] [SemilatticeAlt μ]
  [∀ t : τ, DecidableEq (tag t)] in
theorem traversable_foldl_cons
  {σ α : Type u} (f : σ → α → σ) (init : σ) (x : α) (xs : List α) :
    Traversable.foldl f init (x :: xs) =
      Traversable.foldl f (f init x) xs := by
  simp only [Traversable.foldl, Traversable.foldMap, instTraversableList,
    instApplicativeConstOfOneOfMul, Functor.Const.functor,
    Monoid.Foldl.get, MulOpposite.instMul]
  simp only [List.traverse]
  simp only [Functor.Const.map, MulOpposite.unop_mul]
  simp only [Functor.Const.mk', Monoid.Foldl.mk, Function.comp_apply,
    MulOpposite.unop_op]
  unfold instHMul
  simp only [CategoryTheory.End.mul, CategoryTheory.types, Function.comp_apply]
  rfl

omit [Fintype τ] [BEq τ] [LawfulBEq τ] [Hashable τ] [DecidableEq τ]
  [Monad μ] [Traversable μ] [SemilatticeAlt μ]
  [∀ t : τ, DecidableEq (tag t)] in
theorem traversable_foldl_nil
  {σ α : Type u} (f : σ → α → σ) (init : σ) :
    Traversable.foldl f init ([] : List α) = init := by
  simp only [Traversable.foldl, Traversable.foldMap, instTraversableList,
    instApplicativeConstOfOneOfMul, Functor.Const.functor,
    Monoid.Foldl.get, MulOpposite.instMul]
  simp only [List.traverse]
  change init = init
  rfl

omit [Fintype τ] [BEq τ] [LawfulBEq τ] [Hashable τ] [DecidableEq τ]
  [Monad μ] [Traversable μ] [SemilatticeAlt μ]
  [∀ t : τ, DecidableEq (tag t)] in
theorem traversable_foldl_append
  {σ α : Type u} (f : σ → α → σ) (init : σ) (xs ys : List α) :
    Traversable.foldl f init (xs ++ ys) =
      Traversable.foldl f (Traversable.foldl f init xs) ys := by
  induction xs generalizing init with
  | nil =>
      simp only [List.nil_append]
      rw [traversable_foldl_nil]
  | cons x xs ih =>
      rw [List.cons_append]
      rw [traversable_foldl_cons]
      rw [traversable_foldl_cons]
      exact ih (f init x)

omit [Fintype τ] in
theorem runParser_failure_getElem?_eq_none
  (input : Array β) (start end_pos : ℕ)
  : (runParser (tag := tag) (⊥ : ParserM (tag := tag) β μ α) input start).1[end_pos]? = none := by
  change (runParser (tag := tag)
    (ParserM.lift (Parser.failure : Parser (tag := tag) β μ α))
    input start).1[end_pos]? = none
  unfold runParser ParserM.lift ParserM.lower Parser.bind Parser.bindRun Parser.failure
    Parser.bindContinue Parser.bindActions MStateT.run
  simp only [ReaderT.instFunctorOfMonad, ReaderT.instApplicativeOfMonad,
    ReaderT.instMonad, ReaderT.pure, Id.instMonad, Pure.pure,
    instMonadMStateT,
    hashMap_emptyWithCapacity_toList_eq_nil, List.map_nil, List.foldl_nil]
  change (Std.HashMap.emptyWithCapacity : Std.HashMap ℕ (μ α))[end_pos]? = none
  simp

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
  induction actions generalizing acc memo with
  | nil =>
      simp [Traversable.foldl]
      exact h
  | cons action rest ih =>
      rw [traversable_foldl_cons]
      exact ih (acc := joinUnderCache acc action) memo
        (mem_joinUnderCache_left acc action memo input end_pos x h)

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
  induction actionGroups generalizing acc memo with
  | nil =>
      simpa using h
  | cons actions rest ih =>
      simp [List.foldl]
      exact ih (acc := Traversable.foldl joinUnderCache acc actions) memo
        (mem_traversable_foldl_joinUnderCache_of_acc actions acc memo input end_pos x h)

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
theorem mem_list_foldl_traversable_joinUnderCache_or_group
  [DecidableEq α]
  (actionGroups : List (List (MStateT (MemoData tag List) (ReaderM (Array β)) (ResultMap List α))))
  (acc : MStateT (MemoData tag List) (ReaderM (Array β)) (ResultMap List α))
  (memo : MemoData tag List) (input : Array β)
  (end_pos : ℕ) (x : α)
  (h : x ∈ ((List.foldl (Traversable.foldl joinUnderCache) acc actionGroups)
    memo input).1.getD end_pos []) :
    x ∈ (acc memo input).1.getD end_pos [] ∨
    ∃ pre group post,
      actionGroups = pre ++ group :: post ∧
      x ∈ ((Traversable.foldl joinUnderCache
        (List.foldl (Traversable.foldl joinUnderCache) acc pre) group)
        memo input).1.getD end_pos [] := by
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
          exact Or.inr ⟨[], group, rest, by simp, by simpa using h_group⟩
      | inr h_later =>
          rcases h_later with ⟨pre, group', post, h_eq, h_mem⟩
          refine Or.inr ⟨group :: pre, group', post, ?_, ?_⟩
          · simp [h_eq]
          · simpa [List.foldl] using h_mem

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
  let pairs := pivotToResult.toList
  change List.Forall₂
      (List.Forall₂
        (fun action action' => ∀ memo input,
          (action memo input).2.val = (action' memo input).2.val))
      (List.map
        (fun pair : ℕ × List δ =>
          match pair with
          | (j, values) => List.map (fun a => f a j) values)
        pairs)
      (List.map
        (fun pair : ℕ × List δ =>
          match pair with
          | (j, values) => List.map (fun a => g a j) values)
        pairs)
  induction pairs with
  | nil =>
      exact List.Forall₂.nil
  | cons pair _ ih =>
      rcases pair with ⟨split, values⟩
      apply List.Forall₂.cons
      · induction values with
        | nil =>
            exact List.Forall₂.nil
        | cons a _ ih_values =>
            exact List.Forall₂.cons (h a split) ih_values
      · exact ih

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
    · induction prePairs with
      | nil =>
          exact List.Forall₂.nil
      | cons pair pairs ih =>
          rcases pair with ⟨j, values⟩
          apply List.Forall₂.cons
          · induction values with
            | nil =>
                exact List.Forall₂.nil
            | cons a values ih_values =>
                exact List.Forall₂.cons (h a j) ih_values
          · exact ih
  · induction preValues with
    | nil =>
        exact List.Forall₂.nil
    | cons a values ih =>
        exact List.Forall₂.cons (h a split) ih

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
  induction actions generalizing acc memo with
  | nil =>
      simpa [traversable_foldl_nil] using h_acc memo input
  | cons action actions ih =>
      rw [traversable_foldl_cons]
      exact ih
        (acc := joinUnderCache acc action)
        (memo := memo)
        (fun memo input => by
          rw [joinUnderCache_snd_eq]
          change (action (↑((acc memo input).2)) input).2.val = memo
          rw [h_actions action (by simp)
            (↑((acc memo input).2)) input]
          exact h_acc memo input)
        (fun action' h_action' memo input =>
          h_actions action' (by simp [h_action']) memo input)

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
  induction groups generalizing acc memo with
  | nil =>
      simpa using h_acc memo input
  | cons group groups ih =>
      simp only [List.foldl_cons]
      exact ih
        (acc := Traversable.foldl joinUnderCache acc group)
        (memo := memo)
        (fun memo input =>
          traversable_foldl_joinUnderCache_snd_val_eq_self
            (tag := tag) (β := β)
            (actions := group) (acc := acc)
            (memo := memo) (input := input)
            h_acc
            (fun action h_action memo input =>
              h_groups group (by simp) action h_action memo input))
        (fun group' h_group' action h_action memo input =>
          h_groups group' (by simp [h_group']) action h_action memo input)

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
theorem mem_lower_bind_of_action_exists_mem
  [DecidableEq α']
  {δ : Type u}
  (p : Parser (tag := tag) β List δ)
  (k : δ → ParserM (tag := tag) β List α')
  (split : ℕ) (values : List δ) (a : δ)
  (memo : MemoData tag List) (input : Array β)
  (start end_pos : ℕ) (x : α')
  (h_witness :
    ∃ prePairs postPairs preValues postValues,
      ((p start) memo input).1.toList =
        prePairs ++ (split, values) :: postPairs ∧
      values = preValues ++ a :: postValues ∧
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
  rcases h_witness with ⟨prePairs, postPairs, preValues, postValues,
    h_toList, h_values, h_mem⟩
  exact mem_lower_bind_of_action_mem
    (tag := tag) (β := β) (p := p) (k := k)
    (prePairs := prePairs) (postPairs := postPairs)
    (split := split) (values := values)
    (preValues := preValues) (postValues := postValues)
    (a := a) (memo := memo) (input := input) (start := start)
    (end_pos := end_pos) (x := x)
    h_toList h_values h_mem

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
omit α [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] [DecidableEq α] in
theorem mem_lower_bind_iff_exists_action_split_mem
  [DecidableEq α']
  {δ : Type u}
  (p : Parser (tag := tag) β List δ)
  (k : δ → ParserM (tag := tag) β List α')
  (memo : MemoData tag List) (input : Array β)
  (start end_pos : ℕ) (x : α') :
    x ∈ (((ParserM.Bind p k).lower start) memo input).1.getD end_pos [] ↔
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
  constructor
  · intro h
    exact mem_lower_bind_exists_action_split_mem
      (tag := tag) (β := β)
      (p := p) (k := k)
      (memo := memo) (input := input)
      (start := start) (end_pos := end_pos)
      (x := x) h
  · intro h
    rcases h with ⟨prePairs, postPairs, split, values, preValues, postValues,
      a, h_toList, h_values, h_mem⟩
    exact mem_lower_bind_of_action_mem
      (tag := tag) (β := β)
      (p := p) (k := k)
      (prePairs := prePairs) (postPairs := postPairs)
      (split := split) (values := values)
      (preValues := preValues) (postValues := postValues)
      (a := a) (memo := memo) (input := input)
      (start := start) (end_pos := end_pos) (x := x)
      h_toList h_values h_mem

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
      have h_return := (mem_lower_return_iff
        (tag := tag) (β := β)
        (a := a) (x := x)
        (memo := memo) (input := input)
        (start := start) (end_pos := end_pos)).mp h
      exact (mem_lower_return_iff
        (tag := tag) (β := β)
        (a := f a) (x := f x)
        (memo := memo) (input := input)
        (start := start) (end_pos := end_pos)).mpr
        ⟨h_return.1, by simp [h_return.2]⟩
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
      have h_return := (mem_lower_return_iff
        (tag := tag) (β := β)
        (a := f a) (x := y)
        (memo := memo) (input := input)
        (start := start) (end_pos := end_pos)).mp h
      refine ⟨a, ?_, h_return.2.symm⟩
      exact (mem_lower_return_iff
        (tag := tag) (β := β)
        (a := a) (x := a)
        (memo := memo) (input := input)
        (start := start) (end_pos := end_pos)).mpr
        ⟨h_return.1, rfl⟩
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
theorem runParser_bind_fst_eq_bindContinue
  [DecidableEq α] [DecidableEq α']
  (p : Parser (tag := tag) β List α)
  (k : α → ParserM (tag := tag) β List α')
  (input : Array β)
  (start : ℕ) :
    (runParser (ParserM.Bind p k) input start).1 =
      (Parser.bindContinue (tag := tag) (β := β)
        ((p start) startState input).1
        (fun a => (k a).lower)
        (↑((p start) startState input).2)
        input).1 := by
  rw [runParser_fst_eq_lower]
  change ((Parser.bind p (fun x => (k x).lower) start) startState input).1 =
      (Parser.bindContinue (tag := tag) (β := β)
        ((p start) startState input).1
        (fun a => (k a).lower)
        (↑((p start) startState input).2)
        input).1
  exact parser_bind_fst_eq_bindContinue
    (tag := tag) (β := β)
    (p := p) (f := fun a => (k a).lower)
    (memo := startState) (input := input) (start := start)

set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_runParser_bind_of_action_mem
  [DecidableEq α] [DecidableEq α']
  (p : Parser (tag := tag) β List α)
  (k : α → ParserM (tag := tag) β List α')
  (prePairs postPairs : List (ℕ × List α))
  (split : ℕ) (values preValues postValues : List α) (a : α)
  (input : Array β) (start end_pos : ℕ) (x : α')
  (h_toList : ((p start) startState input).1.toList =
      prePairs ++ (split, values) :: postPairs)
  (h_values : values = preValues ++ a :: postValues)
  (h :
    x ∈ ((k a).lower split
      (↑((Traversable.foldl joinUnderCache
        (List.foldl (Traversable.foldl joinUnderCache)
          (pure Std.HashMap.emptyWithCapacity)
          (List.map
            (fun pair : ℕ × List α =>
              match pair with
              | (j, values) => List.map (fun a => (k a).lower j) values)
            prePairs))
        (List.map (fun a => (k a).lower split) preValues))
        (↑((p start) startState input).2) input).2)
        input).1.getD end_pos []) :
    x ∈ (runParser (ParserM.Bind p k) input start).1.getD end_pos [] := by
  rw [runParser_fst_eq_lower]
  exact mem_lower_bind_of_action_mem
    (tag := tag) (β := β) (p := p) (k := k)
    (prePairs := prePairs) (postPairs := postPairs)
    (split := split) (values := values)
    (preValues := preValues) (postValues := postValues)
    (a := a) (memo := startState) (input := input)
    (start := start) (end_pos := end_pos) (x := x)
    h_toList h_values h

set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_runParser_bind_of_action_exists_mem
  [DecidableEq α] [DecidableEq α']
  (p : Parser (tag := tag) β List α)
  (k : α → ParserM (tag := tag) β List α')
  (split : ℕ) (values : List α) (a : α)
  (input : Array β) (start end_pos : ℕ) (x : α')
  (h_witness :
    ∃ prePairs postPairs preValues postValues,
      ((p start) startState input).1.toList =
        prePairs ++ (split, values) :: postPairs ∧
      values = preValues ++ a :: postValues ∧
      x ∈ ((k a).lower split
        (↑((Traversable.foldl joinUnderCache
          (List.foldl (Traversable.foldl joinUnderCache)
            (pure Std.HashMap.emptyWithCapacity)
            (List.map
              (fun pair : ℕ × List α =>
                match pair with
                | (j, values) => List.map (fun a => (k a).lower j) values)
              prePairs))
          (List.map (fun a => (k a).lower split) preValues))
          (↑((p start) startState input).2) input).2)
        input).1.getD end_pos []) :
    x ∈ (runParser (ParserM.Bind p k) input start).1.getD end_pos [] := by
  rcases h_witness with ⟨prePairs, postPairs, preValues, postValues,
    h_toList, h_values, h_mem⟩
  rw [runParser_fst_eq_lower]
  exact mem_lower_bind_of_action_mem
    (tag := tag) (β := β) (p := p) (k := k)
    (prePairs := prePairs) (postPairs := postPairs)
    (split := split) (values := values)
    (preValues := preValues) (postValues := postValues)
    (a := a) (memo := startState) (input := input) (start := start)
    (end_pos := end_pos) (x := x)
    h_toList h_values h_mem

set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_runParser_bind_of_getElem_action_mem
  [DecidableEq α] [DecidableEq α']
  (p : Parser (tag := tag) β List α)
  (k : α → ParserM (tag := tag) β List α')
  (split : ℕ) (values : List α) (a : α)
  (input : Array β) (start end_pos : ℕ) (x : α')
  (h_get : ((p start) startState input).1[split]? = some values)
  (h_value : a ∈ values)
  (h_action :
    ∀ prePairs postPairs preValues postValues,
      ((p start) startState input).1.toList =
        prePairs ++ (split, values) :: postPairs →
      values = preValues ++ a :: postValues →
      x ∈ ((k a).lower split
        (↑((Traversable.foldl joinUnderCache
          (List.foldl (Traversable.foldl joinUnderCache)
            (pure Std.HashMap.emptyWithCapacity)
            (List.map
              (fun pair : ℕ × List α =>
                match pair with
                | (j, values) => List.map (fun a => (k a).lower j) values)
              prePairs))
          (List.map (fun a => (k a).lower split) preValues))
          (↑((p start) startState input).2) input).2)
        input).1.getD end_pos []) :
    x ∈ (runParser (ParserM.Bind p k) input start).1.getD end_pos [] := by
  rw [runParser_fst_eq_lower]
  exact mem_lower_bind_of_getElem_action_mem
    (tag := tag) (β := β) (p := p) (k := k)
    (split := split) (values := values)
    (a := a) (memo := startState) (input := input) (start := start)
    (end_pos := end_pos) (x := x)
    h_get h_value h_action

set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_runParser_bind_exists_getElem_action_mem
  [DecidableEq α] [DecidableEq α']
  (p : Parser (tag := tag) β List α)
  (k : α → ParserM (tag := tag) β List α')
  (input : Array β)
  (start end_pos : ℕ) (x : α')
  (h :
    x ∈ (runParser (ParserM.Bind p k) input start).1.getD end_pos []) :
    ∃ split values a preGroups preActions postActions postGroups,
      ((p start) startState input).1[split]? = some values ∧
      a ∈ values ∧
      Parser.bindActions (tag := tag) (β := β)
        ((p start) startState input).1
        (fun a => (k a).lower) =
        preGroups ++ (preActions ++ (k a).lower split :: postActions) :: postGroups ∧
      x ∈ (((k a).lower split)
        (↑((Traversable.foldl joinUnderCache
          (List.foldl (Traversable.foldl joinUnderCache)
            (pure Std.HashMap.emptyWithCapacity)
            preGroups)
          preActions)
          (↑((p start) startState input).2) input).2)
        input).1.getD end_pos [] := by
  rw [runParser_fst_eq_lower] at h
  exact mem_lower_bind_exists_getElem_action_mem
    (tag := tag) (β := β) (p := p) (k := k)
    (memo := startState) (input := input)
    (start := start) (end_pos := end_pos) (x := x) h

set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_runParser_bind_exists_action_split_mem
  [DecidableEq α] [DecidableEq α']
  (p : Parser (tag := tag) β List α)
  (k : α → ParserM (tag := tag) β List α')
  (input : Array β)
  (start end_pos : ℕ) (x : α')
  (h :
    x ∈ (runParser (ParserM.Bind p k) input start).1.getD end_pos []) :
    ∃ prePairs postPairs split values preValues postValues a,
      ((p start) startState input).1.toList =
        prePairs ++ (split, values) :: postPairs ∧
      values = preValues ++ a :: postValues ∧
      x ∈ (((k a).lower split)
        (↑((Traversable.foldl joinUnderCache
          (List.foldl (Traversable.foldl joinUnderCache)
            (pure Std.HashMap.emptyWithCapacity)
            (List.map
              (fun pair : ℕ × List α =>
                match pair with
                | (j, values) => List.map (fun a => (k a).lower j) values)
              prePairs))
          (List.map (fun a => (k a).lower split) preValues))
          (↑((p start) startState input).2) input).2)
        input).1.getD end_pos [] := by
  rw [runParser_fst_eq_lower] at h
  exact mem_lower_bind_exists_action_split_mem
    (tag := tag) (β := β)
    (p := p) (k := k)
    (memo := startState) (input := input)
    (start := start) (end_pos := end_pos) (x := x) h

set_option maxHeartbeats 1000000 in
set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_runParser_bind_iff_exists_action_split_mem
  [DecidableEq α] [DecidableEq α']
  (p : Parser (tag := tag) β List α)
  (k : α → ParserM (tag := tag) β List α')
  (input : Array β)
  (start end_pos : ℕ) (x : α') :
    x ∈ (runParser (ParserM.Bind p k) input start).1.getD end_pos [] ↔
      ∃ prePairs postPairs split values preValues postValues a,
        ((p start) startState input).1.toList =
          prePairs ++ (split, values) :: postPairs ∧
        values = preValues ++ a :: postValues ∧
        x ∈ (((k a).lower split)
          (↑((Traversable.foldl joinUnderCache
            (List.foldl (Traversable.foldl joinUnderCache)
              (pure Std.HashMap.emptyWithCapacity)
              (List.map
                (fun pair : ℕ × List α =>
                  match pair with
                  | (j, values) => List.map (fun a => (k a).lower j) values)
                prePairs))
            (List.map (fun a => (k a).lower split) preValues))
            (↑((p start) startState input).2) input).2)
          input).1.getD end_pos [] := by
  rw [runParser_fst_eq_lower]
  exact mem_lower_bind_iff_exists_action_split_mem
    (tag := tag) (β := β)
    (p := p) (k := k)
    (memo := startState) (input := input)
    (start := start) (end_pos := end_pos) (x := x)

set_option maxHeartbeats 800000 in
set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_runParser_lift_map_of_mem
  [DecidableEq α] [DecidableEq α']
  (p : Parser (tag := tag) β List α)
  (f : α → α')
  (input : Array β) (start end_pos : ℕ) (x : α)
  (h : x ∈ ((p start) startState input).1.getD end_pos []) :
    f x ∈ (runParser (f <$> ParserM.lift p) input start).1.getD end_pos [] := by
  rw [Std.HashMap.getD_eq_getD_getElem?] at h
  cases h_opt : ((p start) startState input).1[end_pos]? with
  | none =>
      simp [h_opt] at h
  | some values =>
      simp [h_opt] at h
      change f x ∈
        (runParser
          (ParserM.Bind p
            (fun a => (pure (f a) : ParserM (tag := tag) β List α')))
          input start).1.getD end_pos []
      exact mem_runParser_bind_of_getElem_action_mem
        (tag := tag) (β := β)
        (p := p)
        (k := fun a => (pure (f a) : ParserM (tag := tag) β List α'))
        (split := end_pos) (values := values) (a := x)
        (input := input) (start := start) (end_pos := end_pos)
        (x := f x)
        h_opt h
        (by
          intro prePairs postPairs preValues postValues _h_toList _h_values
          exact (mem_lower_return_iff
            (tag := tag) (β := β)
            (a := f x) (x := f x)
            (memo := ↑((Traversable.foldl joinUnderCache
              (List.foldl (Traversable.foldl joinUnderCache)
                (pure Std.HashMap.emptyWithCapacity)
                (List.map
                  (fun pair : ℕ × List α =>
                    match pair with
                    | (j, values) =>
                        List.map
                          (fun a =>
                            ((pure (f a) : ParserM (tag := tag) β List α').lower j))
                          values)
                  prePairs))
              (List.map
                (fun a => ((pure (f a) : ParserM (tag := tag) β List α').lower end_pos))
                preValues))
              (↑((p start) startState input).2) input).2)
            (input := input) (start := end_pos) (end_pos := end_pos)).mpr
            ⟨rfl, rfl⟩)

set_option maxHeartbeats 800000 in
set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_runParser_lift_map_exists_of_mem
  [DecidableEq α] [DecidableEq α']
  (p : Parser (tag := tag) β List α)
  (f : α → α')
  (input : Array β) (start end_pos : ℕ) (y : α')
  (h : y ∈ (runParser (f <$> ParserM.lift p) input start).1.getD end_pos []) :
    ∃ x, x ∈ ((p start) startState input).1.getD end_pos [] ∧ f x = y := by
  change y ∈
    (runParser
      (ParserM.Bind p
        (fun a => (pure (f a) : ParserM (tag := tag) β List α')))
      input start).1.getD end_pos [] at h
  obtain ⟨split, values, a, preGroups, preActions, postActions, postGroups,
    h_get, h_a_mem, _h_actions, h_action⟩ :=
    mem_runParser_bind_exists_getElem_action_mem
      (tag := tag) (β := β)
      (p := p)
      (k := fun a => (pure (f a) : ParserM (tag := tag) β List α'))
      (input := input) (start := start) (end_pos := end_pos) (x := y) h
  have h_return := (mem_lower_return_iff
    (tag := tag) (β := β)
    (a := f a) (x := y)
    (memo := ↑((Traversable.foldl joinUnderCache
      (List.foldl (Traversable.foldl joinUnderCache)
        (pure Std.HashMap.emptyWithCapacity)
        preGroups)
      preActions)
      (↑((p start) startState input).2) input).2)
    (input := input) (start := split) (end_pos := end_pos)).mp h_action
  cases h_return.1
  refine ⟨a, ?_, h_return.2.symm⟩
  rw [Std.HashMap.getD_eq_getD_getElem?]
  simp [h_get, h_a_mem]

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
  have h_return := (mem_lower_return_iff
    (tag := tag) (β := β)
    (a := a) (x := x)
    (memo := ↑((Traversable.foldl joinUnderCache
      (List.foldl (Traversable.foldl joinUnderCache)
        (pure Std.HashMap.emptyWithCapacity)
        _preGroups)
      _preActions)
      (↑((p start) memo input).2) input).2)
    (input := input) (start := split) (end_pos := end_pos)).mp h_action
  cases h_return.1
  cases h_return.2
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
theorem memoizeStep_empty_fst_eq_compute
  (g : ((t : τ) → ParserM (tag := tag) β List (tag t)) →
      (t : τ) → ParserM (tag := tag) β List (tag t))
  (t : τ) (input : Array β) (start : ℕ) :
    (memoizeStep (Counter.empty : Counter τ) g t
      (fun fuel => memoize ((Counter.empty : Counter τ).dec t fuel) g)
      start startState input).1 =
      (((g (memoize ((Counter.empty : Counter τ).dec t (input.size - start + 1)) g) t).lower start)
        startState input).1 := by
  apply memoizeStep_compute_fst_eq
  simp [startState, Counter.empty, Bot.bot]

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
omit [Monad μ] [Traversable μ] [SemilatticeAlt μ] [DecidableEq α] in
theorem mem_memoize_startState_of_body_mem
  (counter : Counter τ)
  (g : ((t : τ) → ParserM (tag := tag) β List (tag t)) →
      (t : τ) → ParserM (tag := tag) β List (tag t))
  (t : τ) (input : Array β) (start end_pos : ℕ) (x : tag t)
  (h_counter : counter[t]? ≠ some 0)
  (h :
    x ∈ (runParser
      (g (memoize (counter.dec t (input.size - start + 1)) g) t)
      input start).1.getD end_pos []) :
    x ∈ (runParser (memoize counter g t)
      input start).1.getD end_pos [] := by
  rw [runParser_fst_eq_lower] at h
  rw [runParser_fst_eq_lower]
  rw [memoize]
  simp only [h_counter, ↓reduceDIte]
  apply mem_lower_lift_of_mem
  unfold memoizeStep
  simp [startState, Bot.bot]
  exact h

set_option linter.unusedSectionVars false in
omit [Monad μ] [Traversable μ] [SemilatticeAlt μ] [DecidableEq α] in
theorem mem_body_of_memoize_startState_mem
  (counter : Counter τ)
  (g : ((t : τ) → ParserM (tag := tag) β List (tag t)) →
      (t : τ) → ParserM (tag := tag) β List (tag t))
  (t : τ) (input : Array β) (start end_pos : ℕ) (x : tag t)
  (h_counter : counter[t]? ≠ some 0)
  (h :
    x ∈ (runParser (memoize counter g t)
      input start).1.getD end_pos []) :
    x ∈ (runParser
      (g (memoize (counter.dec t (input.size - start + 1)) g) t)
      input start).1.getD end_pos [] := by
  rw [runParser_fst_eq_lower] at h
  rw [runParser_fst_eq_lower]
  rw [memoize] at h
  simp only [h_counter, ↓reduceDIte] at h
  have h_step :
      x ∈ ((memoizeStep counter g t
          (fun fuel => memoize (counter.dec t fuel) g)
          start startState input).1.getD end_pos []) := by
    exact mem_lower_lift_exists_of_mem
      (tag := tag) (β := β)
      (p := memoizeStep counter g t
        (fun fuel => memoize (counter.dec t fuel) g))
      (memo := startState) (input := input)
      (start := start) (end_pos := end_pos) (x := x) h
  unfold memoizeStep at h_step
  simpa [startState, Bot.bot] using h_step

set_option linter.unusedSectionVars false in
omit [Monad μ] [Traversable μ] [SemilatticeAlt μ] [DecidableEq α] in
theorem mem_memoize_empty_of_body_mem
  (g : ((t : τ) → ParserM (tag := tag) β List (tag t)) →
      (t : τ) → ParserM (tag := tag) β List (tag t))
  (t : τ) (input : Array β) (start end_pos : ℕ) (x : tag t)
  (h :
    x ∈ (runParser
      (g (memoize ((Counter.empty : Counter τ).dec t (input.size - start + 1)) g) t)
      input start).1.getD end_pos []) :
    x ∈ (runParser (memoize (Counter.empty : Counter τ) g t)
      input start).1.getD end_pos [] := by
  have h_counter : (Counter.empty : Counter τ)[t]? ≠ some 0 := by
    change (Std.HashMap.emptyWithCapacity : Std.HashMap τ ℕ)[t]? ≠ some 0
    simp
  rw [runParser_fst_eq_lower] at h
  rw [runParser_fst_eq_lower]
  rw [memoize]
  simp only [h_counter, ↓reduceDIte]
  change x ∈ (((ParserM.lift (memoizeStep (Counter.empty : Counter τ) g t
      (fun fuel => memoize ((Counter.empty : Counter τ).dec t fuel) g))).lower start)
      startState input).1.getD end_pos []
  apply mem_lower_lift_of_mem
  unfold memoizeStep
  simp [startState, Counter.empty, Bot.bot]
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
theorem parser_orElse_fst_eq_unionSup
  [DecidableEq α]
  (p q : Parser (tag := tag) β List α)
  (memo : MemoData tag List) (input : Array β)
  (start : ℕ) :
    ((Parser.orElse p q start) memo input).1 =
      ((p start) memo input).1.unionSup
        ((q start) (↑((p start) memo input).2) input).1 := by
  unfold Parser.orElse joinUnderCache liftA2
  simp only [ReaderT.instApplicativeOfMonad, ReaderT.instMonad, instMonadMStateT,
    ReaderT.bind, ReaderT.pure, Id.instMonad, Function.comp_apply]

set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_parser_orElse_iff
  [DecidableEq α]
  (p q : Parser (tag := tag) β List α)
  (memo : MemoData tag List) (input : Array β)
  (start end_pos : ℕ) (x : α) :
    x ∈ ((Parser.orElse p q start) memo input).1.getD end_pos [] ↔
      x ∈ ((p start) memo input).1.getD end_pos [] ∨
      x ∈ ((q start) (↑((p start) memo input).2) input).1.getD end_pos [] := by
  constructor
  · exact mem_parser_orElse_or
      (tag := tag) (β := β)
      p q memo input start end_pos x
  · intro h
    cases h with
    | inl h_left =>
        exact mem_parser_orElse_left_of_mem
          (tag := tag) (β := β)
          p q memo input start end_pos x h_left
    | inr h_right =>
        exact mem_parser_orElse_right_after_left_of_mem
          (tag := tag) (β := β)
          p q memo input start end_pos x h_right

set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_runParser_sup_left
  [DecidableEq α]
  (p q : ParserM (tag := tag) β List α)
  (input : Array β) (start end_pos : ℕ) (x : α)
  (h : x ∈ (runParser p input start).1.getD end_pos []) :
    x ∈ (runParser (p ⊔ q) input start).1.getD end_pos [] := by
  rw [runParser_fst_eq_lower] at h
  rw [runParser_fst_eq_lower]
  cases p with
  | Return a =>
      cases q with
      | Return b =>
          unfold Max.max ParserM.instMaxOfTraversableOfDecidableEq ParserM.lower Parser.bind
          apply mem_parser_bind_return_of_mem
          exact mem_parser_orElse_left_of_mem (tag := tag) (β := β)
            (pure a) (pure b) startState input start end_pos x h
      | Bind q k =>
          unfold Max.max ParserM.instMaxOfTraversableOfDecidableEq ParserM.lift ParserM.lower
          apply mem_parser_bind_return_of_mem
          exact mem_parser_orElse_left_of_mem (tag := tag) (β := β)
            (pure a) (q.bind (ParserM.lower ∘ k)) startState input start end_pos x h
  | Bind p k =>
      cases q with
      | Return b =>
          unfold Max.max ParserM.instMaxOfTraversableOfDecidableEq ParserM.lift ParserM.lower
          apply mem_parser_bind_return_of_mem
          exact mem_parser_orElse_left_of_mem (tag := tag) (β := β)
            (p.bind (ParserM.lower ∘ k)) (pure b) startState input start end_pos x h
      | Bind q kq =>
          unfold Max.max ParserM.instMaxOfTraversableOfDecidableEq ParserM.lift ParserM.lower
          apply mem_parser_bind_return_of_mem
          exact mem_parser_orElse_left_of_mem (tag := tag) (β := β)
            (p.bind (ParserM.lower ∘ k)) (q.bind (ParserM.lower ∘ kq))
            startState input start end_pos x h

set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_runParser_sup_right_after_left_of_mem
  [DecidableEq α]
  (p q : ParserM (tag := tag) β List α)
  (input : Array β) (start end_pos : ℕ) (x : α)
  (h : x ∈ ((q.lower start) (↑(((p.lower start) startState input).2)) input).1.getD end_pos []) :
    x ∈ (runParser (p ⊔ q) input start).1.getD end_pos [] := by
  rw [runParser_fst_eq_lower]
  cases p with
  | Return a =>
      cases q with
      | Return b =>
          unfold Max.max ParserM.instMaxOfTraversableOfDecidableEq ParserM.lower Parser.bind
          apply mem_parser_bind_return_of_mem
          exact mem_parser_orElse_right_after_left_of_mem (tag := tag) (β := β)
            (pure a) (pure b) startState input start end_pos x h
      | Bind q k =>
          unfold Max.max ParserM.instMaxOfTraversableOfDecidableEq ParserM.lift ParserM.lower
          apply mem_parser_bind_return_of_mem
          exact mem_parser_orElse_right_after_left_of_mem (tag := tag) (β := β)
            (pure a) (q.bind (ParserM.lower ∘ k)) startState input start end_pos x h
  | Bind p k =>
      cases q with
      | Return b =>
          unfold Max.max ParserM.instMaxOfTraversableOfDecidableEq ParserM.lift ParserM.lower
          apply mem_parser_bind_return_of_mem
          exact mem_parser_orElse_right_after_left_of_mem (tag := tag) (β := β)
            (p.bind (ParserM.lower ∘ k)) (pure b) startState input start end_pos x h
      | Bind q kq =>
          unfold Max.max ParserM.instMaxOfTraversableOfDecidableEq ParserM.lift ParserM.lower
          apply mem_parser_bind_return_of_mem
          exact mem_parser_orElse_right_after_left_of_mem (tag := tag) (β := β)
            (p.bind (ParserM.lower ∘ k)) (q.bind (ParserM.lower ∘ kq))
            startState input start end_pos x h

set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_runParser_sup_or
  [DecidableEq α]
  (p q : ParserM (tag := tag) β List α)
  (input : Array β) (start end_pos : ℕ) (x : α)
  (h : x ∈ (runParser (p ⊔ q) input start).1.getD end_pos []) :
    x ∈ (runParser p input start).1.getD end_pos [] ∨
    x ∈ ((q.lower start) (↑(((p.lower start) startState input).2)) input).1.getD end_pos [] := by
  rw [runParser_fst_eq_lower] at h
  cases p with
  | Return a =>
      cases q with
      | Return b =>
          unfold Max.max ParserM.instMaxOfTraversableOfDecidableEq ParserM.lower Parser.bind at h
          have h_or := mem_parser_orElse_or (tag := tag) (β := β)
            (pure a) (pure b) startState input start end_pos x
            (mem_parser_bind_return_exists_of_mem (tag := tag) (β := β)
              (p := Parser.orElse (pure a) (pure b))
              (memo := startState) (input := input)
              (start := start) (end_pos := end_pos) (x := x) h)
          cases h_or with
          | inl h_left =>
              left
              rw [runParser_fst_eq_lower]
              simpa [ParserM.lower] using h_left
          | inr h_right =>
              right
              simpa [ParserM.lower] using h_right
      | Bind q k =>
          unfold Max.max ParserM.instMaxOfTraversableOfDecidableEq ParserM.lift ParserM.lower at h
          have h_or := mem_parser_orElse_or (tag := tag) (β := β)
            (pure a) (q.bind (ParserM.lower ∘ k)) startState input start end_pos x
            (mem_lower_lift_exists_of_mem (tag := tag) (β := β)
              (p := Parser.orElse (pure a) (q.bind (ParserM.lower ∘ k)))
              (memo := startState) (input := input)
              (start := start) (end_pos := end_pos) (x := x) h)
          cases h_or with
          | inl h_left =>
              left
              rw [runParser_fst_eq_lower]
              simpa [ParserM.lower] using h_left
          | inr h_right =>
              right
              simpa [ParserM.lower, Function.comp_apply] using h_right
  | Bind p k =>
      cases q with
      | Return b =>
          unfold Max.max ParserM.instMaxOfTraversableOfDecidableEq ParserM.lift ParserM.lower at h
          have h_or := mem_parser_orElse_or (tag := tag) (β := β)
            (p.bind (ParserM.lower ∘ k)) (pure b) startState input start end_pos x
            (mem_lower_lift_exists_of_mem (tag := tag) (β := β)
              (p := Parser.orElse (p.bind (ParserM.lower ∘ k)) (pure b))
              (memo := startState) (input := input)
              (start := start) (end_pos := end_pos) (x := x) h)
          cases h_or with
          | inl h_left =>
              left
              rw [runParser_fst_eq_lower]
              simpa [ParserM.lower, Function.comp_apply] using h_left
          | inr h_right =>
              right
              simpa [ParserM.lower] using h_right
      | Bind q kq =>
          unfold Max.max ParserM.instMaxOfTraversableOfDecidableEq ParserM.lift ParserM.lower at h
          have h_or := mem_parser_orElse_or (tag := tag) (β := β)
            (p.bind (ParserM.lower ∘ k)) (q.bind (ParserM.lower ∘ kq))
            startState input start end_pos x
            (mem_lower_lift_exists_of_mem (tag := tag) (β := β)
              (p := Parser.orElse
                (p.bind (ParserM.lower ∘ k))
                (q.bind (ParserM.lower ∘ kq)))
              (memo := startState) (input := input)
              (start := start) (end_pos := end_pos) (x := x) h)
          cases h_or with
          | inl h_left =>
              left
              rw [runParser_fst_eq_lower]
              simpa [ParserM.lower, Function.comp_apply] using h_left
          | inr h_right =>
              right
              simpa [ParserM.lower, Function.comp_apply] using h_right

set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_runParser_sup_iff_after_left
  [DecidableEq α]
  (p q : ParserM (tag := tag) β List α)
  (input : Array β) (start end_pos : ℕ) (x : α) :
    x ∈ (runParser (p ⊔ q) input start).1.getD end_pos [] ↔
      x ∈ (runParser p input start).1.getD end_pos [] ∨
      x ∈ ((q.lower start)
        (↑(((p.lower start) startState input).2)) input).1.getD end_pos [] := by
  constructor
  · exact mem_runParser_sup_or
      (tag := tag) (β := β)
      p q input start end_pos x
  · intro h
    cases h with
    | inl h_left =>
        exact mem_runParser_sup_left
          (tag := tag) (β := β)
          p q input start end_pos x h_left
    | inr h_right =>
        exact mem_runParser_sup_right_after_left_of_mem
          (tag := tag) (β := β)
          p q input start end_pos x h_right

set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_lower_sup_left
  [DecidableEq α]
  (p q : ParserM (tag := tag) β List α)
  (memo : MemoData tag List) (input : Array β)
  (start end_pos : ℕ) (x : α)
  (h : x ∈ ((p.lower start) memo input).1.getD end_pos []) :
    x ∈ (((p ⊔ q).lower start) memo input).1.getD end_pos [] := by
  cases p with
  | Return a =>
      cases q with
      | Return b =>
          unfold Max.max ParserM.instMaxOfTraversableOfDecidableEq ParserM.lower Parser.bind
          apply mem_parser_bind_return_of_mem
          exact mem_parser_orElse_left_of_mem (tag := tag) (β := β)
            (pure a) (pure b) memo input start end_pos x h
      | Bind q k =>
          unfold Max.max ParserM.instMaxOfTraversableOfDecidableEq ParserM.lift ParserM.lower
          apply mem_parser_bind_return_of_mem
          exact mem_parser_orElse_left_of_mem (tag := tag) (β := β)
            (pure a) (q.bind (ParserM.lower ∘ k)) memo input start end_pos x h
  | Bind p k =>
      cases q with
      | Return b =>
          unfold Max.max ParserM.instMaxOfTraversableOfDecidableEq ParserM.lift ParserM.lower
          apply mem_parser_bind_return_of_mem
          exact mem_parser_orElse_left_of_mem (tag := tag) (β := β)
            (p.bind (ParserM.lower ∘ k)) (pure b) memo input start end_pos x h
      | Bind q kq =>
          unfold Max.max ParserM.instMaxOfTraversableOfDecidableEq ParserM.lift ParserM.lower
          apply mem_parser_bind_return_of_mem
          exact mem_parser_orElse_left_of_mem (tag := tag) (β := β)
            (p.bind (ParserM.lower ∘ k)) (q.bind (ParserM.lower ∘ kq))
            memo input start end_pos x h

set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_lower_sup_right_after_left_of_mem
  [DecidableEq α]
  (p q : ParserM (tag := tag) β List α)
  (memo : MemoData tag List) (input : Array β)
  (start end_pos : ℕ) (x : α)
  (h : x ∈ ((q.lower start) (↑(((p.lower start) memo input).2)) input).1.getD end_pos []) :
    x ∈ (((p ⊔ q).lower start) memo input).1.getD end_pos [] := by
  cases p with
  | Return a =>
      cases q with
      | Return b =>
          unfold Max.max ParserM.instMaxOfTraversableOfDecidableEq ParserM.lower Parser.bind
          apply mem_parser_bind_return_of_mem
          exact mem_parser_orElse_right_after_left_of_mem (tag := tag) (β := β)
            (pure a) (pure b) memo input start end_pos x h
      | Bind q k =>
          unfold Max.max ParserM.instMaxOfTraversableOfDecidableEq ParserM.lift ParserM.lower
          apply mem_parser_bind_return_of_mem
          exact mem_parser_orElse_right_after_left_of_mem (tag := tag) (β := β)
            (pure a) (q.bind (ParserM.lower ∘ k)) memo input start end_pos x h
  | Bind p k =>
      cases q with
      | Return b =>
          unfold Max.max ParserM.instMaxOfTraversableOfDecidableEq ParserM.lift ParserM.lower
          apply mem_parser_bind_return_of_mem
          exact mem_parser_orElse_right_after_left_of_mem (tag := tag) (β := β)
            (p.bind (ParserM.lower ∘ k)) (pure b) memo input start end_pos x h
      | Bind q kq =>
          unfold Max.max ParserM.instMaxOfTraversableOfDecidableEq ParserM.lift ParserM.lower
          apply mem_parser_bind_return_of_mem
          exact mem_parser_orElse_right_after_left_of_mem (tag := tag) (β := β)
            (p.bind (ParserM.lower ∘ k)) (q.bind (ParserM.lower ∘ kq))
            memo input start end_pos x h

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
  · exact mem_lower_sup_or
      (tag := tag) (β := β)
      p q memo input start end_pos x
  · intro h
    cases h with
    | inl h_left =>
        exact mem_lower_sup_left
          (tag := tag) (β := β)
          p q memo input start end_pos x h_left
    | inr h_right =>
        exact mem_lower_sup_right_after_left_of_mem
          (tag := tag) (β := β)
          p q memo input start end_pos x h_right

omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem joinUnderCache_empty_pure_singleton_mem_iff
  [DecidableEq β]
  (a x : β) (input : Array β) (start end_pos : ℕ)
  (s : MemoData tag List) :
  x ∈ (joinUnderCache
      (fun s => ReaderT.pure (Std.HashMap.emptyWithCapacity, ⟨s, le_refl s⟩))
      ((ParserM.Return (tag := tag) (β := β) (μ := List) a).lower (start + 1))
      s input).1.getD end_pos [] ↔
    end_pos = start + 1 ∧ x = a := by
  unfold joinUnderCache liftA2 ParserM.lower
  simp only [ReaderT.instFunctorOfMonad, ReaderT.instApplicativeOfMonad,
    ReaderT.instMonad, ReaderT.bind, ReaderT.pure, instMonadMStateT]
  simp only [Id.instMonad, Function.comp_apply, Pure.pure, ReaderT.pure]
  let singleton : Std.HashMap ℕ (List β) :=
    (Std.HashMap.emptyWithCapacity : Std.HashMap ℕ (List β)).insert (start + 1) [a]
  let m : Std.HashMap ℕ (List β) :=
    Std.HashMap.emptyWithCapacity.unionSup singleton
  change x ∈ m.getD end_pos [] ↔ end_pos = start + 1 ∧ x = a
  have h_equiv :
      Quotient.mk (List.memSetoid β) (m.getD end_pos []) =
        Quotient.mk (List.memSetoid β) (singleton.getD end_pos []) := by
    exact Std.HashMap.EquivQuot.getD_eq
      (s := List.memSetoid β)
      (k := end_pos) (fallback := [])
      (Std.HashMap.empty_unionSup_equiv_self
        (s := List.memSetoid β)
        (semi := List.instSemilatticeAlt.instSemilatticeoidInstSetoid)
        singleton)
  simp [List.memSetoid] at h_equiv
  have h_mem_iff :
      x ∈ m.getD end_pos [] ↔ x ∈ singleton.getD end_pos [] := by
    exact ⟨fun h => h_equiv.1 h, fun h => h_equiv.2 h⟩
  rw [h_mem_iff]
  by_cases h_end : end_pos = start + 1
  · subst h_end
    rw [Std.HashMap.getD_eq_getD_getElem?]
    simp [singleton]
  · have h_key : start + 1 ≠ end_pos := by
      intro h_eq
      exact h_end h_eq.symm
    rw [Std.HashMap.getD_eq_getD_getElem?]
    simp [singleton, h_end, h_key]

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
  simp only [ge_iff_le, Nat.zero_le, decide_true, Bool.true_and]
  simp only [readThe, MonadReader.read, MonadReaderOf.read,
    ReaderT.read, liftM, monadLift, MonadLift.monadLift]
  simp only [instMonadMStateT]
  simp only [ReaderT.instMonad, ReaderT.bind, Id.instMonad, Pure.pure,
    ReaderT.pure]
  by_cases h_match : some a = input[start]?
  · simp [h_match, readerT_pure_snd]
  · simp [h_match, readerT_pure_snd]

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
  simp only [ge_iff_le, Nat.zero_le, decide_true, Bool.true_and]
  simp only [readThe, MonadReader.read, MonadReaderOf.read,
    ReaderT.read, liftM, monadLift, MonadLift.monadLift]
  simp only [instMonadMStateT]
  simp only [ReaderT.instMonad, ReaderT.bind, Id.instMonad, Pure.pure,
    ReaderT.pure]
  by_cases h_match : some a = input[start]?
  · simp only [h_match, decide_true, if_true]
    rw [readerT_pure_fst]
    rw [Std.HashMap.getD_eq_getD_getElem?]
    by_cases h_end : end_pos = start + 1
    · subst h_end
      simp
    · have h_key : start + 1 ≠ end_pos := by
        intro h_eq
        exact h_end h_eq.symm
      simp [h_end, h_key]
  · simp only [h_match, decide_false, Bool.false_eq_true, if_false]
    rw [readerT_pure_fst]
    rw [Std.HashMap.getD_eq_getD_getElem?]
    simp

omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_lower_terminal_iff
  [DecidableEq β]
  (a x : β) (input : Array β) (start end_pos : ℕ)
  (memo : MemoData tag List) :
    x ∈ (((terminal' (tag := tag) (μ := List) a).lower start)
      memo input).1.getD end_pos [] ↔
      some a = input[start]? ∧ end_pos = start + 1 ∧ x = a := by
  constructor
  · intro h
    have h_lift :
        x ∈ (((ParserM.lift (terminalPrimitive (tag := tag) a)).lower start)
          memo input).1.getD end_pos [] := by
      simpa [terminal'_eq_lift_terminalPrimitive (tag := tag) (a := a)] using h
    have h_prim :
        x ∈ ((terminalPrimitive (tag := tag) a start) memo input).1.getD end_pos [] :=
      mem_lower_lift_exists_of_mem
        (tag := tag) (β := β)
        (p := terminalPrimitive (tag := tag) a)
        (memo := memo) (input := input)
        (start := start) (end_pos := end_pos) (x := x)
        h_lift
    exact (mem_terminalPrimitive_iff
      (tag := tag) (a := a) (x := x)
      (input := input) (start := start) (end_pos := end_pos)
      (memo := memo)).mp h_prim
  · intro h
    have h_prim :
        x ∈ ((terminalPrimitive (tag := tag) a start) memo input).1.getD end_pos [] :=
      (mem_terminalPrimitive_iff
        (tag := tag) (a := a) (x := x)
        (input := input) (start := start) (end_pos := end_pos)
        (memo := memo)).mpr h
    have h_lift :
        x ∈ (((ParserM.lift (terminalPrimitive (tag := tag) a)).lower start)
          memo input).1.getD end_pos [] :=
      mem_lower_lift_of_mem
        (tag := tag) (β := β)
        (p := terminalPrimitive (tag := tag) a)
        (memo := memo) (input := input)
        (start := start) (end_pos := end_pos) (x := x)
        h_prim
    simpa [terminal'_eq_lift_terminalPrimitive (tag := tag) (a := a)] using h_lift

-- Primitive terminal semantics, stated in the membership form used by soundness proofs.
omit [Fintype τ] in
set_option maxHeartbeats 2000000 in
theorem mem_runParser_terminal_iff
  [DecidableEq β]
  (a x : β) (input : Array β) (start end_pos : ℕ)
  : x ∈ (runParser (tag := tag)
        (terminal' (tag := tag) (μ := List) a) input start).1.getD end_pos [] ↔
      some a = input[start]? ∧ end_pos = start + 1 ∧ x = a
  := by
  unfold runParser terminal' ParserM.lift ParserM.lower Parser.bind Parser.bindRun
    Parser.bindContinue Parser.bindActions MStateT.run
  simp only [ge_iff_le, Nat.zero_le, decide_true, Bool.true_and]
  simp only [readThe, MonadReader.read, MonadReaderOf.read,
    ReaderT.read, liftM, monadLift, MonadLift.monadLift]
  simp only [instMonadMStateT]
  simp only [ReaderT.instFunctorOfMonad, ReaderT.instApplicativeOfMonad,
    ReaderT.instMonad, ReaderT.bind, ReaderT.pure]
  unfold ReaderT.run
  simp only [Id.instMonad]
  by_cases h_match : some a = input[start]?
  · simp only [h_match, decide_true, if_true]
    rw [prod_fst_bifunctor_snd]
    simp only [readerT_pure_fst]
    rw [hashMap_singleton_toList_eq_singleton]
    simp only [List.instSemilatticeAlt, List.instAlternative, List.instMonad, Functor.map]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    rw [traversable_foldl_singleton]
    rw [joinUnderCache_empty_pure_singleton_mem_iff]
    simp
  · simp only [h_match, decide_false, Bool.false_eq_true, if_false, ReaderT.pure]
    simp only [hashMap_emptyWithCapacity_toList_eq_nil, List.map_nil, List.foldl_nil]
    rw [prod_fst_bifunctor_snd]
    rw [readerT_pure_fst]
    simp

set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_runParser_map_of_mem
  [DecidableEq α] [DecidableEq α']
  (p : ParserM (tag := tag) β List α)
  (f : α → α')
  (input : Array β) (start end_pos : ℕ) (x : α)
  (h : x ∈ (runParser p input start).1.getD end_pos []) :
    f x ∈ (runParser (f <$> p) input start).1.getD end_pos [] := by
  rw [runParser_fst_eq_lower] at h ⊢
  exact mem_lower_map_of_mem
    (tag := tag) (β := β)
    (p := p) (f := f)
    (memo := startState) (input := input)
    (start := start) (end_pos := end_pos) (x := x) h

set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_runParser_map_exists_of_mem
  [DecidableEq α] [DecidableEq α']
  (p : ParserM (tag := tag) β List α)
  (f : α → α')
  (input : Array β) (start end_pos : ℕ) (y : α')
  (h : y ∈ (runParser (f <$> p) input start).1.getD end_pos []) :
    ∃ x, x ∈ (runParser p input start).1.getD end_pos [] ∧ f x = y := by
  rw [runParser_fst_eq_lower] at h ⊢
  exact mem_lower_map_exists_of_mem
    (tag := tag) (β := β)
    (p := p) (f := f)
    (memo := startState) (input := input)
    (start := start) (end_pos := end_pos) (y := y) h

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
theorem mem_lower_traverse_cons_tail_exists_of_cons
  [DecidableEq α]
  (head : ParserM (tag := tag) β List α)
  (tail : List (ParserM (tag := tag) β List α))
  (memo : MemoData tag List) (input : Array β)
  (start end_pos : ℕ)
  {result_head : α} {result_tail : List α}
  (h :
    result_head :: result_tail ∈
      (((head >>= fun a => List.cons a <$> List.traverse id tail).lower start)
        memo input).1.getD end_pos []) :
    ∃ split memo_tail,
      result_tail ∈
        (((List.traverse id tail).lower split) memo_tail input).1.getD end_pos [] := by
  induction head generalizing memo start end_pos result_head result_tail with
  | Return a =>
      change result_head :: result_tail ∈
        (((List.cons a <$> List.traverse id tail).lower start)
          memo input).1.getD end_pos [] at h
      obtain ⟨h_head_eq, h_tail_mem⟩ :=
        mem_lower_cons_map_exists_of_cons
          (tag := tag) (β := β)
          (tail := tail) (head_result := a)
          (memo := memo) (input := input)
          (split := start) (end_pos := end_pos) h
      cases h_head_eq
      exact ⟨start, memo, h_tail_mem⟩
  | Bind p k ih =>
      change result_head :: result_tail ∈
        (((ParserM.Bind p
          (fun a => k a >>= fun a => List.cons a <$> List.traverse id tail)).lower start)
          memo input).1.getD end_pos [] at h
      obtain ⟨split₀, _values₀, a₀, preGroups, preActions,
        postActions, postGroups, _h_get₀, _h_value₀, h_actions, h_action⟩ :=
        mem_lower_bind_exists_getElem_action_mem
          (tag := tag) (β := β)
          (p := p)
          (k := fun a => k a >>= fun a => List.cons a <$> List.traverse id tail)
          (memo := memo) (input := input)
          (start := start) (end_pos := end_pos)
          (x := result_head :: result_tail) h
      exact ih a₀
        (memo := _)
        (start := split₀) (end_pos := end_pos)
        (result_head := result_head) (result_tail := result_tail)
        h_action

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
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_lower_traverse_cons_bind_return_exists_head_tail
  [DecidableEq α']
  (p : Parser (tag := tag) β List α)
  (f : α → α')
  (tail : List (ParserM (tag := tag) β List α'))
  (memo : MemoData tag List) (input : Array β)
  (start end_pos : ℕ)
  {result_head : α'} {result_tail : List α'}
  (h :
    result_head :: result_tail ∈
      (((List.traverse id
        ((ParserM.Bind p
          (fun a => ParserM.Return (tag := tag) (β := β) (μ := List) (f a)) : ParserM (tag := tag) β List α')
          :: tail)).lower start)
        memo input).1.getD end_pos []) :
    ∃ split a memo_tail,
      a ∈ ((p start) memo input).1.getD split [] ∧
      f a = result_head ∧
      result_tail ∈
        (((List.traverse id tail).lower split) memo_tail input).1.getD end_pos [] := by
  rw [List.traverse, seq_eq_bind] at h
  simp at h
  change result_head :: result_tail ∈
    (((ParserM.Bind p
      (fun a => List.cons (f a) <$> List.traverse id tail)).lower start)
      memo input).1.getD end_pos [] at h
  obtain ⟨split, values, a, _preGroups, _preActions,
    _postActions, _postGroups, h_get, h_value, _h_actions, h_action⟩ :=
    mem_lower_bind_exists_getElem_action_mem
      (tag := tag) (β := β)
      (p := p)
      (k := fun a => List.cons (f a) <$> List.traverse id tail)
      (memo := memo) (input := input)
      (start := start) (end_pos := end_pos)
      (x := result_head :: result_tail) h
  obtain ⟨h_head_eq, h_tail_mem⟩ :=
    mem_lower_cons_map_exists_of_cons
      (tag := tag) (β := β)
      (tail := tail) (head_result := f a)
      (memo := _) (input := input)
      (split := split) (end_pos := end_pos)
      h_action
  refine ⟨split, a, _, ?_, ?_, h_tail_mem⟩
  · rw [Std.HashMap.getD_eq_getD_getElem?]
    simp [h_get, h_value]
  · exact h_head_eq.symm

set_option maxHeartbeats 1000000 in
set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem not_mem_lower_traverse_cons_nil
  [DecidableEq α]
  (head : ParserM (tag := tag) β List α)
  (tail : List (ParserM (tag := tag) β List α))
  (memo : MemoData tag List) (input : Array β)
  (start end_pos : ℕ)
  (h :
    ([] : List α) ∈
      (((head >>= fun a => List.cons a <$> List.traverse id tail).lower start)
        memo input).1.getD end_pos []) :
    False := by
  induction head generalizing memo start end_pos with
  | Return a =>
      change ([] : List α) ∈
        (((List.cons a <$> List.traverse id tail).lower start)
          memo input).1.getD end_pos [] at h
      exact not_mem_lower_cons_map_nil
        (tag := tag) (β := β)
        (tail := tail) (head_result := a)
        (memo := memo) (input := input)
        (split := start) (end_pos := end_pos) h
  | Bind p k ih =>
      change ([] : List α) ∈
        (((ParserM.Bind p
          (fun a => k a >>= fun a => List.cons a <$> List.traverse id tail)).lower start)
          memo input).1.getD end_pos [] at h
      obtain ⟨split, _values, a, _preGroups, _preActions,
        _postActions, _postGroups, _h_get, _h_value, _h_actions, h_action⟩ :=
        mem_lower_bind_exists_getElem_action_mem
          (tag := tag) (β := β)
          (p := p)
          (k := fun a => k a >>= fun a => List.cons a <$> List.traverse id tail)
          (memo := memo) (input := input)
          (start := start) (end_pos := end_pos)
          (x := ([] : List α)) h
      exact ih a
        (memo := _)
        (start := split) (end_pos := end_pos) h_action

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

set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem mem_bind_cons_map_exists_of_cons
  [DecidableEq α]
  (tail : List (ParserM (tag := tag) β List α))
  (input : Array β) (split end_pos : ℕ)
  {s : List α} {result_head : α} {result_tail : List α}
  (h :
    result_head :: result_tail ∈
      s >>= fun a =>
        (runParser (tag := tag)
          (List.cons a <$> List.traverse id tail) input split).1[end_pos]?.toList.flatten) :
    ∃ head_result,
      head_result ∈ s ∧
      result_head = head_result ∧
      result_tail ∈
        (runParser (tag := tag) (List.traverse id tail) input split).1.getD end_pos [] := by
  rw [List.bind_eq_flatMap] at h
  obtain ⟨head_result, h_head_mem, h_mapped⟩ := List.mem_flatMap.mp h
  have h_mapped_getD :
      result_head :: result_tail ∈
        (runParser (tag := tag)
          (List.cons head_result <$> List.traverse id tail) input split).1.getD end_pos [] := by
    exact mem_resultMap_getD_of_mem_getElem?_toList_flatten
      ((runParser (tag := tag)
        (List.cons head_result <$> List.traverse id tail) input split).1)
      h_mapped
  rw [runParser_fst_eq_lower] at h_mapped_getD
  obtain ⟨h_head_eq, h_tail_mem⟩ := mem_lower_cons_map_exists_of_cons
    (tag := tag) (β := β)
    (tail := tail) (head_result := head_result)
    (memo := startState) (input := input)
    (split := split) (end_pos := end_pos) h_mapped_getD
  cases h_head_eq
  rw [← runParser_fst_eq_lower] at h_tail_mem
  exact ⟨result_head, h_head_mem, rfl, h_tail_mem⟩

set_option linter.unusedSectionVars false in
omit [Fintype τ] [Monad μ] [Traversable μ] [SemilatticeAlt μ] in
theorem not_mem_bind_cons_map_nil
  [DecidableEq α]
  (tail : List (ParserM (tag := tag) β List α))
  (input : Array β) (split end_pos : ℕ)
  {s : List α}
  (h :
    ([] : List α) ∈
      s >>= fun a =>
        (runParser (tag := tag)
          (List.cons a <$> List.traverse id tail) input split).1[end_pos]?.toList.flatten) :
    False := by
  rw [List.bind_eq_flatMap] at h
  obtain ⟨head_result, _h_head_mem, h_mapped⟩ := List.mem_flatMap.mp h
  have h_mapped_getD :
      ([] : List α) ∈
        (runParser (tag := tag)
          (List.cons head_result <$> List.traverse id tail) input split).1.getD end_pos [] := by
    exact mem_resultMap_getD_of_mem_getElem?_toList_flatten
      ((runParser (tag := tag)
        (List.cons head_result <$> List.traverse id tail) input split).1)
      h_mapped
  rw [runParser_fst_eq_lower] at h_mapped_getD
  exact not_mem_lower_cons_map_nil
    (tag := tag) (β := β)
    (tail := tail) (head_result := head_result)
    (memo := startState) (input := input)
    (split := split) (end_pos := end_pos) h_mapped_getD
