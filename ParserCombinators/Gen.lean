/-

Parser generation from CFGs.

-/

import ParserCombinators.CFG
import ParserCombinators.Memoized
import ParserCombinators.Lemmas

namespace Gen

universe u
variable {α ν : Type u} {μ : Type u → Type u} [Monad μ] [SemilatticeAlt μ] [Traversable μ] [BEq α] [DecidableEq α] [DecidableEq ν] [Hashable ν] [Fintype ν]

open CFG
open ParseTree

abbrev tag (cfg : @CFG α ν) := Function.const ν (ParseTree cfg)

instance {cfg : @CFG α ν} (t : ν) : DecidableEq (tag cfg t) := by
  simp only [Function.const_apply]
  infer_instance

-- A generator function for a parser generator that discards the result.
--
-- g: input grammar
-- recur: for recursive calls
-- n: current nonterminal to parse
def gen' (cfg : @CFG α ν) (recur : ν → ParserM (tag := tag cfg) α μ (ParseTree cfg)) (n : ν)
    : ParserM (tag := tag cfg) α μ (ParseTree cfg) :=
  let parseSym (sym : Symbol α ν) : ParserM α μ (ParseTree cfg) := match sym with
    | Symbol.term a => ParseTree.Leaf <$> terminal' a
    | Symbol.nonterm n => recur n
  let parseRule (rule : {rule // rule ∈ cfg.rules n}) : ParserM α μ (ParseTree cfg) := do
    let children := List.map parseSym rule
    ParseTree.Node n rule <$> List.traverse id children
  ((cfg.rules n).attach.map parseRule).foldl ParserM.instMaxOfTraversableOfDecidableEq.max ⊥

def gen (cfg : @CFG α ν) : ν → ParserM (tag := tag cfg) α μ (ParseTree cfg) := memoize (g := gen' cfg)

-- Generated parsers return plain parse trees.  Correctness information is
-- attached externally by the soundness theorem below and the planned
-- completeness theorem, rather than by injecting validity proofs into parser
-- result types.

-- NOTE: We are proving these for Lists, we can later on generalize it to
-- other "sensible" collections that preserve parts of a list.

abbrev sound (cfg : @CFG α ν)
  (n : ν) (p : ParserM (tag := tag cfg) α List (ParseTree cfg)) (input : Array α)
  :=
  ∀ start end_ : ℕ,
  ∀ _h_bound : start ≤ end_ ∧ end_ ≤ input.size,
  ∀ tree ∈ (runParser p input start).1.getD end_ ⊥, tree.Valid ∧ tree.root = Symbol.nonterm n

abbrev complete (cfg : @CFG α ν) (n : ν) (p : ParserM (tag := tag cfg) α List (ParseTree cfg)) (input : Array α)
  :=
  cfg.derives [Symbol.nonterm n] (input.toList.map Symbol.term) →
    ∃ tree,
      tree ∈ (runParser p input 0).1.getD input.size [] ∧
      tree.Valid ∧
      tree.root = Symbol.nonterm n ∧
      tree.leaves = input.toList

abbrev result_bounded (cfg : @CFG α ν)
  (p : ParserM (tag := tag cfg) α List (ParseTree cfg)) (input : Array α)
  :=
  ∀ start end_ : ℕ,
  start ≤ input.size →
  ∀ tree, tree ∈ (runParser p input start).1.getD end_ [] →
    start ≤ end_ ∧ end_ ≤ input.size

omit [BEq α] [DecidableEq α] [DecidableEq ν] in
lemma mem_zip_index_pair
  {xs : List α} {ys : List β}
  (h_len : xs.length = ys.length)
  {x : α} {y : β}
  (h_mem : (x, y) ∈ xs.zip ys)
  : ∃ i : Fin xs.length, xs[i] = x ∧ ys[i] = y := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp h_mem
  have h_len_zip : (xs.zip ys).length = xs.length := by
    simp [List.length_zip, h_len]
  let i' : Fin xs.length := ⟨i.1, by simpa [h_len_zip] using i.2⟩
  refine ⟨i', ?_, ?_⟩
  · have hfst := congrArg Prod.fst hi
    simpa [i', h_len_zip] using hfst
  · have hsnd := congrArg Prod.snd hi
    simpa [i', h_len_zip] using hsnd

-- Traversal and parser-constructor lemmas used by generated-parser soundness.
omit [BEq α] [Hashable ν] [Fintype ν] [DecidableEq α] [DecidableEq ν] in
lemma mem_zip_index
  {rule : List (Symbol α ν)} {subtrees : List (ParseTree (α := α) cfg)}
  (h_len : rule.length = subtrees.length)
  {a : ν} {n : ν} {rule' : { rule // rule ∈ cfg.rules n }} {children' : List (ParseTree cfg)}
  (h_mem : (Symbol.nonterm a, Node n rule' children') ∈ rule.zip subtrees)
  : ∃ i : Fin rule.length, rule[i] = Symbol.nonterm a ∧ subtrees[i] = Node n rule' children' := by
  exact mem_zip_index_pair h_len h_mem

omit [Fintype ν] in
lemma runParser_traverse_origin
  {cfg : @CFG α ν}
  {γ : Type u} [DecidableEq γ]
  {xs : List (ParserM (tag := tag cfg) α List γ)}
  {input : Array α} {start end_ : ℕ} {result : List γ}
  (h_result : result ∈ (runParser (tag := tag cfg) (List.traverse id xs) input start).1.getD end_ [])
  (i : Fin result.length)
  : ∃ j : Fin xs.length, j.1 = i.1 ∧
      ∃ s e : ℕ, ∃ h : e ∈ (runParser (tag := tag cfg) xs[j] input s).1,
        result[i] ∈ (runParser (tag := tag cfg) xs[j] input s).1[e]'h := by
  induction xs generalizing start end_ result with
  | nil =>
      cases result with
      | nil => exact Fin.elim0 i
      | cons head tail =>
          have h_len := runParser_traverse_preserves_length (tag := tag cfg) input
            ([] : List (ParserM (tag := tag cfg) α List γ)) start end_ (head :: tail) h_result
          simp at h_len
  | cons head tail ih =>
      rw [List.traverse, seq_eq_bind] at h_result
      simp at h_result
      have h_end_mem : end_ ∈ (runParser
            (head >>= fun a =>
              List.cons a <$> List.traverse id tail)
            input start).1 := by
        rw [Std.HashMap.getD_eq_getD_getElem?] at h_result
        unfold Option.getD at h_result
        cases h_opt : (runParser
            (head >>= fun a =>
              List.cons a <$> List.traverse id tail)
            input start).1[end_]?
        · simp [h_opt] at h_result
        · exact (Std.HashMap.getElem?_eq_some_iff.mp h_opt).1
      rw [Std.HashMap.getD_eq_getD_getElem?] at h_result
      rw [Std.HashMap.getElem?_eq_some_getElem h_end_mem] at h_result
      let r := (runParser
        (head >>= fun a => List.cons a <$> List.traverse id tail)
        input start).1[end_]
      have h_split := by
        apply (mem_runParser_bind_iff_eq_bind_mem_runParser input head
          (fun (a : γ) => List.cons a <$> List.traverse id tail)
          (x := result) (r := r) (start := start) (end_pos := end_)).mp
        constructor
        · exact Std.HashMap.getElem?_eq_some_getElem h_end_mem
        · simpa [r] using h_result
      obtain ⟨split, s, h_split, h_result_in_bind⟩ := h_split
      simp [runParser_map_getElem?_eq] at h_result_in_bind
      cases result with
      | nil =>
          simp at h_result_in_bind
      | cons result_head result_tail =>
          cases i using Fin.cases with
          | zero =>
              simp at h_result_in_bind
              obtain ⟨head_result, h_head_mem, tail_results, h_tail_results, h_tail_mem, h_result_eq⟩ := h_result_in_bind
              cases h_result_eq
              let h_split_mem := (Std.HashMap.getElem?_eq_some_iff.mp h_split).1
              have h_split_val : (runParser head input start).1[split]'h_split_mem = s :=
                (Std.HashMap.getElem?_eq_some_iff.mp h_split).2
              refine ⟨⟨0, by simp⟩, by simp, start, split, ?_, ?_⟩
              · exact h_split_mem
              · simpa [h_split_val] using h_head_mem
          | succ i_tail =>
              simp at h_result_in_bind
              obtain ⟨head_result, h_head_mem, tail_results, h_tail_results, h_tail_mem, h_result_eq⟩ := h_result_in_bind
              cases h_result_eq
              have h_tail_mem_getD : result_tail ∈ (runParser (tag := tag cfg) (List.traverse id tail) input split).1.getD end_ [] := by
                rw [Std.HashMap.getD_eq_getD_getElem?]
                simp [h_tail_results, h_tail_mem]
              have h_tail_origin := ih h_tail_mem_getD i_tail
              obtain ⟨j, h_j, s', e', h_e', h_mem'⟩ := h_tail_origin
              refine ⟨⟨j.1 + 1, Nat.succ_lt_succ j.2⟩, ?_, s', e', ?_, ?_⟩
              · simp [h_j]
              · simpa using h_e'
              · simpa using h_mem'

omit [Fintype ν] in
lemma runParser_traverse_origin_bounded
  {cfg : @CFG α ν}
  {xs : List (ParserM (tag := tag cfg) α List (ParseTree cfg))}
  {input : Array α} {start end_ : ℕ} {result : List (ParseTree cfg)}
  (h_xs : ∀ j : Fin xs.length, ∀ s e : ℕ,
    s ≤ input.size →
    ∀ tree, tree ∈ (runParser (tag := tag cfg) xs[j] input s).1.getD e [] →
      s ≤ e ∧ e ≤ input.size)
  (h_start : start ≤ input.size)
  (h_result : result ∈ (runParser (tag := tag cfg) (List.traverse id xs) input start).1.getD end_ [])
  (i : Fin result.length)
  : ∃ j : Fin xs.length, j.1 = i.1 ∧
      ∃ s e : ℕ, ∃ h : e ∈ (runParser (tag := tag cfg) xs[j] input s).1,
        result[i] ∈ (runParser (tag := tag cfg) xs[j] input s).1[e]'h ∧
        s ≤ e ∧ e ≤ input.size := by
  induction xs generalizing start end_ result with
  | nil =>
      cases result with
      | nil => exact Fin.elim0 i
      | cons head tail =>
          have h_len := runParser_traverse_preserves_length (tag := tag cfg) input
            ([] : List (ParserM (tag := tag cfg) α List (ParseTree cfg))) start end_ (head :: tail) h_result
          simp at h_len
  | cons head tail ih =>
      rw [List.traverse, seq_eq_bind] at h_result
      simp at h_result
      have h_end_mem : end_ ∈ (runParser
            (head >>= fun a =>
              List.cons a <$> List.traverse id tail)
            input start).1 := by
        rw [Std.HashMap.getD_eq_getD_getElem?] at h_result
        unfold Option.getD at h_result
        cases h_opt : (runParser
            (head >>= fun a =>
              List.cons a <$> List.traverse id tail)
            input start).1[end_]?
        · simp [h_opt] at h_result
        · exact (Std.HashMap.getElem?_eq_some_iff.mp h_opt).1
      rw [Std.HashMap.getD_eq_getD_getElem?] at h_result
      rw [Std.HashMap.getElem?_eq_some_getElem h_end_mem] at h_result
      let r := (runParser
        (head >>= fun a => List.cons a <$> List.traverse id tail)
        input start).1[end_]
      have h_split := by
        apply (mem_runParser_bind_iff_eq_bind_mem_runParser input head
          (fun (a : ParseTree cfg) => List.cons a <$> List.traverse id tail)
          (x := result) (r := r) (start := start) (end_pos := end_)).mp
        constructor
        · exact Std.HashMap.getElem?_eq_some_getElem h_end_mem
        · simpa [r] using h_result
      obtain ⟨split, s, h_split, h_result_in_bind⟩ := h_split
      simp [runParser_map_getElem?_eq] at h_result_in_bind
      cases result with
      | nil =>
          simp at h_result_in_bind
      | cons result_head result_tail =>
          simp at h_result_in_bind
          obtain ⟨head_result, h_head_mem, tail_results, h_tail_results, h_tail_mem, h_result_eq⟩ := h_result_in_bind
          cases h_result_eq
          let h_split_mem := (Std.HashMap.getElem?_eq_some_iff.mp h_split).1
          have h_split_val : (runParser head input start).1[split]'h_split_mem = s :=
            (Std.HashMap.getElem?_eq_some_iff.mp h_split).2
          have h_head_getD : result_head ∈ (runParser (tag := tag cfg) head input start).1.getD split [] := by
            rw [Std.HashMap.getD_eq_getD_getElem?]
            simp [h_split, h_head_mem]
          have h_head_bounds := h_xs ⟨0, by simp⟩ start split h_start result_head h_head_getD
          cases i using Fin.cases with
          | zero =>
              refine ⟨⟨0, by simp⟩, by simp, start, split, ?_, ?_, ?_⟩
              · exact h_split_mem
              · simpa [h_split_val] using h_head_mem
              · exact h_head_bounds
          | succ i_tail =>
              have h_tail_mem_getD : result_tail ∈ (runParser (tag := tag cfg) (List.traverse id tail) input split).1.getD end_ [] := by
                rw [Std.HashMap.getD_eq_getD_getElem?]
                simp [h_tail_results, h_tail_mem]
              have h_tail_bounds :
                  ∀ j : Fin tail.length, ∀ s e : ℕ,
                    s ≤ input.size →
                    ∀ tree, tree ∈ (runParser (tag := tag cfg) tail[j] input s).1.getD e [] →
                      s ≤ e ∧ e ≤ input.size := by
                intro j s' e' h_s' tree h_tree
                have h := h_xs ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩ s' e' h_s' tree
                simpa using h h_tree
              have h_tail_origin := ih h_tail_bounds h_head_bounds.2 h_tail_mem_getD i_tail
              obtain ⟨j, h_j, s', e', h_e', h_mem', h_bounds'⟩ := h_tail_origin
              refine ⟨⟨j.1 + 1, Nat.succ_lt_succ j.2⟩, ?_, s', e', ?_, ?_, ?_⟩
              · simp [h_j]
              · simpa using h_e'
              · simpa using h_mem'
              · exact h_bounds'

omit [Fintype ν] in
lemma runParser_traverse_result_bounds
  {cfg : @CFG α ν}
  {xs : List (ParserM (tag := tag cfg) α List (ParseTree cfg))}
  {input : Array α} {start end_ : ℕ} {result : List (ParseTree cfg)}
  (h_xs : ∀ j : Fin xs.length, ∀ s e : ℕ,
    s ≤ input.size →
    ∀ tree, tree ∈ (runParser (tag := tag cfg) xs[j] input s).1.getD e [] →
      s ≤ e ∧ e ≤ input.size)
  (h_start : start ≤ input.size)
  (h_result : result ∈ (runParser (tag := tag cfg) (List.traverse id xs) input start).1.getD end_ [])
  : start ≤ end_ ∧ end_ ≤ input.size := by
  induction xs generalizing start end_ result with
  | nil =>
      rw [Std.HashMap.getD_eq_getD_getElem?, List.traverse, runParser_pure] at h_result
      by_cases h_end : end_ = start
      · subst h_end
        exact ⟨le_rfl, h_start⟩
      · simp [h_end] at h_result
  | cons head tail ih =>
      rw [List.traverse, seq_eq_bind] at h_result
      simp at h_result
      have h_end_mem : end_ ∈ (runParser
            (head >>= fun a =>
              List.cons a <$> List.traverse id tail)
            input start).1 := by
        rw [Std.HashMap.getD_eq_getD_getElem?] at h_result
        unfold Option.getD at h_result
        cases h_opt : (runParser
            (head >>= fun a =>
              List.cons a <$> List.traverse id tail)
            input start).1[end_]?
        · simp [h_opt] at h_result
        · exact (Std.HashMap.getElem?_eq_some_iff.mp h_opt).1
      rw [Std.HashMap.getD_eq_getD_getElem?] at h_result
      rw [Std.HashMap.getElem?_eq_some_getElem h_end_mem] at h_result
      let r := (runParser
        (head >>= fun a => List.cons a <$> List.traverse id tail)
        input start).1[end_]
      have h_split := by
        apply (mem_runParser_bind_iff_eq_bind_mem_runParser input head
          (fun (a : ParseTree cfg) => List.cons a <$> List.traverse id tail)
          (x := result) (r := r) (start := start) (end_pos := end_)).mp
        constructor
        · exact Std.HashMap.getElem?_eq_some_getElem h_end_mem
        · simpa [r] using h_result
      obtain ⟨split, s, h_split, h_result_in_bind⟩ := h_split
      simp [runParser_map_getElem?_eq] at h_result_in_bind
      cases result with
      | nil =>
          simp at h_result_in_bind
      | cons result_head result_tail =>
          simp at h_result_in_bind
          obtain ⟨head_result, h_head_mem, tail_results, h_tail_results, h_tail_mem, h_result_eq⟩ := h_result_in_bind
          cases h_result_eq
          have h_head_getD : result_head ∈ (runParser (tag := tag cfg) head input start).1.getD split [] := by
            rw [Std.HashMap.getD_eq_getD_getElem?]
            simp [h_split, h_head_mem]
          have h_head_bounds := h_xs ⟨0, by simp⟩ start split h_start result_head h_head_getD
          have h_tail_mem_getD : result_tail ∈ (runParser (tag := tag cfg) (List.traverse id tail) input split).1.getD end_ [] := by
            rw [Std.HashMap.getD_eq_getD_getElem?]
            simp [h_tail_results, h_tail_mem]
          have h_tail_bounds :
              ∀ j : Fin tail.length, ∀ s e : ℕ,
                s ≤ input.size →
                ∀ tree, tree ∈ (runParser (tag := tag cfg) tail[j] input s).1.getD e [] →
                  s ≤ e ∧ e ≤ input.size := by
            intro j s' e' h_s' tree h_tree
            have h := h_xs ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩ s' e' h_s' tree
            simpa using h h_tree
          have h_tail_result_bounds := ih h_tail_bounds h_head_bounds.2 h_tail_mem_getD
          exact ⟨Nat.le_trans h_head_bounds.1 h_tail_result_bounds.1, h_tail_result_bounds.2⟩

-- set_option maxHeartbeats 800000 in
omit [Fintype ν] in
lemma terminal'_sound
  {cfg : @CFG α ν}
  {a : α} {input : Array α} {start end_ : ℕ} {tree : ParseTree cfg}
  (h : tree ∈ (runParser (Leaf <$> terminal' (tag := tag cfg) a) input start).1.getD end_ [])
  : tree = Leaf a := by
  rw [Std.HashMap.getD_eq_getD_getElem?] at h
  rw [runParser_map_getElem?_eq] at h
  cases h_opt : (runParser (tag := tag cfg) (terminal' (tag := tag cfg) (μ := List) a) input start).1[end_]? with
  | none =>
      simp [h_opt] at h
  | some xs =>
      simp [h_opt] at h
      obtain ⟨x, h_x, h_tree⟩ := h
      have h_x_getD : x ∈ (runParser (tag := tag cfg)
          (terminal' (tag := tag cfg) (μ := List) a) input start).1.getD end_ [] := by
        rw [Std.HashMap.getD_eq_getD_getElem?]
        simp [h_opt, h_x]
      have h_x' := (mem_runParser_terminal_iff (tag := tag cfg)
        (a := a) (x := x) (input := input) (start := start) (end_pos := end_)).mp h_x_getD
      exact h_tree.symm.trans (congrArg Leaf h_x'.2.2)

omit [Fintype ν] in
lemma terminal'_complete
  {cfg : @CFG α ν}
  {a : α} {input : Array α} {start : ℕ}
  (h : input[start]? = some a)
  : Leaf (cfg := cfg) a ∈
      (runParser (tag := tag cfg) (Leaf <$> terminal' (tag := tag cfg) a) input start).1.getD (start + 1) [] := by
  have h_terminal : a ∈
      (runParser (tag := tag cfg) (terminal' (tag := tag cfg) (μ := List) a) input start).1.getD (start + 1) [] := by
    exact (mem_runParser_terminal_iff (tag := tag cfg)
      (a := a) (x := a) (input := input) (start := start) (end_pos := start + 1)).mpr
      ⟨h.symm, rfl, rfl⟩
  rw [Std.HashMap.getD_eq_getD_getElem?] at h_terminal ⊢
  rw [runParser_map_getElem?_eq]
  cases h_opt :
      (runParser (tag := tag cfg) (terminal' (tag := tag cfg) (μ := List) a) input start).1[start + 1]? with
  | none =>
      simp [h_opt] at h_terminal
  | some xs =>
      simp [h_opt] at h_terminal ⊢
      exact h_terminal

omit [Fintype ν] in
lemma terminal'_bounded
  {cfg : @CFG α ν}
  {a : α} {input : Array α}
  : result_bounded cfg (Leaf <$> terminal' (tag := tag cfg) a) input := by
  unfold result_bounded
  intro start end_ h_start tree h_mem
  rw [Std.HashMap.getD_eq_getD_getElem?] at h_mem
  rw [runParser_map_getElem?_eq] at h_mem
  cases h_opt : (runParser (tag := tag cfg) (terminal' (tag := tag cfg) (μ := List) a) input start).1[end_]? with
  | none =>
      simp [h_opt] at h_mem
  | some xs =>
      simp [h_opt] at h_mem
      obtain ⟨x, h_x, _h_tree⟩ := h_mem
      have h_x_getD : x ∈ (runParser (tag := tag cfg)
          (terminal' (tag := tag cfg) (μ := List) a) input start).1.getD end_ [] := by
        rw [Std.HashMap.getD_eq_getD_getElem?]
        simp [h_opt, h_x]
      have h_x' := (mem_runParser_terminal_iff (tag := tag cfg)
        (a := a) (x := x) (input := input) (start := start) (end_pos := end_)).mp h_x_getD
      obtain ⟨h_match, h_end, _h_x_eq⟩ := h_x'
      have h_start_lt : start < input.size := by
        exact (Array.getElem?_eq_some_iff.mp h_match.symm).1
      constructor
      · omega
      · omega

omit [Fintype ν] in
lemma failure_empty (cfg : @CFG α ν) {start : ℕ} : (runParser (tag := tag cfg) (⊥ : ParserM α μ (ParseTree cfg)) input start).1.isEmpty := by
  simp [Bot.bot, runParser, ReaderT.run, MStateT.run, ParserM.lift, ParserM.lower]
  unfold Parser.failure Parser.bind Bind.bind

  have h : @Std.HashMap.emptyWithCapacity.toList ℕ (μ (ParseTree cfg)) = [] := by
    apply List.isEmpty_iff.mp
    simp [Std.HashMap.isEmpty_emptyWithCapacity, Std.HashMap.isEmpty_toList]

  conv =>
    lhs
    enter [1, 1]
    whnf
    simp [h]
    left
    arg 1
    whnf
  simp

omit [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
theorem failure_sound (cfg : @CFG α ν) (n : ν) (input : Array α) : sound cfg n ⊥ input
  := by
  unfold sound
  intro start end_ _h tree
  simp [Std.HashMap.getD_of_isEmpty, failure_empty]
  simp [Bot.bot, SemilatticeAlt.failure]

omit [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
theorem failure_bounded (cfg : @CFG α ν) (input : Array α) : result_bounded cfg ⊥ input
  := by
  unfold result_bounded
  intro start end_ _h_start tree
  simp [Std.HashMap.getD_of_isEmpty, failure_empty]

omit [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
/-- The join operation on lists preserves soundness. -/
theorem sound_of_sup_sound (cfg : @CFG α ν) (n : ν) (p q : ParserM (tag := tag cfg) α List (ParseTree cfg)) (input : Array α)
  (h_p : sound cfg n p input) (h_q : sound cfg n q input) : sound cfg n (p ⊔ q) input
  := by
  unfold sound at *
  intro start end_ h_bound tree h_mem
  have h_p := h_p start end_ h_bound
  have h_q := h_q start end_ h_bound
  -- Extract subset relationships to use with h_mem
  have h := runParser_sup_eq_sup_runParser p q input start
  have h' := Std.HashMap.EquivQuot.getD_eq (s := SemilatticeAlt.setoid) (k := end_) (fallback := ⊥) h
  simp [SemilatticeAlt.setoid, List.memSetoid] at h'
  dsimp [Subset, List.Subset] at *
  replace h_mem := @h'.1 tree h_mem
  dsimp [Max.max] at h_mem
  by_cases h_p_contains_end_ : end_ ∈ (runParser p input start).1
  · by_cases h_q_contains_end_ : end_ ∈ (runParser q input start).1
    · rw [<- Std.HashMap.getElem_eq_getD] at h_p <;> simp_all
      rw [<- Std.HashMap.getElem_eq_getD] at h_q <;> try simp_all
      -- The explicit application is for providing the Semilatticeoid instance.
      have h' := Std.HashMap.unionSup_getD_both (s := SemilatticeAlt.setoid) (semi := List.instSemilatticeAlt.instSemilatticeoidInstSetoid) h_p_contains_end_ h_q_contains_end_
      simp [SemilatticeAlt.setoid, List.memSetoid, Subset, List.Subset] at h'
      replace h_mem := @h'.1 tree h_mem
      simp [Max.max, SemilatticeAlt.orElse] at h_mem
      cases h_mem <;> rename_i h_mem
      · exact h_p tree h_mem
      · exact h_q tree h_mem
    · have h' := Std.HashMap.unionSup_getD_of_right_not_contains (s := SemilatticeAlt.setoid) (semi := List.instSemilatticeAlt.instSemilatticeoidInstSetoid) (fallback := ⊥) (runParser p input start).1 (runParser q input start).1 h_q_contains_end_
      simp [SemilatticeAlt.setoid, List.memSetoid, Subset, List.Subset] at h'
      replace h_mem := @h'.1 tree h_mem
      exact h_p tree h_mem
  · have h' := Std.HashMap.unionSup_getD_of_not_contains (s := SemilatticeAlt.setoid) (semi := List.instSemilatticeAlt.instSemilatticeoidInstSetoid) (fallback := ⊥) (runParser p input start).1 (runParser q input start).1 h_p_contains_end_
    simp [SemilatticeAlt.setoid, List.memSetoid, Subset, List.Subset] at h'
    replace h_mem := @h'.1 tree h_mem
    by_cases h_q_contains_0 : 0 ∈ (runParser q input).1
    · exact h_q tree h_mem
    · simp_all

omit [Monad μ] [SemilatticeAlt μ] [Traversable μ] [Fintype ν] in
/-- The join operation on lists preserves result bounds. -/
theorem bounded_of_sup_bounded (cfg : @CFG α ν) (p q : ParserM (tag := tag cfg) α List (ParseTree cfg)) (input : Array α)
  (h_p : result_bounded cfg p input) (h_q : result_bounded cfg q input) : result_bounded cfg (p ⊔ q) input
  := by
  unfold result_bounded at *
  intro start end_ h_start tree h_mem
  have h := runParser_sup_eq_sup_runParser p q input start
  have h' := Std.HashMap.EquivQuot.getD_eq (s := SemilatticeAlt.setoid) (k := end_) (fallback := []) h
  simp [SemilatticeAlt.setoid, List.memSetoid] at h'
  dsimp [Subset, List.Subset] at *
  replace h_mem := @h'.1 tree h_mem
  dsimp [Max.max] at h_mem
  by_cases h_p_contains_end_ : end_ ∈ (runParser p input start).1
  · by_cases h_q_contains_end_ : end_ ∈ (runParser q input start).1
    · have h' := Std.HashMap.unionSup_getD_both (s := SemilatticeAlt.setoid) (semi := List.instSemilatticeAlt.instSemilatticeoidInstSetoid) h_p_contains_end_ h_q_contains_end_
      simp [SemilatticeAlt.setoid, List.memSetoid, Subset, List.Subset] at h'
      replace h_mem := @h'.1 tree h_mem
      simp [Max.max, SemilatticeAlt.orElse] at h_mem
      cases h_mem <;> rename_i h_mem
      · exact h_p start end_ h_start tree (by simpa [Std.HashMap.getElem_eq_getD (fallback := [])] using h_mem)
      · exact h_q start end_ h_start tree (by simpa [Std.HashMap.getElem_eq_getD (fallback := [])] using h_mem)
    · have h' := Std.HashMap.unionSup_getD_of_right_not_contains (s := SemilatticeAlt.setoid) (semi := List.instSemilatticeAlt.instSemilatticeoidInstSetoid) (fallback := []) (runParser p input start).1 (runParser q input start).1 h_q_contains_end_
      simp [SemilatticeAlt.setoid, List.memSetoid, Subset, List.Subset] at h'
      replace h_mem := @h'.1 tree h_mem
      exact h_p start end_ h_start tree h_mem
  · have h' := Std.HashMap.unionSup_getD_of_not_contains (s := SemilatticeAlt.setoid) (semi := List.instSemilatticeAlt.instSemilatticeoidInstSetoid) (fallback := []) (runParser p input start).1 (runParser q input start).1 h_p_contains_end_
    simp [SemilatticeAlt.setoid, List.memSetoid, Subset, List.Subset] at h'
    replace h_mem := @h'.1 tree h_mem
    exact h_q start end_ h_start tree h_mem

set_option maxHeartbeats 1000000 in
theorem gen_sound (cfg : @CFG α ν) n input : sound cfg n (gen (μ := List) cfg n) input := by
  unfold gen
  let p (parser : (n : ν) → ParserM α List (tag cfg n)) :=
    ∀ n input, sound cfg n (parser n) input ∧ result_bounded cfg (parser n) input
  have h_all : p (memoize (g := gen' (μ := List) cfg)) := by
    refine memoize_induction (gen' (μ := List) cfg) p ?_ ?_
    · intro n input
      exact ⟨failure_sound cfg n input, failure_bounded cfg input⟩
    · intro recur h_recur n input
      unfold gen'
      simp
      apply List.foldlRecOn
        (motive := fun parser => sound cfg n parser input ∧ result_bounded cfg parser input)
        _ _ ?_ ?_
      · exact ⟨failure_sound cfg n input, failure_bounded cfg input⟩
      · simp_all
        intro b b_sound b_bounded a rule h_rule h_a
        let buildNode := Node n ⟨rule, (Iff.of_eq (Eq.refl (rule ∈ cfg.rules n))).mpr h_rule⟩
        let mkParser : Symbol α ν -> (ParserM α List _) := (fun sym ↦
          match sym with
          | Symbol.term a => Leaf <$> terminal' a
          | Symbol.nonterm n => recur n)
        let children : ParserM α List (List (ParseTree cfg)) := List.traverse id (List.map mkParser rule)
        subst h_a
        constructor
        · apply sound_of_sup_sound
          · exact b_sound
          · unfold sound
            intro start end_ h_bound tree h_tree
            conv at h_tree =>
              enter [1,1,1,1]
              conv => arg 1 ; change buildNode
              conv => arg 2 ; change children
            rw [Std.HashMap.Equiv.getD_eq (runParser_map _ _ _)] at h_tree
            rw [Std.HashMap.getD_eq_getD_getElem?] at h_tree
            let result := (Std.HashMap.map (fun x ↦ Functor.map buildNode) (runParser children input start).1)
            by_cases h : end_ ∈ result <;> subst result <;> simp [h] at h_tree
            · subst buildNode
              replace ⟨subtrees, h_subtrees, h_tree⟩ := h_tree
              subst h_tree
              simp [ParseTree.Valid]
              have h_len : rule.length = subtrees.length := by
                simp [children] at *
                let parsers := rule.map mkParser
                rw [<- List.length_map mkParser]
                symm
                apply runParser_traverse_preserves_length input _ start end_
                rw [Std.HashMap.getElem_eq_getD (fallback := [])] at h_subtrees
                exact h_subtrees
              constructor
              · exact h_len
              · intro sym subtree h_mem
                have h_mem_subtrees (i : Fin subtrees.length) :
                    ∃ s e : ℕ, ∃ h : e ∈ (runParser (mkParser rule[i]) input s).1,
                      subtrees[i] ∈ (runParser (mkParser rule[i]) input s).1[e]'h ∧
                      s ≤ e ∧ e ≤ input.size := by
                  let parsers := rule.map mkParser
                  have h_subtrees_getD : subtrees ∈ (runParser (tag := tag cfg) (List.traverse id parsers) input start).1.getD end_ [] := by
                    rw [← Std.HashMap.getElem_eq_getD (fallback := [])]
                    simpa [children, parsers] using h_subtrees
                  have h_start_input : start ≤ input.size := Nat.le_trans h_bound.1 h_bound.2
                  have h_parsers_bounded :
                      ∀ j : Fin parsers.length, ∀ s e : ℕ,
                        s ≤ input.size →
                        ∀ tree, tree ∈ (runParser (tag := tag cfg) parsers[j] input s).1.getD e [] →
                          s ≤ e ∧ e ≤ input.size := by
                    intro j s e h_s tree h_tree
                    let jr : Fin rule.length := ⟨j.1, by simpa [parsers] using j.2⟩
                    have h_parser_j : parsers[j] = mkParser rule[jr] := by
                      simp [parsers, jr]
                    cases h_sym : rule[jr] with
                    | term a =>
                        exact terminal'_bounded (cfg := cfg) (a := a) (input := input)
                          s e h_s tree (by simpa [h_parser_j, mkParser, h_sym] using h_tree)
                    | nonterm a =>
                        exact (h_recur a input).2 s e h_s tree
                          (by simpa [h_parser_j, mkParser, h_sym] using h_tree)
                  have h_origin := runParser_traverse_origin_bounded (cfg := cfg) (xs := parsers)
                    (input := input) (start := start) (end_ := end_) (result := subtrees)
                    h_parsers_bounded h_start_input h_subtrees_getD i
                  obtain ⟨j, h_j, s, e, h_e, h_tree_mem, h_bounds⟩ := h_origin
                  have h_parser : parsers[j] = mkParser rule[i] := by
                    simp [parsers, h_j]
                  refine ⟨s, e, ?_, ?_, ?_⟩
                  · simpa [h_parser] using h_e
                  · simpa [h_parser] using h_tree_mem
                  · exact h_bounds
                cases sym <;> cases subtree <;> simp only [ParseTree.Valid] at h_mem ⊢
                · rename_i a b
                  have h_mem_zip : (Symbol.term a, Leaf b) ∈ rule.zip subtrees := by
                    simpa using h_mem
                  obtain ⟨i, hi⟩ := List.mem_iff_get.mp h_mem_zip
                  have h_len_zip : (rule.zip subtrees).length = subtrees.length := by
                    simp [List.length_zip, h_len]
                  let i' : Fin subtrees.length := ⟨i.1, by simpa [h_len_zip] using i.2⟩
                  have h_rule_i : rule[i'] = Symbol.term a := by
                    have hfst := congrArg Prod.fst hi
                    simpa [i', h_len_zip] using hfst
                  have h_sub_i : subtrees[i'] = Leaf b := by
                    have hsnd := congrArg Prod.snd hi
                    simpa [i', h_len_zip] using hsnd
                  obtain ⟨s, e, h_e, h_tree_mem, _h_bounds⟩ := h_mem_subtrees i'
                  have h_tree_mem' : subtrees[i'] ∈ (runParser (mkParser rule[i']) input s).1.getD e ⊥ := by
                    simpa [Std.HashMap.getElem_eq_getD (fallback := ⊥)] using h_tree_mem
                  have h_tree_mem'' : subtrees[i'] ∈ (runParser (mkParser rule[i']) input s).1.getD e [] := by
                    simpa [Bot.bot] using h_tree_mem'
                  have h_rule_i' : mkParser rule[i'] = Leaf <$> terminal' a := by
                    simp [mkParser, h_rule_i]
                  have h_leaf : subtrees[i'] = Leaf a := by
                    set t := subtrees[i']
                    have h_tree_mem''' : t ∈ (runParser (tag := tag cfg) (Leaf <$> terminal' a) input s).1.getD e [] := by
                      have h' := h_tree_mem''
                      rw [h_rule_i'] at h'
                      simpa [t] using h'
                    have h_t : t = Leaf a := terminal'_sound (cfg := cfg) (a := a) (input := input)
                      (start := s) (end_ := e) (tree := t) h_tree_mem'''
                    simpa [t] using h_t
                  have h_eq_leaf : Leaf (cfg := cfg) b = Leaf a := by
                    calc
                      Leaf b = subtrees[i'] := by simp [h_sub_i]
                      _ = Leaf a := h_leaf
                  cases h_eq_leaf
                  rfl
                · rename_i a n' rule' children'
                  obtain ⟨i, h_rule_i, h_sub_i⟩ := mem_zip_index_pair h_len h_mem
                  let i' : Fin subtrees.length := ⟨i.1, by simpa [h_len] using i.2⟩
                  obtain ⟨s, e, h_e, h_tree_mem, _h_bounds⟩ := h_mem_subtrees i'
                  have h_rule_i' : rule[i'] = Symbol.term a := by
                    simpa [i', h_len] using h_rule_i
                  have h_sub_i' : subtrees[i'] = Node n' rule' children' := by
                    simpa [i', h_len] using h_sub_i
                  have h_tree_mem' : subtrees[i'] ∈ (runParser (mkParser rule[i']) input s).1.getD e ⊥ := by
                    simpa [Std.HashMap.getElem_eq_getD (fallback := ⊥)] using h_tree_mem
                  have h_tree_mem'' : subtrees[i'] ∈ (runParser (mkParser rule[i']) input s).1.getD e [] := by
                    simpa [Bot.bot] using h_tree_mem'
                  have h_rule_parser : mkParser rule[i'] = Leaf <$> terminal' a := by
                    simp [mkParser, h_rule_i']
                  have h_node_is_leaf : Node n' rule' children' = Leaf a := by
                    have h_terminal : subtrees[i'] = Leaf a := by
                      set t := subtrees[i']
                      have h_t_mem : t ∈ (runParser (tag := tag cfg) (Leaf <$> terminal' a) input s).1.getD e [] := by
                        have h' := h_tree_mem''
                        rw [h_rule_parser] at h'
                        simpa [t] using h'
                      have h_t : t = Leaf a := terminal'_sound (cfg := cfg) (a := a) (input := input)
                        (start := s) (end_ := e) (tree := t) h_t_mem
                      simpa [t] using h_t
                    simp [h_sub_i'] at h_terminal
                  cases h_node_is_leaf
                · rename_i a b
                  obtain ⟨i, h_rule_i, h_sub_i⟩ := mem_zip_index_pair h_len h_mem
                  let i' : Fin subtrees.length := ⟨i.1, by simpa [h_len] using i.2⟩
                  obtain ⟨s, e, h_e, h_tree_mem, h_bounds⟩ := h_mem_subtrees i'
                  have h_rule_i' : rule[i'] = Symbol.nonterm a := by
                    simpa [i', h_len] using h_rule_i
                  have h_sub_i' : subtrees[i'] = Leaf b := by
                    simpa [i', h_len] using h_sub_i
                  have h_tree_mem' : subtrees[i'] ∈ (runParser (mkParser rule[i']) input s).1.getD e ⊥ := by
                    simpa [Std.HashMap.getElem_eq_getD (fallback := ⊥)] using h_tree_mem
                  have h_tree_mem_recur : subtrees[i'] ∈ (runParser (recur a) input s).1.getD e ⊥ := by
                    simpa [mkParser, h_rule_i'] using h_tree_mem'
                  have h_tree_mem_leaf : Leaf (cfg := cfg) b ∈ (runParser (recur a) input s).1.getD e ⊥ := by
                    simpa [h_sub_i'] using h_tree_mem_recur
                  have h_valid_root : (Leaf (cfg := cfg) b).Valid ∧ (Leaf (cfg := cfg) b).root = Symbol.nonterm a :=
                    (h_recur a input).1 s e h_bounds (Leaf b) h_tree_mem_leaf
                  have h_root : (Leaf (cfg := cfg) b).root = Symbol.nonterm a := h_valid_root.2
                  simp at h_root
                · rename_i a n rule' children'
                  obtain ⟨i, h_rule_i, h_sub_i⟩ := mem_zip_index_pair h_len h_mem
                  let i' : Fin subtrees.length := ⟨i.1, by simpa [h_len] using i.2⟩
                  obtain ⟨s, e, h_e, h_tree_mem, h_bounds⟩ := h_mem_subtrees i'
                  have h_rule_i' : rule[i'] = Symbol.nonterm a := by
                    simpa [i', h_len] using h_rule_i
                  have h_sub_i' : subtrees[i'] = Node n rule' children' := by
                    simpa [i', h_len] using h_sub_i
                  have h_tree_mem' : subtrees[i'] ∈ (runParser (mkParser rule[i']) input s).1.getD e ⊥ := by
                    simpa [Std.HashMap.getElem_eq_getD (fallback := ⊥)] using h_tree_mem
                  have h_tree_mem_recur : subtrees[i'] ∈ (runParser (recur a) input s).1.getD e ⊥ := by
                    simpa [mkParser, h_rule_i'] using h_tree_mem'
                  have h_tree_mem_node : Node n rule' children' ∈ (runParser (recur a) input s).1.getD e ⊥ := by
                    simpa [h_sub_i'] using h_tree_mem_recur
                  have h_valid_root : (Node n rule' children').Valid ∧ (Node n rule' children').root = Symbol.nonterm a :=
                    (h_recur a input).1 s e h_bounds (Node n rule' children') h_tree_mem_node
                  have h_valid : (Node n rule' children').Valid := h_valid_root.1
                  have h_eq : a = n := by
                    have h_root : (Node n rule' children').root = Symbol.nonterm a := h_valid_root.2
                    simpa using h_root.symm
                  exact And.intro h_eq (by simpa [ParseTree.Valid] using h_valid)
            · simp [Bot.bot, SemilatticeAlt.failure] at h_tree
        · apply bounded_of_sup_bounded
          · exact b_bounded
          · unfold result_bounded
            intro start end_ h_start tree h_tree
            conv at h_tree =>
              enter [1,1,1,1]
              conv => arg 1 ; change buildNode
              conv => arg 2 ; change children
            rw [Std.HashMap.Equiv.getD_eq (runParser_map _ _ _)] at h_tree
            rw [Std.HashMap.getD_eq_getD_getElem?] at h_tree
            let result := (Std.HashMap.map (fun x ↦ Functor.map buildNode) (runParser children input start).1)
            by_cases h : end_ ∈ result <;> subst result <;> simp [h] at h_tree
            · obtain ⟨subtrees, h_subtrees, _h_tree⟩ := h_tree
              let parsers := rule.map mkParser
              have h_subtrees_getD : subtrees ∈ (runParser (tag := tag cfg) (List.traverse id parsers) input start).1.getD end_ [] := by
                rw [← Std.HashMap.getElem_eq_getD (fallback := [])]
                simpa [children, parsers] using h_subtrees
              have h_parsers_bounded :
                  ∀ j : Fin parsers.length, ∀ s e : ℕ,
                    s ≤ input.size →
                    ∀ tree, tree ∈ (runParser (tag := tag cfg) parsers[j] input s).1.getD e [] →
                      s ≤ e ∧ e ≤ input.size := by
                intro j s e h_s tree h_tree
                let jr : Fin rule.length := ⟨j.1, by simpa [parsers] using j.2⟩
                have h_parser_j : parsers[j] = mkParser rule[jr] := by
                  simp [parsers, jr]
                cases h_sym : rule[jr] with
                | term a =>
                    exact terminal'_bounded (cfg := cfg) (a := a) (input := input)
                      s e h_s tree (by simpa [h_parser_j, mkParser, h_sym] using h_tree)
                | nonterm a =>
                    exact (h_recur a input).2 s e h_s tree
                      (by simpa [h_parser_j, mkParser, h_sym] using h_tree)
              exact runParser_traverse_result_bounds (cfg := cfg) (xs := parsers)
                (input := input) (start := start) (end_ := end_) (result := subtrees)
                h_parsers_bounded h_start h_subtrees_getD
  exact (h_all n input).1

-- Generated-parser completeness.
--
-- Proof outline: combine `ParseTree.exists_Valid_tree_of_derives` with a
-- minimal-tree/fuel theorem.  Choose a valid tree with no same-nonterminal
-- same-span cycle; the memoization budget `remaining input + 1` admits the
-- final nullable/base call, and exact-counter cache keys prevent lower-fuel
-- entries from suppressing later higher-fuel calls.  The tree proof then
-- follows the generated rule branch, assembles children through
-- `List.traverse`, and uses terminal semantics for leaves.
axiom gen_complete_exists
  {cfg : @CFG α ν} {n : ν} {input : Array α}
  (h : cfg.derives [Symbol.nonterm n] (input.toList.map Symbol.term)) :
    ∃ tree,
      tree ∈ (runParser (tag := tag cfg) (gen (μ := List) cfg n) input 0).1.getD input.size [] ∧
      tree.Valid ∧
      tree.root = Symbol.nonterm n ∧
      tree.leaves = input.toList

theorem gen_complete (cfg : @CFG α ν) n input :
    complete cfg n (gen (μ := List) cfg n) input := by
  intro h
  exact gen_complete_exists (cfg := cfg) (n := n) (input := input) h

theorem gen_correct (cfg : @CFG α ν) n input :
    sound cfg n (gen (μ := List) cfg n) input ∧
    complete cfg n (gen (μ := List) cfg n) input := by
  exact ⟨gen_sound cfg n input, gen_complete cfg n input⟩

end Gen
