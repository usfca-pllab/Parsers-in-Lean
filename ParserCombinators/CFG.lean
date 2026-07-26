/-
Context-free grammars along with derivation and parsing relations.

Conventions:
- `ν` is the type of nonterminals/variables.
- `α` is the type of terminals (the alphabet).
-/
import Batteries.Data.List.Basic
import Mathlib.Data.List.Monad
import Mathlib.Data.List.Zip
import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Relation
import ParserCombinators.Util
import Aesop

universe u v
variable {α : Type u} {ν : Type v} [DecidableEq α] [DecidableEq ν]

-- Symbol
inductive Symbol (α : Type u) (ν : Type v) where
  | term    : α -> Symbol α ν
  | nonterm : ν -> Symbol α ν
  deriving DecidableEq, Repr

-- Derivation strings.  Also used as right-hand sides for CFG rules
@[simp]
abbrev symbols (α : Type u) (ν : Type v) := List (Symbol α ν)

/-
Context-free grammars.

For a proper CFG, `ν` needs to be a finite type.
-/
structure CFG where
  rules : ν -> List (symbols α ν)
  start : ν

namespace CFG

open Symbol

@[simp]
private def my_vars : Finset ℕ := {1,2,3}

instance : OfNat my_vars 1 where
  ofNat := ⟨1, by decide⟩

instance : OfNat my_vars 2 where
  ofNat := ⟨2, by decide⟩

instance : OfNat my_vars 3 where
  ofNat := ⟨3, by decide⟩

@[simp]
private def my_alphabet : Finset Char := {'a', 'b', 'c'}

@[simp]
def of (c : Char ) ( h : c ∈ my_alphabet ) : my_alphabet := ⟨c, h⟩

@[simp]
def a_in : 'a' ∈ my_alphabet := by decide

@[simp]
def b_in : 'b' ∈ my_alphabet := by decide

@[simp]
def c_in : 'c' ∈ my_alphabet := by decide

abbrev a := of 'a' a_in
abbrev b := of 'b' b_in
abbrev c := of 'c' c_in

def my_cfg : @CFG my_alphabet my_vars := {
  start := 1
  rules :=
    let a := of 'a' a_in
    fun x =>
    match x with
      | 1 => [[nonterm 1, term a], []]
      | 2 => []
      | 3 => []
}

#check my_cfg.rules

-- All possible derivations: a step function
@[simp, aesop unsafe]
def yield {cfg : @CFG α ν} (deriv : symbols α ν) : List (symbols α ν) := do
  let (init, Symbol.nonterm x :: tail) ← deriv.inits.zip deriv.tails
    | []  -- eliminate positions that do not start with a variable
  (fun rhs => init ++ rhs ++ tail) <$> cfg.rules x

def my_str : symbols my_alphabet my_vars := [term a, nonterm 1, term c]

#eval my_cfg.yield my_str

-- Relation version of the step function
@[simp, aesop unsafe]
def yields {cfg : @CFG α ν} (a b : symbols α ν) := b ∈ cfg.yield a

instance {cfg : @CFG α ν} (a b : symbols α ν) : Decidable (cfg.yields a b) :=
  if h : b ∈ cfg.yield a then isTrue h else isFalse h

example : my_cfg.yields [term a, nonterm 1, term c] [term a, term c] := by
  simp only [yields]
  decide

omit [DecidableEq α] [DecidableEq ν] in
theorem yields_iff_decompose
  {cfg : @CFG α ν} {v u : symbols α ν} :
    cfg.yields v u ↔
      ∃ pre n post rhs,
        v = pre ++ [Symbol.nonterm n] ++ post ∧
        rhs ∈ cfg.rules n ∧
        u = pre ++ rhs ++ post := by
  unfold yields yield
  simp only [List.bind_eq_flatMap, List.mem_flatMap]
  constructor
  · rintro ⟨⟨pre, rest⟩, h_split, h_result⟩
    rw [List.mem_zip_inits_tails] at h_split
    cases rest with
    | nil => simp at h_result
    | cons sym post =>
        cases sym with
        | term _ => simp at h_result
        | nonterm n =>
            change u ∈
              List.map (fun rhs => pre ++ rhs ++ post) (cfg.rules n) at h_result
            obtain ⟨rhs, h_rhs, h_u⟩ := List.mem_map.mp h_result
            exact ⟨pre, n, post, rhs, by
              simpa [List.append_assoc] using h_split.symm, h_rhs, h_u.symm⟩
  · rintro ⟨pre, n, post, rhs, h_v, h_rhs, rfl⟩
    subst v
    refine ⟨(pre, Symbol.nonterm n :: post), ?_, ?_⟩
    · rw [List.mem_zip_inits_tails]
      simp [List.append_assoc]
    · exact List.mem_map.mpr ⟨rhs, h_rhs, rfl⟩

omit [DecidableEq α] [DecidableEq ν] in
theorem yields_decompose
  {cfg : @CFG α ν} {v u : symbols α ν}
  (h : cfg.yields v u) :
    ∃ pre n post rhs,
      v = pre ++ [Symbol.nonterm n] ++ post ∧
      rhs ∈ cfg.rules n ∧
      u = pre ++ rhs ++ post :=
  yields_iff_decompose.mp h

omit [DecidableEq α] [DecidableEq ν] in
theorem yields_of_append_left
    {cfg : @CFG α ν} (v₁ v₂ w : symbols α ν) (h : cfg.yields v₁ w) :
    cfg.yields (v₁ ++ v₂) (w ++ v₂) := by
  obtain ⟨pre, n, post, rhs, h_v, h_rhs, h_w⟩ := yields_decompose h
  apply yields_iff_decompose.mpr
  refine ⟨pre, n, post ++ v₂, rhs, ?_, h_rhs, ?_⟩
  · simp [h_v, List.append_assoc]
  · simp [h_w, List.append_assoc]

omit [DecidableEq α] [DecidableEq ν] in
theorem yields_of_append_right
    {cfg : @CFG α ν} (v₁ v₂ w : symbols α ν) (h : cfg.yields v₁ w) :
    cfg.yields (v₂ ++ v₁) (v₂ ++ w) := by
  obtain ⟨pre, n, post, rhs, h_v, h_rhs, h_w⟩ := yields_decompose h
  apply yields_iff_decompose.mpr
  refine ⟨v₂ ++ pre, n, post, rhs, ?_, h_rhs, ?_⟩
  · simp [h_v, List.append_assoc]
  · simp [h_w, List.append_assoc]

-- Derives: transitive reflexive closure of yields.
-- NOTE(maemre): This is potentially noncomputable, might need a step index
@[simp, aesop unsafe]
def derives {cfg : @CFG α ν} : (symbols α ν) → (symbols α ν) → Prop :=
  Relation.ReflTransGen cfg.yields

example : my_cfg.derives [term a, nonterm 1, term c] [term a, term a, term c] := by
  -- local defs for convenience
  let rel := my_cfg.yields
  let x : symbols my_alphabet my_vars := [term a, nonterm 1, term c]
  let y : symbols my_alphabet my_vars := [term a, nonterm 1, term a, term c]
  let z : symbols my_alphabet my_vars := [term a, term a, term c]
  unfold derives
  -- `derives` is not decidable, so we have to explicitly give a route.
  show Relation.ReflTransGen rel x z
  refine @Relation.ReflTransGen.head (symbols my_alphabet my_vars) rel x y z ?_ ?_
  · simp only [rel, yields]
    decide
  · refine @Relation.ReflTransGen.tail (symbols my_alphabet my_vars) rel y y z Relation.ReflTransGen.refl ?_
    simp only [rel, yields]
    decide

theorem derives_of_append_left {cfg : @CFG α ν} {v₁ v₂ w : symbols α ν} (h : cfg.derives v₁ w)
    : cfg.derives (v₁ ++ v₂) (w ++ v₂) := by
  refine Relation.ReflTransGen.head_induction_on h ?_ ?_
  · exact Relation.ReflTransGen.refl
  · intro v u h_yields h_tail ih
    apply yields_of_append_left at h_yields
    exact Relation.ReflTransGen.head h_yields ih

theorem derives_of_append_right {cfg : @CFG α ν} {v₁ v₂ w : symbols α ν} (h : cfg.derives v₂ w)
    : cfg.derives (v₁ ++ v₂) (v₁ ++ w) := by
  refine Relation.ReflTransGen.head_induction_on h ?_ ?_
  · exact Relation.ReflTransGen.refl
  · intro v u h_yields h_tail ih
    apply yields_of_append_right at h_yields
    exact Relation.ReflTransGen.head h_yields ih

theorem derives_of_append {cfg : @CFG α ν} {v₁ v₂ w₁ w₂ : symbols α ν} (h₁ : cfg.derives v₁ w₁) (h₂ : cfg.derives v₂ w₂)
    : cfg.derives (v₁ ++ v₂) (w₁ ++ w₂) := by
  exact Relation.ReflTransGen.trans (derives_of_append_left h₁) (derives_of_append_right h₂)

end CFG

-- A parse tree according to given grammar.  It stores which rule is used to build the current node.
inductive ParseTree (cfg : @CFG α ν) : Type (max u v) where
  | Leaf (t : α)
  | Node (n : ν) (rule : {rule // rule ∈ cfg.rules n}) (children : List (ParseTree cfg))
  deriving Repr

namespace ParseTree

open CFG
open Symbol

private lemma List.eq_of_Forall_eq {α} (xs ys : List α) (h : List.Forall₂ Eq xs ys) : xs = ys := by induction xs with
  | nil => simp_all
  | cons head tail ih => simp_all

private lemma List.Forall_of_Forall_attach {α} (xs ys : List α) (r : α → α → Prop) (h : List.Forall₂ (fun a b => r a.val b.val) xs.attach ys.attach)
    : List.Forall₂ r xs ys := by induction xs generalizing ys with
  | nil => simp_all
  | cons head tail ih => cases ys <;> simp_all

private def beq {cfg : @CFG α ν} [DecidableEq α] [DecidableEq ν] (tree₁ tree₂ : ParseTree cfg) : Bool :=
  match tree₁, tree₂ with
  | Leaf t₁, Leaf t₂ => t₁ = t₂
  | Node n₁ rule₁ children₁, Node n₂ rule₂ children₂ =>
      n₁ = n₂ && rule₁.val = rule₂.val && children₁.length = children₂.length
        && (List.all₂ (fun a b => beq a.val b.val) children₁.attach children₂.attach)
  | _, _ => false
termination_by tree₁
decreasing_by
  calc sizeOf a.val < sizeOf children₁ := List.sizeOf_lt_of_mem a.property
       _ < sizeOf (Node n₁ rule₁ children₁) := by simp +arith

instance {cfg : @CFG α ν} [BEq α] [BEq ν] : BEq (ParseTree cfg) where
  beq := beq

section DecidableEq
variable {cfg : @CFG α ν}

set_option maxHeartbeats 10000
private lemma eq_of_beq {tree₁ tree₂ : ParseTree cfg} (h : beq tree₁ tree₂) : tree₁ = tree₂ := by
  match tree₁, tree₂ with
    | Leaf _, Node _ _ _ => simp [beq] at h
    | Node _ _ _, Leaf _ => simp [beq] at h
    | Leaf t₁, Leaf t₂ =>
      simp [beq] at h
      simp [h]
    | Node n₁ rule₁ children₁, Node n₂ rule₂ children₂ =>
      simp [beq] at h
      have ⟨⟨⟨h_n, h_rule⟩, h_children_len⟩, h_children⟩ := h
      simp
      constructor
      · assumption
      · constructor
        · obtain ⟨val, property⟩ := rule₁
          obtain ⟨val_1, property_1⟩ := rule₂
          simp at h_rule
          subst h_n
          simp [h_rule]
        · clear h
          have h_dec : sizeOf children₂ ≤ sizeOf (Node n₁ rule₁ children₂) := by simp
          apply List.eq_of_Forall_eq
          apply List.Forall_of_Forall_attach
          refine List.Forall₂.imp ?_ h_children
          intro a b
          apply eq_of_beq
decreasing_by
  calc sizeOf a.val < sizeOf children₁ := List.sizeOf_lt_of_mem a.property
       _ < sizeOf (Node n₁ rule₁ children₁) := by simp +arith

variable [BEq α] [BEq ν]

private lemma beq_rfl {tree : ParseTree cfg} : tree == tree := by match tree with
  | Leaf t => dsimp [BEq.beq] ; simp [beq]
  | Node n rule children =>
      dsimp [BEq.beq]
      unfold beq
      simp []
      intro subtree h_mem
      exact beq_rfl

instance : LawfulBEq (ParseTree cfg) where
  rfl := beq_rfl
  eq_of_beq := eq_of_beq

instance : DecidableEq (ParseTree cfg) := instDecidableEqOfLawfulBEq
end DecidableEq

def my_tree₁ : ParseTree my_cfg := Node 1 ⟨[], by decide⟩ []
def my_tree₂ : ParseTree my_cfg := Leaf a
def my_tree₃ : ParseTree my_cfg := Node 1 ⟨[nonterm 1, term a], by decide⟩ [
  Node 1 ⟨[nonterm 1, term a], by decide⟩ [
    my_tree₁, Leaf a
  ],
  Leaf a]

@[simp]
def children {cfg : @CFG α ν} : ParseTree cfg → List (ParseTree cfg)
  | ParseTree.Node _ _ children => children
  | ParseTree.Leaf _ => []

@[simp]
def isNode {cfg : @CFG α ν} : (ParseTree cfg) → Bool
  | Node _ _ _ => true
  | Leaf _ => false

@[simp]
def nonterminal {cfg : @CFG α ν} (tree : ParseTree cfg) (h : tree.isNode) : ν := match tree with
  | ParseTree.Node n _ _ => n
  | ParseTree.Leaf _ => by contradiction

@[simp]
def nonterminal? {cfg : @CFG α ν} : ParseTree cfg → Option ν
  | ParseTree.Node n _ _ => n
  | ParseTree.Leaf _ => none

@[simp]
def root {cfg : @CFG α ν} : ParseTree cfg → Symbol α ν
  | ParseTree.Node n _ _ => nonterm n
  | ParseTree.Leaf a => term a

@[simp]
def sizeOf_lt_of_child_forest {cfg : @CFG α ν} {child : ParseTree cfg} {forest : List (ParseTree cfg)} [SizeOf α] (h_mem : child ∈ forest)
    : sizeOf child < sizeOf forest := by
  exact @List.sizeOf_lt_of_mem (ParseTree cfg) child inferInstance forest h_mem

@[simp]
def sizeOf_lt_of_child {cfg : @CFG α ν} {parent child : ParseTree cfg} [SizeOf α] (h_mem : child ∈ parent.children)
    : sizeOf child < sizeOf parent := match parent with
    | ParseTree.Node _ _ children => by
        simp_all only [ParseTree.children, Node.sizeOf_spec]
        apply Nat.lt_add_left
        exact (sizeOf_lt_of_child_forest h_mem)
    | ParseTree.Leaf _ => by simp at h_mem


def leaves {cfg : @CFG α ν} (tree : ParseTree cfg) : List α := match tree with
  | ParseTree.Leaf a => [a]
  | ParseTree.Node _ _ children => children.attach.flatMap (fun ⟨node, _h_mem⟩ => leaves node)
termination_by tree
decreasing_by
  exact sizeOf_lt_of_child _h_mem

#guard leaves my_tree₁ == []
#guard leaves my_tree₂ == [a]
#guard leaves my_tree₃ == [a, a]

def Valid {cfg : @CFG α ν} (tree : ParseTree cfg) : Prop := match tree with
  | Leaf _ => True
  | Node n rule children => rule.val.length = children.length ∧
  ∀ pair (_h : pair ∈ List.zip rule.val children), match _h_pair : pair, _h with
    | ⟨Symbol.term a, Leaf b⟩, _ => a = b
    | ⟨Symbol.nonterm n, subtree@_h:(Node n' _ _)⟩, _ => n = n' ∧ subtree.Valid
    | _, _ => False
decreasing_by
  rename_i h_mem
  apply List.of_mem_zip at h_mem
  unfold namedPattern at h_mem
  rw [<- _h] at h_mem
  exact sizeOf_lt_of_child h_mem.right

-- Boolean version of `Valid`, used for decidability.
def valid {cfg : @CFG α ν} (tree : ParseTree cfg) : Bool := match tree with
  | Leaf _ => True
  | Node n rule children => rule.val.length = children.length &&
  (List.zip rule.val children).attach.all (fun
    | ⟨(Symbol.term a, Leaf b), _⟩ => a == b
    | ⟨(Symbol.nonterm n, subtree@_h:(Node n' _ _)), _⟩ => n = n' && subtree.valid
    | _ => false)
decreasing_by
  rename_i h_mem
  apply List.of_mem_zip at h_mem
  unfold namedPattern at h_mem
  rw [<- _h] at h_mem
  exact sizeOf_lt_of_child h_mem.right

#guard my_tree₁.valid
#guard my_tree₂.valid
#guard my_tree₃.valid

lemma valid_eq_true_iff_Valid {cfg : @CFG α ν} {tree : ParseTree cfg} : tree.valid = true ↔ tree.Valid := match h : tree with
  | ParseTree.Leaf _ => by unfold valid Valid ; decide
  | ParseTree.Node n rule children => by {
    unfold valid Valid
    subst h
    simp_all [symbols]
    intro h_eq_len
    apply forall_congr'
    intro a
    repeat (apply forall_congr' ; intro)
    rename_i subtree h_mem
    match a, h : subtree with
    | nonterm _, Node _ _ _ =>
        have h' := @valid_eq_true_iff_Valid cfg subtree
        rw [h] at h'
        simp [h']
    | nonterm _, Leaf _ => simp
    | term _, Node _ _ _ => simp
    | term _, Leaf _ => simp
  }
termination_by tree
decreasing_by
  apply List.of_mem_zip at h_mem
  rw [h]
  exact sizeOf_lt_of_child h_mem.right

instance decidable_of_Valid {cfg : @CFG α ν} {tree : ParseTree cfg} : Decidable tree.Valid :=
  decidable_of_iff (tree.valid = true) valid_eq_true_iff_Valid

example : my_tree₁.Valid := by native_decide
example : my_tree₂.Valid := by native_decide
example : my_tree₃.Valid := by native_decide

theorem derives_of_Valid_tree {cfg : @CFG α ν} {tree : ParseTree cfg} (h : tree.Valid)
    : cfg.derives [tree.root] (tree.leaves.map term) := match tree with
  | Leaf a => by
     simp [leaves]
     exact Relation.ReflTransGen.refl
  | Node n rule_and_mem children => by {
    unfold Valid at h
    simp at h
    obtain ⟨h_len, h_recur⟩ := h
    have ⟨rule, property⟩ := rule_and_mem
    have h_step : cfg.yields [Symbol.nonterm n] rule :=
      CFG.yields_iff_decompose.mpr
        ⟨[], n, [], rule, by simp, property, by simp⟩
    refine Relation.ReflTransGen.head h_step ?_
    simp only [symbols, leaves, List.flatMap_subtype, List.unattach_attach]
    have derives_of_children (subtree : ParseTree cfg) (a : Symbol α ν)
        (h_mem : (a, subtree) ∈ List.zip rule children) :
        cfg.derives [a] (subtree.leaves.map term) := by {
      have subtree_root_eq_symbol : subtree.root = a := by
        have helper := h_recur a subtree h_mem
        split at helper
        · simp_all
        · simp_all
        · simp_all
      replace h_recur := h_recur a subtree h_mem
      rw [<- subtree_root_eq_symbol]
      apply derives_of_Valid_tree
      unfold Valid
      cases h_subtree : subtree
      · simp
      · cases h_a : a with
        | term =>
          subst h_a h_subtree
          simp at h_recur
        | nonterm =>
          subst h_a h_subtree
          simp only at h_recur
          unfold Valid at h_recur
          simp [h_recur]
    }

    simp at h_len
    clear h_recur property h_step
    induction h : rule.zip children generalizing rule children with
    | nil =>
      replace h := zip_eq_nil_of_eq_length h_len h
      simp [h]
      exact Relation.ReflTransGen.refl
    | cons head tail ih =>
      obtain ⟨symbol, subtree⟩ := head
      obtain ⟨symbols, trees, h_rule, h_children, h_tail⟩ :=
        List.zip_eq_cons_iff.mp h
      subst h_rule h_children
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h_len
      obtain ih' := by
        refine ih trees symbols h_len ?_ (symm h_tail)
        · intro subtree symbol h_mem
          refine derives_of_children subtree symbol ?_
          simp [h_mem]
      rw [List.flatMap_cons, List.map_append, <- List.singleton_append]
      refine derives_of_append ?_ ?_
      · refine derives_of_children subtree symbol ?_
        simp
      · exact ih'
  }
termination_by tree
decreasing_by
  apply List.of_mem_zip at h_mem
  exact sizeOf_lt_of_child h_mem.right

def forestLeaves {cfg : @CFG α ν} (forest : List (ParseTree cfg)) : List α :=
  forest.flatMap fun tree => tree.leaves

def ForestPairValid {cfg : @CFG α ν} : Symbol α ν × ParseTree cfg → Prop
  | (Symbol.term a, Leaf b) => a = b
  | (Symbol.nonterm n, subtree@(Node n' _ _)) => n = n' ∧ subtree.Valid
  | _ => False

def ForestValid {cfg : @CFG α ν}
  (syms : symbols α ν) (forest : List (ParseTree cfg)) : Prop :=
  syms.length = forest.length ∧
    ∀ pair, pair ∈ syms.zip forest → ForestPairValid (cfg := cfg) pair

omit [DecidableEq α] [DecidableEq ν] in
theorem ForestPairValid_iff_valid_and_root
    {cfg : @CFG α ν} {sym : Symbol α ν} {tree : ParseTree cfg} :
    ForestPairValid (cfg := cfg) (sym, tree) ↔
      tree.Valid ∧ tree.root = sym := by
  cases sym <;> cases tree <;>
    simp [ForestPairValid, Valid, root, eq_comm, and_comm]

omit [DecidableEq α] [DecidableEq ν] in
theorem valid_node_iff_ForestValid
    {cfg : @CFG α ν} {n : ν}
    {rule : {rule // rule ∈ cfg.rules n}}
    {children : List (ParseTree cfg)} :
    (Node (cfg := cfg) n rule children).Valid ↔
      ForestValid (cfg := cfg) rule.val children := by
  unfold Valid ForestValid
  constructor <;> rintro ⟨h_len, h_pairs⟩
  all_goals refine ⟨h_len, ?_⟩
  all_goals rintro ⟨sym, tree⟩ h_mem
  all_goals have h_pair := h_pairs (sym, tree) h_mem
  all_goals cases sym <;> cases tree <;>
    simp [ForestPairValid] at h_pair ⊢ <;> assumption

omit [DecidableEq α] [DecidableEq ν] in
theorem ForestValid_iff_forall₂
    {cfg : @CFG α ν} {syms : symbols α ν}
    {forest : List (ParseTree cfg)} :
    ForestValid (cfg := cfg) syms forest ↔
      List.Forall₂
        (fun sym tree => ForestPairValid (cfg := cfg) (sym, tree))
        syms forest := by
  unfold ForestValid
  constructor
  · rintro ⟨h_len, h_pairs⟩
    exact List.forall₂_iff_zip.mpr
      ⟨h_len, fun h_mem => h_pairs _ h_mem⟩
  · intro h
    obtain ⟨h_len, h_pairs⟩ := List.forall₂_iff_zip.mp h
    refine ⟨h_len, ?_⟩
    rintro ⟨sym, tree⟩ h_mem
    exact h_pairs h_mem

omit [DecidableEq α] [DecidableEq ν] in
theorem valid_node_child_at
  {cfg : @CFG α ν} {n} {rule : {rule // rule ∈ cfg.rules n}} {children}
  (hvalid : (Node n rule children).Valid)
  (i : Fin rule.val.length) (j : Fin children.length)
  (hji : j.val = i.val) :
  children[j].Valid ∧ children[j].root = rule.val[i] := by
  have hforall :=
    ForestValid_iff_forall₂.mp (valid_node_iff_ForestValid.mp hvalid)
  let k : Fin children.length := ⟨i.val, hforall.length_eq ▸ i.isLt⟩
  have hp := hforall.get i.isLt k.isLt
  change ForestPairValid (rule.val[i], children[k]) at hp
  rw [ForestPairValid_iff_valid_and_root] at hp
  have hkj : k = j := Fin.ext hji.symm
  simpa [hkj] using hp

omit [DecidableEq α] [DecidableEq ν] in
theorem forestLeaves_map_leaf {cfg : @CFG α ν} (w : List α) :
    forestLeaves (cfg := cfg) (w.map Leaf) = w := by
  induction w <;> simp_all [forestLeaves, leaves]

omit [DecidableEq α] [DecidableEq ν] in
theorem leaves_node_eq_forestLeaves
  {cfg : @CFG α ν} (n : ν) (rule : {rule // rule ∈ cfg.rules n})
  (children : List (ParseTree cfg)) :
    (Node (cfg := cfg) n rule children).leaves = forestLeaves children := by
  simp [leaves, forestLeaves, List.flatMap_subtype, List.unattach_attach]

omit [DecidableEq α] [DecidableEq ν] in
theorem ForestValid_map_leaf {cfg : @CFG α ν} (w : List α) :
    ForestValid (cfg := cfg) (w.map Symbol.term) (w.map Leaf) := by
  rw [ForestValid_iff_forall₂]
  induction w with
  | nil => exact List.Forall₂.nil
  | cons a rest ih =>
      exact List.Forall₂.cons (by simp [ForestPairValid]) ih

omit [DecidableEq α] [DecidableEq ν] in
theorem valid_node_of_ForestValid
  {cfg : @CFG α ν} {n : ν} {rule : {rule // rule ∈ cfg.rules n}}
  {children : List (ParseTree cfg)}
  (h : ForestValid (cfg := cfg) rule.val children) :
    (Node (cfg := cfg) n rule children).Valid :=
  valid_node_iff_ForestValid.mpr h

omit [DecidableEq α] [DecidableEq ν] in
theorem ForestValid_singleton_node
  {cfg : @CFG α ν} {n : ν} {rule : {rule // rule ∈ cfg.rules n}}
  {children : List (ParseTree cfg)}
  (h : ForestValid (cfg := cfg) rule.val children) :
    ForestValid (cfg := cfg) [Symbol.nonterm n] [Node (cfg := cfg) n rule children] := by
  rw [ForestValid_iff_forall₂]
  exact List.Forall₂.cons
    (by simp [ForestPairValid, valid_node_iff_ForestValid.mpr h])
    List.Forall₂.nil

omit [DecidableEq α] [DecidableEq ν] in
theorem ForestValid_append
  {cfg : @CFG α ν} {xs ys : symbols α ν}
  {xf yf : List (ParseTree cfg)}
  (hx : ForestValid (cfg := cfg) xs xf)
  (hy : ForestValid (cfg := cfg) ys yf) :
    ForestValid (cfg := cfg) (xs ++ ys) (xf ++ yf) := by
  rw [ForestValid_iff_forall₂] at hx hy ⊢
  exact List.rel_append hx hy

omit [DecidableEq α] [DecidableEq ν] in
theorem ForestValid_append_inv
  {cfg : @CFG α ν} {xs ys : symbols α ν} {forest : List (ParseTree cfg)}
  (h : ForestValid (cfg := cfg) (xs ++ ys) forest) :
    ∃ xf yf,
      forest = xf ++ yf ∧
      ForestValid (cfg := cfg) xs xf ∧
      ForestValid (cfg := cfg) ys yf := by
  rw [ForestValid_iff_forall₂] at h
  refine ⟨forest.take xs.length, forest.drop xs.length,
    (List.take_append_drop xs.length forest).symm, ?_, ?_⟩
  · rw [ForestValid_iff_forall₂]
    simpa using List.forall₂_take xs.length h
  · rw [ForestValid_iff_forall₂]
    simpa using List.forall₂_drop xs.length h

omit [DecidableEq α] [DecidableEq ν] in
theorem exists_forest_of_terminals {cfg : @CFG α ν} (w : List α) :
    ∃ forest : List (ParseTree cfg),
      ForestValid (cfg := cfg) (w.map Symbol.term) forest ∧
      forestLeaves forest = w := by
  exact ⟨w.map Leaf, ForestValid_map_leaf w, forestLeaves_map_leaf w⟩

omit [DecidableEq α] [DecidableEq ν] in
theorem ForestValid_reverse_step_explicit
  {cfg : @CFG α ν} {pre rhs post : symbols α ν}
  {preForest rhsForest postForest : List (ParseTree cfg)}
  {n : ν} (h_rule : rhs ∈ cfg.rules n)
  (h_pre : ForestValid (cfg := cfg) pre preForest)
  (h_rhs : ForestValid (cfg := cfg) rhs rhsForest)
  (h_post : ForestValid (cfg := cfg) post postForest) :
    ForestValid (cfg := cfg)
      (pre ++ [Symbol.nonterm n] ++ post)
      (preForest ++ [Node (cfg := cfg) n ⟨rhs, h_rule⟩ rhsForest] ++ postForest) := by
  have h_node : ForestValid (cfg := cfg)
      [Symbol.nonterm n] [Node (cfg := cfg) n ⟨rhs, h_rule⟩ rhsForest] :=
    ForestValid_singleton_node h_rhs
  have h_tail := ForestValid_append h_node h_post
  have h_all := ForestValid_append h_pre h_tail
  simpa [List.append_assoc] using h_all

omit [DecidableEq α] [DecidableEq ν] in
theorem ForestValid_reverse_step
  {cfg : @CFG α ν} {pre rhs post : symbols α ν}
  {forest : List (ParseTree cfg)}
  {n : ν} (h_rule : rhs ∈ cfg.rules n)
  (h : ForestValid (cfg := cfg) (pre ++ rhs ++ post) forest) :
    ∃ newForest : List (ParseTree cfg),
      ForestValid (cfg := cfg) (pre ++ [Symbol.nonterm n] ++ post) newForest ∧
      forestLeaves newForest = forestLeaves forest := by
  have h_assoc : ForestValid (cfg := cfg) (pre ++ (rhs ++ post)) forest := by
    simpa [List.append_assoc] using h
  obtain ⟨preForest, tailForest, h_forest, h_pre, h_tail⟩ :=
    ForestValid_append_inv h_assoc
  obtain ⟨rhsForest, postForest, h_tailForest, h_rhs, h_post⟩ :=
    ForestValid_append_inv h_tail
  let newForest :=
    preForest ++ [Node (cfg := cfg) n ⟨rhs, h_rule⟩ rhsForest] ++ postForest
  refine ⟨newForest, ?_, ?_⟩
  · exact ForestValid_reverse_step_explicit h_rule h_pre h_rhs h_post
  · subst newForest
    rw [h_forest, h_tailForest]
    simp [leaves_node_eq_forestLeaves, forestLeaves, List.append_assoc]

omit [DecidableEq α] [DecidableEq ν] in
theorem exists_Valid_tree_of_singleton_forest
  {cfg : @CFG α ν} {n : ν} {w : List α} {forest : List (ParseTree cfg)}
  (h_valid : ForestValid (cfg := cfg) [Symbol.nonterm n] forest)
  (h_leaves : forestLeaves forest = w) :
    ∃ tree : ParseTree cfg,
      tree.Valid ∧ tree.root = Symbol.nonterm n ∧ tree.leaves = w := by
  rw [ForestValid_iff_forall₂] at h_valid
  cases h_valid with
  | cons h_pair h_tail =>
      cases h_tail
      rw [ForestPairValid_iff_valid_and_root] at h_pair
      exact ⟨_, h_pair.1, h_pair.2, by
        simpa [forestLeaves] using h_leaves⟩

theorem exists_forest_of_derives
  {cfg : @CFG α ν} {sentential : symbols α ν} {w : List α}
  (h : cfg.derives sentential (w.map Symbol.term)) :
    ∃ forest : List (ParseTree cfg),
      ForestValid (cfg := cfg) sentential forest ∧
      forestLeaves forest = w := by
  refine Relation.ReflTransGen.head_induction_on h ?_ ?_
  · exact exists_forest_of_terminals w
  · intro v u h_yields _h_derives ih
    obtain ⟨forest, h_forest_valid, h_forest_leaves⟩ := ih
    obtain ⟨pre, n, post, rhs, h_v, h_rhs, h_u⟩ := CFG.yields_decompose h_yields
    have h_forest_valid' :
        ForestValid (cfg := cfg) (pre ++ rhs ++ post) forest := by
      simpa [h_u] using h_forest_valid
    obtain ⟨newForest, h_new_valid, h_new_leaves⟩ :=
      ForestValid_reverse_step (cfg := cfg) (n := n) h_rhs h_forest_valid'
    refine ⟨newForest, ?_, ?_⟩
    · simpa [h_v] using h_new_valid
    · exact h_new_leaves.trans h_forest_leaves

-- Parse-tree completeness for CFG derivations.
theorem exists_Valid_tree_of_derives
  {cfg : @CFG α ν} {n : ν} {w : List α}
  (h : cfg.derives [Symbol.nonterm n] (w.map Symbol.term)) :
    ∃ tree : ParseTree cfg,
      tree.Valid ∧ tree.root = Symbol.nonterm n ∧ tree.leaves = w
  := by
  obtain ⟨forest, h_forest_valid, h_forest_leaves⟩ :=
    exists_forest_of_derives h
  exact exists_Valid_tree_of_singleton_forest h_forest_valid h_forest_leaves

end ParseTree
