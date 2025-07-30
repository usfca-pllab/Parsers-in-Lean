/-
Context-free grammars along with derivation and parsing relations.

Conventions:
- `ν` is the type of nonterminals/variables.
- `α` is the type of terminals (the alphabet).
-/
import Batteries.Data.List.Basic
import Mathlib.Data.List.Monad
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
  let init ← List.inits deriv
  let Option.some (List.cons (Symbol.nonterm x) tail) := List.getRest deriv init
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

theorem yields_not_empty {cfg : @CFG α ν} {w : symbols α ν} (h : cfg.yields [] w) : False := by
  simp [yields, List.getRest] at h

theorem yields_of_cons {cfg : @CFG α ν} (σ : Symbol α ν) (v w : symbols α ν) (h : cfg.yields v w)
  : cfg.yields (σ :: v) (σ :: w) := by
  simp_all
  obtain ⟨a, h₁, h₂⟩ := h
  right
  use a
  simp [h₁]
  split at h₂
  · simp at h₂
    simp [h₂]
  · simp at h₂

theorem yields_of_append_left {cfg : @CFG α ν} (v₁ v₂ w : symbols α ν) (h : cfg.yields v₁ w)
    : cfg.yields (v₁ ++ v₂) (w ++ v₂) := by
  induction v₁ generalizing v₂ w
  · apply yields_not_empty at h
    contradiction

  · rename_i head tail ih
    repeat rewrite [List.cons_append]
    simp_all [List.getRest]
    cases h
    · rename_i h
      cases head with
      | term t =>
        simp at h
      | nonterm n =>
        left
        simp_all
        obtain ⟨a, h₁, h₂⟩ := h
        use a
        subst h₂
        simp_all only [List.append_assoc, and_self]
    · rename_i h
      obtain ⟨a, h₁, h₂⟩ := h
      right
      left
      use a
      simp [*]
      split at h₂
      · simp at h₂
        obtain ⟨a, h₂⟩ := h₂
        simp_all
        use a
        simp_all only [true_and]
        obtain ⟨left, right⟩ := h₂
        subst right
        simp_all only [List.cons_append, List.append_assoc]
      · simp at h₂

theorem yields_of_append_right {cfg : @CFG α ν} (v₁ v₂ w : symbols α ν) (h : cfg.yields v₁ w)
    : cfg.yields (v₂ ++ v₁) (v₂ ++ w) := by
  induction v₂
  · simp [-yields, h]
  · rename_i head tail ih
    simp
    right
    simp at ih
    obtain ⟨a, ih⟩ := ih
    split at ih
    · rename_i ih
      obtain ⟨h₁, h₂⟩ := ih
      left
      use a
      simp_all only [true_and, List.mem_map]
      obtain ⟨rule, h₂⟩ := h₂
      use rule
      simp [h₂]
    · rename_i ih
      obtain ⟨h₁, h₂⟩ := ih
      contradiction
    · rename_i ih
      obtain ⟨a, h₁, h₂⟩ := ih
      right
      use (head :: a)
      simp_all only [yields, symbols, yield, List.append_assoc, List.map_eq_map,
        List.bind_eq_flatMap, List.mem_flatMap, List.mem_inits, getRest_cons, List.cons_append]
      constructor
      · rw [<- List.map_tail, List.mem_map]
        rw [<- List.map_tail, List.mem_map] at h₁
        simp [h₁]
      · split at h₂
        · simp_all
        · contradiction

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

-- Indexed version of `derives`
def derives_nth {cfg : @CFG α ν} (n : ℕ) (v w : symbols α ν) : Prop := v = w ∨ match n with
  | 0 => v = w
  | Nat.succ n' => ∃ u, cfg.yields v u ∧ cfg.derives_nth n' u w

-- Decidable instance for the indexed step relation
instance {cfg : @CFG α ν} (n : ℕ) (v w : symbols α ν) : Decidable (cfg.derives_nth n v w) := by induction n generalizing v with
  | zero =>
    unfold derives_nth
    refine decidable_of_iff (v = w) ?_
    simp only [or_self]
  | succ n' ih =>
    unfold derives_nth
    if h : v = w then exact isTrue (Or.inl h)
    else
      let recur (u : symbols α ν) := cfg.derives_nth n' u w
      refine decidable_of_iff (∃ u ∈ (cfg.yield v).toFinset, recur u) ?_
      unfold yields
      simp only [h, false_or]
      have h' (u : symbols α ν) := @List.mem_toFinset (symbols α ν) inferInstance (cfg.yield v) u
      have h'' (p :symbols α ν → Prop) : (∃ u ∈ cfg.yield v, p u) <-> (∃ u ∈ (cfg.yield v).toFinset, p u) := by simp
      rw [h'' recur]

-- With the `Decidable` instance above, we can *inefficiently* decide bounded instances of the derivation relation.
example : my_cfg.derives_nth 2 [term a, nonterm 1, term c] [term a, term a, term c] := by decide
-- this search is really inefficient but it works
-- example : my_cfg.derives_nth 5 [term a, nonterm 1, term c] [term a, term a, term a, term a, term c] := by decide

private lemma derives_nth_of_derives {cfg : @CFG α ν} (v w : symbols α ν) : cfg.derives v w -> ∃ n : ℕ, cfg.derives_nth n v w := by
  intro h
  refine Relation.ReflTransGen.head_induction_on h ?_ ?_
  · use 0
    simp [derives_nth]
  · rintro v u h_yields h_derives ⟨n, ih⟩
    use n + 1
    unfold derives_nth
    right
    simp only []
    use u

private lemma derives_of_derives_nth {cfg : @CFG α ν} (v w : symbols α ν) : (∃ n : ℕ, cfg.derives_nth n v w) -> cfg.derives v w := by
  intro ⟨n, h⟩
  induction n generalizing v with
  | zero =>
    simp only [derives_nth, or_self] at h
    simp only [derives, h]
    exact Relation.ReflTransGen.refl
  | succ n' ih =>
    unfold derives_nth at h
    simp only [] at h
    refine Or.by_cases h ?_ ?_
    · intro h
      simp only [derives, h]
      exact Relation.ReflTransGen.refl
    · intro ⟨u, ⟨h_yields, h_recur⟩⟩
      unfold derives
      refine @Relation.ReflTransGen.head (symbols α ν) cfg.yields v u w ?_ ?_
      · exact h_yields
      · exact ih u h_recur

theorem derives_iff_derives_nth {cfg : @CFG α ν} (v w : symbols α ν) : cfg.derives v w ↔ ∃ n : ℕ, cfg.derives_nth n v w :=
  ⟨derives_nth_of_derives v w, derives_of_derives_nth v w⟩

theorem derives_empty_of_empty  {cfg : @CFG α ν} {w : symbols α ν} (h₁ : cfg.derives [] w) : w = [] := by
  simp [derives] at h₁
  induction h₁ with
  | refl => rfl
  | tail _ h_yields h_empty =>
      subst h_empty
      simp [List.getRest] at h_yields

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
def isLeaf {cfg : @CFG α ν} : (ParseTree cfg) → Bool
  | Node _ _ _ => false
  | Leaf _ => true

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

lemma lift_forall {α} {p q : α → Prop} (h : ∀ x, p x ↔ q x) : (∀ x, p x) ↔ (∀ x, q x) :=
    of_eq_true
      (Eq.trans
        (congrArg (fun x ↦ x ↔ ∀ (x : α), q x) (forall_congr fun x ↦ (fun x ↦ propext (h x)) x))
        (iff_self (∀ (x : α), q x)))

lemma valid_eq_true_iff_Valid {cfg : @CFG α ν} {tree : ParseTree cfg} : tree.valid = true ↔ tree.Valid := match h : tree with
  | ParseTree.Leaf _ => by unfold valid Valid ; decide
  | ParseTree.Node n rule children => by {
    unfold valid Valid
    subst h
    simp_all [symbols]
    intro h_eq_len
    apply lift_forall
    intro a
    repeat (apply lift_forall ; intro)
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
    -- apply derives_of_derives_nth
    refine @Relation.ReflTransGen.head (symbols α ν) cfg.yields ?_ rule ?_ ?_ ?_
    · unfold yields
      unfold yield
      simp [List.getRest, property]
    · simp only [symbols, leaves, List.flatMap_subtype, List.unattach_attach]
      have derives_of_children (subtree : ParseTree cfg) (a : Symbol α ν) (h_mem : (a, subtree) ∈ (List.zip rule children))
          : cfg.derives [a] (subtree.leaves.map term)
        := by {
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
      clear h_recur property
      induction h : rule.zip children generalizing rule children with
      | nil =>
        replace h := zip_eq_nil_of_eq_length h_len h
        simp [h]
        exact Relation.ReflTransGen.refl
      | cons head tail ih =>
        obtain ⟨symbol, subtree⟩ := head
        obtain ⟨symbols, trees, h_rule, h_children, h_tail⟩ := List.zip_eq_cons_iff.mp h
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

end ParseTree
