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

theorem yields_decompose
  {cfg : @CFG α ν} {v u : symbols α ν}
  (h : cfg.yields v u) :
    ∃ pre n post rhs,
      v = pre ++ [Symbol.nonterm n] ++ post ∧
      rhs ∈ cfg.rules n ∧
      u = pre ++ rhs ++ post := by
  unfold yields yield at h
  simp only [List.bind_eq_flatMap, List.mem_flatMap, List.mem_inits] at h
  obtain ⟨pre, h_prefix, h_rest⟩ := h
  cases h_get : List.getRest v pre with
  | none =>
      simp [h_get] at h_rest
  | some rest =>
      cases rest with
      | nil =>
          simp [h_get] at h_rest
      | cons sym post =>
          cases sym with
          | term _ =>
              simp [h_get] at h_rest
          | nonterm n =>
              simp [h_get] at h_rest
              obtain ⟨rhs, h_rhs, h_u⟩ := h_rest
              refine ⟨pre, n, post, rhs, ?_, h_rhs, ?_⟩
              · obtain ⟨suffix, h_v⟩ := h_prefix
                have h_suffix : suffix = Symbol.nonterm n :: post := by
                  rw [← h_v] at h_get
                  nth_rw 2 [show pre = pre ++ ([] : List (Symbol α ν)) by simp] at h_get
                  change List.getRest (pre ++ suffix)
                    (pre ++ ([] : List (Symbol α ν))) = some (Symbol.nonterm n :: post) at h_get
                  rw [getRest_elim_prefix] at h_get
                  simpa [List.getRest] using h_get
                rw [← h_v, h_suffix]
                simp
              · simpa [List.append_assoc] using h_u.symm

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
theorem forestLeaves_map_leaf {cfg : @CFG α ν} (w : List α) :
    forestLeaves (cfg := cfg) (w.map Leaf) = w := by
  induction w with
  | nil => rfl
  | cons a rest ih =>
      unfold forestLeaves at ih ⊢
      simp only [List.map_cons, List.flatMap_cons]
      have h_leaf : (Leaf (cfg := cfg) a).leaves = [a] := by
        unfold leaves
        rfl
      rw [h_leaf]
      simp [ih]

omit [DecidableEq α] [DecidableEq ν] in
theorem forestLeaves_append
  {cfg : @CFG α ν} (xs ys : List (ParseTree cfg)) :
    forestLeaves (xs ++ ys) = forestLeaves xs ++ forestLeaves ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      unfold forestLeaves at ih ⊢
      simp [ih, List.append_assoc]

omit [DecidableEq α] [DecidableEq ν] in
theorem leaves_node_eq_forestLeaves
  {cfg : @CFG α ν} (n : ν) (rule : {rule // rule ∈ cfg.rules n})
  (children : List (ParseTree cfg)) :
    (Node (cfg := cfg) n rule children).leaves = forestLeaves children := by
  simp [leaves, forestLeaves, List.flatMap_subtype, List.unattach_attach]

omit [DecidableEq α] [DecidableEq ν] in
theorem ForestValid_map_leaf {cfg : @CFG α ν} (w : List α) :
    ForestValid (cfg := cfg) (w.map Symbol.term) (w.map Leaf) := by
  induction w with
  | nil =>
      unfold ForestValid
      simp
  | cons a rest ih =>
      unfold ForestValid at ih ⊢
      constructor
      · simp
      · intro pair h_pair
        simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at h_pair
        cases h_pair with
        | inl h_head =>
            cases h_head
            rfl
        | inr h_tail =>
            exact ih.2 pair h_tail

omit [DecidableEq α] [DecidableEq ν] in
theorem valid_node_of_ForestValid
  {cfg : @CFG α ν} {n : ν} {rule : {rule // rule ∈ cfg.rules n}}
  {children : List (ParseTree cfg)}
  (h : ForestValid (cfg := cfg) rule.val children) :
    (Node (cfg := cfg) n rule children).Valid := by
  unfold ForestValid at h
  unfold Valid
  constructor
  · exact h.1
  · intro pair h_pair
    have h_pair_valid := h.2 pair h_pair
    cases pair with
    | mk sym tree =>
        cases sym <;> cases tree <;> simp [ForestPairValid] at h_pair_valid ⊢ <;> exact h_pair_valid

omit [DecidableEq α] [DecidableEq ν] in
theorem ForestValid_singleton_node
  {cfg : @CFG α ν} {n : ν} {rule : {rule // rule ∈ cfg.rules n}}
  {children : List (ParseTree cfg)}
  (h : ForestValid (cfg := cfg) rule.val children) :
    ForestValid (cfg := cfg) [Symbol.nonterm n] [Node (cfg := cfg) n rule children] := by
  unfold ForestValid
  constructor
  · simp
  · intro pair h_pair
    simp at h_pair
    cases h_pair
    simp [ForestPairValid, valid_node_of_ForestValid h]

omit [DecidableEq α] [DecidableEq ν] in
theorem ForestValid_append
  {cfg : @CFG α ν} {xs ys : symbols α ν}
  {xf yf : List (ParseTree cfg)}
  (hx : ForestValid (cfg := cfg) xs xf)
  (hy : ForestValid (cfg := cfg) ys yf) :
    ForestValid (cfg := cfg) (xs ++ ys) (xf ++ yf) := by
  unfold ForestValid at hx hy ⊢
  constructor
  · simp [hx.1, hy.1]
  · intro pair h_pair
    rw [List.zip_append] at h_pair
    · cases List.mem_append.mp h_pair with
      | inl h_left => exact hx.2 pair h_left
      | inr h_right => exact hy.2 pair h_right
    · exact hx.1

omit [DecidableEq α] [DecidableEq ν] in
theorem ForestValid_append_inv
  {cfg : @CFG α ν} {xs ys : symbols α ν} {forest : List (ParseTree cfg)}
  (h : ForestValid (cfg := cfg) (xs ++ ys) forest) :
    ∃ xf yf,
      forest = xf ++ yf ∧
      ForestValid (cfg := cfg) xs xf ∧
      ForestValid (cfg := cfg) ys yf := by
  induction xs generalizing forest with
  | nil =>
      refine ⟨[], forest, by simp, ?_, ?_⟩
      · unfold ForestValid
        simp
      · simpa using h
  | cons x xs ih =>
      obtain ⟨h_len, h_pairs⟩ := h
      cases forest with
      | nil =>
          simp at h_len
      | cons tree forestTail =>
          have h_head : ForestPairValid (cfg := cfg) (x, tree) := by
            exact h_pairs (x, tree) (by simp)
          have h_tail : ForestValid (cfg := cfg) (xs ++ ys) forestTail := by
            unfold ForestValid
            constructor
            · simpa using h_len
            · intro pair h_pair
              exact h_pairs pair (by simp [h_pair])
          obtain ⟨xf, yf, h_tail_eq, h_xs, h_ys⟩ := ih h_tail
          refine ⟨tree :: xf, yf, ?_, ?_, h_ys⟩
          · simp [h_tail_eq]
          · unfold ForestValid at h_xs ⊢
            constructor
            · simp [h_xs.1]
            · intro pair h_pair
              simp at h_pair
              cases h_pair with
              | inl h_eq =>
                  cases h_eq
                  exact h_head
              | inr h_tail_pair =>
                  exact h_xs.2 pair h_tail_pair

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
  obtain ⟨h_len, h_pairs⟩ := h_valid
  cases forest with
  | nil =>
      simp at h_len
  | cons tree tail =>
      cases tail with
      | nil =>
          have h_pair := h_pairs (Symbol.nonterm n, tree) (by simp)
          cases tree with
          | Leaf a =>
              simp [ForestPairValid] at h_pair
          | Node n' rule children =>
              simp [ForestPairValid] at h_pair
              obtain ⟨h_n, h_tree_valid⟩ := h_pair
              cases h_n
              refine ⟨Node n rule children, h_tree_valid, rfl, ?_⟩
              simpa [forestLeaves] using h_leaves
      | cons _ _ =>
          simp at h_len

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
