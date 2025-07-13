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
def my_vars : Finset ℕ := {1,2,3}

instance : OfNat my_vars 1 where
  ofNat := ⟨1, by decide⟩

instance : OfNat my_vars 2 where
  ofNat := ⟨2, by decide⟩

instance : OfNat my_vars 3 where
  ofNat := ⟨3, by decide⟩

@[simp]
def my_alphabet : Finset Char := {'a', 'b', 'c'}

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
@[simp]
def yield {cfg : @CFG α ν} (deriv : symbols α ν) : List (symbols α ν) := do
  let init ← List.inits deriv
  let Option.some (List.cons (Symbol.nonterm x) tail) := List.getRest deriv init
    | []  -- eliminate positions that do not start with a variable
  (fun rhs => init ++ rhs ++ tail) <$> cfg.rules x

def my_str : symbols my_alphabet my_vars := [term a, nonterm 1, term c]

#eval my_cfg.yield my_str

-- Relation version of the step function
@[simp]
def yields {cfg : @CFG α ν} (a b : symbols α ν) := b ∈ cfg.yield a

instance {cfg : @CFG α ν} (a b : symbols α ν) : Decidable (cfg.yields a b) :=
  if h : b ∈ cfg.yield a then isTrue h else isFalse h

example : my_cfg.yields [term a, nonterm 1, term c] [term a, term c] := by
  simp only [yields]
  decide

-- Derives: transitive reflexive closure of yields.
-- NOTE(maemre): This is potentially noncomputable, might need a step index
@[simp]
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
example : my_cfg.derives_nth 5 [term a, nonterm 1, term c] [term a, term a, term a, term a, term c] := by decide

private lemma derives_to_derives_nth {cfg : @CFG α ν} (v w : symbols α ν) : cfg.derives v w -> ∃ n : ℕ, cfg.derives_nth n v w := by
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

private lemma derives_from_derives_nth {cfg : @CFG α ν} (v w : symbols α ν) : (∃ n : ℕ, cfg.derives_nth n v w) -> cfg.derives v w := by
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
      exact ih u h_recur

theorem derives_iff_derives_nth {cfg : @CFG α ν} (v w : symbols α ν) : cfg.derives v w ↔ ∃ n : ℕ, cfg.derives_nth n v w :=
  ⟨derives_to_derives_nth v w, derives_from_derives_nth v w⟩

-- A parse tree according to given grammar.  It stores which rule is used to build the current node.
inductive ParseTree (cfg : @CFG α ν) : Type ((max u v) + 1) where
  | Leaf (t : α)
  | Node (n : ν) (rule : {rule // rule ∈ cfg.rules n}) (children : List (ParseTree cfg))

namespace ParseTree

def my_tree : ParseTree my_cfg := ParseTree.Node 1 ⟨[], by decide⟩ []

@[simp]
def children {cfg : @CFG α ν} : ParseTree cfg → List (ParseTree cfg)
  | ParseTree.Node _ _ children => children
  | ParseTree.Leaf _ => []

@[simp]
def nonterminal {cfg : @CFG α ν} : ParseTree cfg → Option ν
  | ParseTree.Node n _ _ => n
  | ParseTree.Leaf _ => none

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


def leaves {cfg : @CFG α ν} (tree : ParseTree cfg) : symbols α ν := match tree with
  | ParseTree.Leaf a => [term a]
  | ParseTree.Node _ _ children => children.attach.flatMap (fun ⟨node, _h_mem⟩ => leaves node)
termination_by tree
decreasing_by
  exact sizeOf_lt_of_child _h_mem

#guard leaves my_tree == []

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

#guard my_tree.valid

lemma lift_forall {α} {p q : α → Prop} (h : ∀ x, p x ↔ q x) : (∀ x, p x) ↔ (∀ x, q x) :=
    of_eq_true
      (Eq.trans
        (congrArg (fun x ↦ x ↔ ∀ (x : α), q x) (forall_congr fun x ↦ (fun x ↦ propext (h x)) x))
        (iff_self (∀ (x : α), q x)))

lemma valid_eq_true_iff_valid {cfg : @CFG α ν} {tree : ParseTree cfg} : tree.valid = true ↔ tree.Valid := match h : tree with
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
        have h' := @valid_eq_true_iff_valid cfg subtree
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
  decidable_of_iff (tree.valid = true) valid_eq_true_iff_valid

example : Valid my_tree := by
  native_decide

end ParseTree
