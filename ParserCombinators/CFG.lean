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

universe u v
variable (α : Type u) (ν : Type v) [DecidableEq α] [DecidableEq ν]

-- Symbol
inductive Symbol where
  | term    : α -> Symbol
  | nonterm : ν -> Symbol
  deriving DecidableEq, Repr

-- Derivation strings.  Also used as right-hand sides for CFG rules
@[simp]
abbrev symbols := List (Symbol α ν)

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

def my_cfg : CFG my_alphabet my_vars := {
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
def yield {cfg : CFG α ν} (deriv : symbols α ν) : List (symbols α ν) := do
  let init ← List.inits deriv
  let Option.some (List.cons (Symbol.nonterm x) tail) := List.getRest deriv init
    | []  -- eliminate positions that do not start with a variable
  (fun rhs => init ++ rhs ++ tail) <$> cfg.rules x

def my_str : symbols my_alphabet my_vars := [term a, nonterm 1, term c]

#eval my_cfg.yield my_alphabet my_vars my_str

-- Relation version of the step function
@[simp]
def yields {cfg : CFG α ν} (a b : symbols α ν) := b ∈ cfg.yield α ν a

example : my_cfg.yields my_alphabet my_vars [term a, nonterm 1, term c] [term a, term c] := by
  simp only [yields]
  decide

-- Derives: transitive reflexive closure of yields.
-- NOTE(maemre): This is potentially noncomputable, might need a step index
@[simp]
def derives {cfg : CFG α ν} : (symbols α ν) → (symbols α ν) → Prop :=
  Relation.ReflTransGen (cfg.yields α ν)

example : my_cfg.derives my_alphabet my_vars [term a, nonterm 1, term c] [term a, term a, term c] := by
  have rel := my_cfg.derives my_alphabet my_vars
  have x : symbols my_alphabet my_vars := [term a, nonterm 1, term c]
  have y : symbols my_alphabet my_vars := [term a, nonterm 1, term a, term c]
  have z : symbols my_alphabet my_vars := [term a, term a, term c]
  simp
  have nicer : Relation.ReflTransGen rel x z := by
    refine @Relation.ReflTransGen.head (symbols my_alphabet my_vars) rel x y z ?_ ?_
    sorry
    sorry
  -- simp [rel, x, y, z] at nicer
  sorry
