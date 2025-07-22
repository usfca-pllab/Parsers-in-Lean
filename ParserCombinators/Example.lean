import ParserCombinators.Basic
import ParserCombinators.CFG

namespace Example

open Symbol
open ParserCombinators.Basic

inductive MyVars where
  | S
  deriving DecidableEq, Repr

open MyVars

@[simp]
private def my_alphabet : Finset Char := {'a', 'b', 'c'}

@[simp]
private def of (c : Char ) ( h : c ∈ my_alphabet ) : my_alphabet := ⟨c, h⟩

@[simp]
private def a_in : 'a' ∈ my_alphabet := by decide

@[simp]
private def b_in : 'b' ∈ my_alphabet := by decide

@[simp]
private def c_in : 'c' ∈ my_alphabet := by decide

private abbrev a := of 'a' a_in
private abbrev b := of 'b' b_in
private abbrev c := of 'c' c_in

/-

An ε-free, non-left-recursive grammar:

1 → a 1 | a | b

-/
private def my_cfg : @CFG my_alphabet MyVars := {
  start := S
  rules :=
    let a := of 'a' a_in
    fun x =>
    match x with
      | S => [[Term a, Nonterm S], [Term a], [Term b]]
}

abbrev ValidTree := { tree : ParseTree my_cfg // tree.Valid }

-- A set of parsers

@[simp]
def parseChar' (expected : my_alphabet) : Parser {t : ValidTree // t.val = ParseTree.Leaf expected } := by
  refine map ?_ $ parseChar (fun c => c == expected)
  rintro ⟨c, h⟩
  apply eq_of_beq at h
  let t : ParseTree my_cfg := ParseTree.Leaf expected
  refine Subtype.mk ?_ ?_
  · use t
    unfold ParseTree.Valid
    trivial
  · simp only [my_alphabet, ↓Char.isValue]
    subst t
    rfl

@[simp]
def parseA := parseChar' a

@[simp]
def parseB := parseChar' b

abbrev ValidTreeS := { t : ValidTree // t.val.nonterminal? = some S }

mutual
unsafe def parser1 : Parser ValidTreeS := by
    refine map ?_ (concat parseA parseS)
    rintro ⟨⟨t, h⟩, ⟨treeS, hS⟩⟩
    let root : ParseTree my_cfg := ParseTree.Node S ⟨[Term a, Nonterm S], by decide⟩ [t, treeS]
    refine Subtype.mk (Subtype.mk root ?_) (of_eq_true (eq_self (some S)))
    unfold ParseTree.Valid
    simp at hS
    split at hS
    · rename_i n rule children heq
      simp_all [↓Char.isValue]
      intro a b _h
      simp_all only [↓Char.isValue, my_alphabet, of]
      obtain ⟨val, property⟩ := t
      obtain ⟨val_1, property_1⟩ := treeS
      obtain ⟨val_2, property_2⟩ := rule
      simp_all only [↓Char.isValue]
      cases _h with
      | inl h_1 =>
        obtain ⟨left, right⟩ := h_1
        subst left right
        simp_all only [↓Char.isValue]
      | inr h_2 =>
        obtain ⟨left, right⟩ := h_2
        subst left right
        simp_all only [↓Char.isValue, symbols]
        subst heq h
        simp_all only [↓Char.isValue]

    · contradiction

unsafe def parseS : Parser ValidTreeS :=
  let parser2 : Parser ValidTreeS := by
    refine map ?_ parseA
    rintro ⟨t, h⟩
    let root : ParseTree my_cfg := ParseTree.Node S ⟨[Term a], by decide⟩ [t]
    refine Subtype.mk (Subtype.mk root ?_) (of_eq_true (eq_self (some S)))
    unfold ParseTree.Valid
    simp_all [↓Char.isValue]
    intro a b _h
    simp_all only [↓Char.isValue, my_alphabet, of]
    obtain ⟨val, property⟩ := t
    obtain ⟨left, right⟩ := _h
    subst left right
    simp_all only [↓Char.isValue]
  let parser3 : Parser ValidTreeS := by
    refine map ?_ parseB
    rintro ⟨t, h⟩
    let root : ParseTree my_cfg := ParseTree.Node S ⟨[Term b], by decide⟩ [t]
    refine Subtype.mk (Subtype.mk root ?_) (of_eq_true (eq_self (some S)))
    unfold ParseTree.Valid
    simp_all [↓Char.isValue]
    intro a b _h
    simp_all only [↓Char.isValue, my_alphabet, of]
    obtain ⟨val, property⟩ := t
    obtain ⟨left, right⟩ := _h
    subst left right
    simp_all only [↓Char.isValue]

  -- TODO(maemre): try extracting the parser function for building it explicitly
  (or_parser parser1 (or_parser parser2 parser3))
end

-- Replacing `#reduce` with `#eval` crashes with a stack overflow
#reduce ((parseS.run "ab".data).map (fun (tree, _) => tree.val.val)).getD (ParseTree.Leaf a)

end Example
