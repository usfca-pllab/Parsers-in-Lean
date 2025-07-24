import ParserCombinators.Memoized
import ParserCombinators.CFG

namespace Example2

open Symbol

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
      | S => [[term a, nonterm S], [term a], [term b]]
}

abbrev ValidTree := { tree : ParseTree my_cfg // tree.Valid }

-- A set of parsers

#check Subtype

@[simp]
def parseChar' {μ : Type → Type} [Monad μ] [Alternative μ] (expected : my_alphabet)
    : Parser (tag := emptyTag) UChar μ {t : ValidTree // t.val = ParseTree.Leaf expected } := by
  refine Functor.map ?_ $ terminal (String.mk [expected.val])
  let t : ParseTree my_cfg := ParseTree.Leaf expected
  intro
  refine Subtype.mk ?_ ?_
  · use t
    unfold ParseTree.Valid
    trivial
  · simp only [my_alphabet, ↓Char.isValue]
    subst t
    rfl

@[simp]
def parseA {μ} [Monad μ] [Alternative μ] := parseChar' (μ := μ) a

@[simp]
def parseB {μ} [Monad μ] [Alternative μ] := parseChar' (μ := μ) b

abbrev ValidTreeS := { t : ValidTree // t.val.nonterminal? = some S }

mutual
unsafe def parser1 {μ} [Monad μ] [Alternative μ] [Traversable μ] : Parser (tag := emptyTag) UChar μ ValidTreeS := by
    refine (pure ?_) <*> parseA <*> parseS
    rintro ⟨t, h⟩ ⟨treeS, hS⟩
    let root : ParseTree my_cfg := ParseTree.Node S ⟨[term a, nonterm S], by decide⟩ [t, treeS]
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

unsafe def parseS {μ} [Monad μ] [Alternative μ] [Traversable μ] : Parser (tag := emptyTag) UChar μ ValidTreeS :=
  let parser2 : Parser UChar μ ValidTreeS := by
    refine ?_ <$> parseA
    rintro ⟨t, h⟩
    let root : ParseTree my_cfg := ParseTree.Node S ⟨[term a], by decide⟩ [t]
    refine Subtype.mk (Subtype.mk root ?_) (of_eq_true (eq_self (some S)))
    unfold ParseTree.Valid
    simp_all [↓Char.isValue]
    intro a b _h
    simp_all only [↓Char.isValue, my_alphabet, of]
    obtain ⟨val, property⟩ := t
    obtain ⟨left, right⟩ := _h
    subst left right
    simp_all only [↓Char.isValue]
  let parser3 : Parser UChar μ ValidTreeS := by
    refine ?_ <$> parseB
    rintro ⟨t, h⟩
    let root : ParseTree my_cfg := ParseTree.Node S ⟨[term b], by decide⟩ [t]
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
  (parser1 <|> (parser2 <|> parser3))
end

#check runParser'
#check (runParser' parseS "ab").1.values.flatten
#check (runParser' (μ := Option) parseS "ab").1.values

-- This breaks due to reaching maximum recursion depth
-- #reduce (runParser.{1} parseS "ab").1.toList
-- #reduce (runParser (μ := Option) parseS "ab").1.values

end Example2
