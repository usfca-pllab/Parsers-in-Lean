From Stdlib Require Import
  ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlString List PeanoNat String.
From CoStar Require Import Defs Main Orders.

Module Export Indexed_Types <: SYMBOL_TYPES.

  Definition terminal := nat.
  Definition nonterminal := nat.

  Definition compareIndex := Nat.compare.

  Lemma compareIndex_eq :
    forall x y, compareIndex x y = Eq <-> x = y.
  Proof.
    exact Nat.compare_eq_iff.
  Qed.

  Lemma compareIndex_trans :
    forall c x y z,
      compareIndex x y = c ->
      compareIndex y z = c ->
      compareIndex x z = c.
  Proof.
    intros c x y z hxy hyz; destruct c.
    - apply Nat.compare_eq_iff in hxy.
      apply Nat.compare_eq_iff in hyz.
      subst; apply Nat.compare_refl.
    - apply Nat.compare_lt_iff in hxy.
      apply Nat.compare_lt_iff in hyz.
      apply Nat.compare_lt_iff.
      eapply Nat.lt_trans; eauto.
    - apply Nat.compare_gt_iff in hxy.
      apply Nat.compare_gt_iff in hyz.
      apply Nat.compare_gt_iff.
      eapply Nat.lt_trans; eauto.
  Qed.

  Definition compareT := compareIndex.
  Definition compareNT := compareIndex.

  Lemma compareT_eq :
    forall x y : terminal, compareT x y = Eq <-> x = y.
  Proof. exact compareIndex_eq. Qed.

  Lemma compareT_trans :
    forall c (x y z : terminal),
      compareT x y = c -> compareT y z = c -> compareT x z = c.
  Proof. exact compareIndex_trans. Qed.

  Lemma compareNT_eq :
    forall x y : nonterminal, compareNT x y = Eq <-> x = y.
  Proof. exact compareIndex_eq. Qed.

  Lemma compareNT_trans :
    forall c (x y z : nonterminal),
      compareNT x y = c -> compareNT y z = c -> compareNT x z = c.
  Proof. exact compareIndex_trans. Qed.

  Definition showT (_ : terminal) : string := "".
  Definition showNT (_ : nonterminal) : string := "".

End Indexed_Types.

Module Export D <: Defs.T.
  Module Export SymTy := Indexed_Types.
  Module Export Defs := DefsFn SymTy.
End D.

Module Export PG := Make D.

Require Extraction.
Set Extraction Output Directory "extracted".
Separate Extraction D PG parse.
