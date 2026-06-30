From Stdlib Require Import List RelationClasses SetoidList.
From LJF Require Import SetoidList_Extended.

Fixpoint prepend_all [A: Type] (B : A) (L : list (list A)) : list (list A) := 
  match L with
  | nil       => nil
  | L1 :: L'  => (B :: L1) :: (prepend_all B L')
  end
.

Lemma prepend_all_iff {A: Type} :
  forall (B: A) {L1 : list A} {L : list (list A)},
    In L1 L <-> In (B :: L1) (prepend_all B L).
Proof.
  intros B L1 L. revert B L1. induction L.
  - intros. split.
    + intro. simpl in*. apply H.
    + intro. simpl in*. apply H.
  - intros. split.
    + simpl. intro. destruct H.
      -- subst. left. reflexivity.
      -- right. apply (proj1 (IHL B L1) H).
    + simpl. intro. destruct H. 
      -- inversion H. subst. left. reflexivity.
      -- right. apply (proj2 (IHL B L1 ) H).
Qed.

Lemma prepend_all_inv {A : Type} :
  forall {B : A} {L1 : list A} {L : list (list A)}, 
  In L1 (prepend_all B L) -> exists L2, L1 = B :: L2 /\ In L2 L.
Proof.
   induction L.
   - intros. simpl in H. inversion H.
   - intros. simpl in H. destruct H.
      ++ eexists a. split. symmetry. apply H. apply in_eq.
      ++ specialize (IHL H). destruct IHL. destruct H0.
         subst. eexists x. split. reflexivity. apply in_cons. apply H1.
Qed.

Lemma NoDupA_prepend_all [A: Type] {eqA : relation A} `{Equivalence A eqA} :
  forall {B: A} {L: list (list A)},
  NoDupA (equivlistA eqA) L -> 
  Forall (fun a => ~ InA eqA B a) L -> 
  NoDupA (equivlistA eqA) (prepend_all B L).
Proof.
  induction L.
  - intros. simpl. apply NoDupA_nil.
  - intros. simpl.
    apply NoDupA_cons.
    + intro.
      inversion H0 ; subst ; clear H0.
      inversion H1 ; subst ; clear H1.
      destruct (proj1 (InA_alt _ _ _) H2) ; destruct H0.
      apply prepend_all_inv in H1 as [y [-> Hy]].
      assert (equivlistA eqA a y).
      -- intro x. specialize (H0 x) ; destruct H0. split.
        ++ intro. destruct (InA_cons eqA x B a).
          specialize (H9 (or_intror H3)).
          specialize (H0 H9). apply InA_cons in H0. destruct H0.
          --- exfalso. apply H4. apply (InA_eqA H H0 H3).
          --- apply H0.
        ++ intro. destruct (InA_cons eqA x B y).
          specialize (H9 (or_intror H3)).
          specialize (H1 H9). apply InA_cons in H1. destruct H1.
          --- exfalso. apply Forall_forall with (x := y) in H7. apply H7. apply (InA_eqA H H1 H3). apply Hy.
          --- apply H1.
      -- apply H5.
        symmetry in H1. apply (InA_eqA (equivlist_equiv H) H1 (In_InA (equivlist_equiv H) Hy)).
    + inversion H0 ; subst. inversion H1 ; subst. apply (IHL H5 H7).
Qed.

Fixpoint get_all_subsets [A: Type] (L : list A) : list (list A) := 
    match L with
    | nil       => nil :: nil
    | B :: L'   => let L0 := get_all_subsets L' in L0 ++ (prepend_all B L0)
    end.

Lemma inclA_iff_get_all_subsets [A: Type] 
  {eqA : relation A} `{Equivalence A eqA} (eqA_dec : forall x y, {eqA x y} + {~ eqA x y}):
  forall {L2 L1: list A}, inclA eqA L1 L2 <-> InA (equivlistA eqA) L1 (get_all_subsets L2).
Proof.
  specialize (equivlist_equiv H) ; intro. induction L2 ; intros ; split ; intro.
  - simpl. destruct L1.
    + simpl. apply InA_cons_hd. reflexivity.
    + simpl. assert (eqA a a). reflexivity. exfalso.
      specialize (H1 a (InA_cons_hd L1 H2)). apply (proj1 (InA_nil eqA a ) H1).
  - simpl in H1. destruct (proj1 (InA_cons (equivlistA eqA) L1 nil nil) H1).
    + intro x. intro. apply (proj1 (H2 x) H3).
    + exfalso. apply (proj1 (InA_nil (equivlistA eqA) L1) H2).
  - simpl. destruct (proj1 (inclA_removeA_iff eqA_dec) H1).
    + apply InA_app_iff. right.
      destruct H2. specialize (proj1 (IHL2 _) H3). intro.
      apply InA_alt in H4 as [y [H4 H5]].
      apply InA_alt. eexists (a :: y).
      split.
      -- intro x. split.
        ++ intro. destruct (eqA_dec x a).
          --- apply (InA_cons_hd y e).
          --- destruct (H4 x).
            specialize (H7 (proj2 (removeA_InA H eqA_dec L1 a x) (conj H6 (eqA_not_symmetry n)))).
            apply (InA_cons_tl a H7).
        ++ intro. destruct (proj1 (InA_cons eqA x a y) H6).
          --- rewrite H7. apply H2.
          --- apply (proj1 (removeA_InA H eqA_dec L1 a x) (proj2 (H4 x) H7)).
      -- apply (proj1 (prepend_all_iff a) H5).
    + apply InA_app_iff. left.
      destruct H2.
      apply (proj1 (IHL2 L1) H3).
  - simpl in H1. destruct (proj1 (InA_app_iff _ _ _ _) H1).
    + apply (inclA_cons_2 a (proj2 (IHL2 L1) H2)).
    + apply InA_alt in H2 as [y [H2 H3]].
      apply prepend_all_inv in H3.
      destruct H3 as [L3 [-> H3]].
      assert (InA (equivlistA eqA) L3 (get_all_subsets L2)).
      -- apply InA_alt. eexists L3. split. reflexivity. apply H3.
      -- specialize (proj2 (IHL2 L3) H4). intro.
        intro x. intro. rewrite H2 in*.
        destruct (proj1 (InA_cons eqA x a L3) H6).
        ++ apply (InA_cons_hd L2 H7).
        ++ apply (InA_cons_tl a (H5 x H7)).
Qed.

Lemma NoDupA_get_all_subsets [A: Type] {eqA : relation A} `{Equivalence A eqA}
  (eqA_dec : forall x y, {eqA x y} + {~ eqA x y}):
  forall {L: list A},
  NoDupA eqA L -> 
  NoDupA (equivlistA eqA) (get_all_subsets L).
Proof.
  induction L.
  - intro. simpl. apply NoDupA_singleton.
  - intro. inversion H0 ; subst.
    specialize (IHL H4).
    simpl. apply NoDupA_app.
    + apply (equivlist_equiv H).
    + apply IHL.
    + apply NoDupA_prepend_all.
      -- apply H.
      -- apply IHL.
      -- apply Forall_forall. intros. intro. apply H3.
        assert (InA (equivlistA eqA) x (get_all_subsets L)).
        ++ apply InA_alt. eexists x. split. reflexivity. apply H1.
        ++ apply (proj2 (inclA_iff_get_all_subsets eqA_dec) H5). apply H2.
    + intros. apply H3.
      destruct (proj1 (InA_alt _ _ _) H2) as [y [H5 H6]].
      destruct (prepend_all_inv H6) as [z [-> H7]].
      apply (proj2 (inclA_iff_get_all_subsets eqA_dec) H1 ).
      specialize (proj2 (H5 a)). intro.
      apply H8. apply (InA_cons_hd). reflexivity.
Qed.


  


      
