From Stdlib Require Import List RelationClasses SetoidList PeanoNat.

Lemma equivlistA_dec [A: Type] (eqA : relation A) `{Equivalence A eqA}
    (eqA_dec : forall x y, {eqA x y} + {~ eqA x y}) :
    forall l l', {equivlistA eqA l l'} + {~ equivlistA eqA l l'}.
Proof.
  intros l l'.
  destruct (Forall_dec (fun a => InA eqA a l') (fun a => InA_dec eqA_dec a l') l) as [F1 | F1];
  destruct (Forall_dec (fun a => InA eqA a l)  (fun a => InA_dec eqA_dec a l ) l') as [F2 | F2].
  - left. intro. split ; intro.
    + apply InA_alt in H0. destruct H0 as [y [Hxy Hy]].
      eapply Forall_forall in F1. symmetry in Hxy. apply (InA_eqA H Hxy F1). apply Hy.
    + apply InA_alt in H0. destruct H0 as [y [Hxy Hy]].
      eapply Forall_forall in F2. symmetry in Hxy. apply (InA_eqA H Hxy F2). apply Hy.
  - right. intro Heq. apply F2. apply Forall_forall. intros.
    destruct (Heq x).  apply H2. apply In_InA. apply H. apply H0.
  - right. intro Heq. apply F1. apply Forall_forall. intros.
    destruct (Heq x).  apply H1. apply In_InA. apply H. apply H0.
  - right. intro Heq. apply F2. apply Forall_forall. intros.
    destruct (Heq x).  apply H2. apply In_InA. apply H. apply H0.
Defined.

Lemma InA_equivlistA [A: Type] {eqA : relation A} `{Equivalence A eqA} :
  forall {B : A} {L1 L2 : list A},
  InA eqA B L1    ->
  equivlistA eqA L1 L2 ->
  InA eqA B L2.
Proof. intros. apply (proj1 (H1 B) H0). Qed.

Lemma inclA_cons_1 [A: Type] {eqA : relation A} `{Equivalence A eqA} :
  forall (B : A) {L1 L2 : list A},
  inclA eqA (B :: L1) L2 ->
  inclA eqA L1 L2.
Proof. intros. intro x. intro. apply (H0 x (InA_cons_tl B H1)). Qed.

Lemma inclA_cons_2 [A: Type] {eqA : relation A} `{Equivalence A eqA} :
  forall (B : A) {L1 L2 : list A},
  inclA eqA L1 L2 ->
  inclA eqA L1 (B :: L2).
Proof. intros. intro x. intro. apply (InA_cons_tl B (H0 x H1)). Qed.


Lemma inclA_removeA [A: Type] {eqA : relation A} `{Equivalence A eqA}
  (eqA_dec : forall x y, {eqA x y} + {~ eqA x y}) :
  forall {B : A} {L1 L2 : list A}, inclA eqA (removeA eqA_dec B L1) L2 -> inclA eqA L1 (B :: L2).
Proof.
  intros B L1. induction L1.
  - intros. apply incl_nil.
  - intros. simpl in H0. destruct (eqA_dec B a).
    + intro x. intro. destruct (eqA_dec x a).
      -- rewrite e0. apply InA_cons_hd. symmetry. apply e.
      -- destruct (proj1 (InA_cons eqA x a L1) H1).
        ++ contradiction.
        ++ apply (IHL1 L2 H0 x H2).
    + intro x. intro. destruct (eqA_dec x a).
      -- specialize (H0 x (InA_cons_hd (removeA (eqA:=eqA) eqA_dec B L1) e)).
        apply (InA_cons_tl B H0).
      -- destruct (proj1 (InA_cons eqA x a L1) H1).
        ++ contradiction.
        ++ specialize (IHL1 L2 (inclA_cons_1 a H0)).
          apply (IHL1 x H2). 
Qed.

Lemma removeA_swap [A: Type] {eqA : relation A} `{Equivalence A eqA}
  (eqA_dec : forall x y, {eqA x y} + {~ eqA x y}) :
  forall (B1 B2 : A) (L : list A),
  equivlistA eqA 
    (removeA eqA_dec B1 (removeA eqA_dec B2 L))
    (removeA eqA_dec B2 (removeA eqA_dec B1 L)).
Proof.
  intros. induction L.
  - simpl. reflexivity.
  - simpl. destruct (eqA_dec B2 a).
    + destruct (eqA_dec B1 a).
      -- apply IHL.
      -- simpl. destruct (eqA_dec B2 a).
        ++ apply IHL.
        ++ contradiction.
    + destruct (eqA_dec B1 a).
      -- simpl. destruct (eqA_dec B1 a).
        ++ apply IHL.
        ++ contradiction.
      -- simpl. destruct (eqA_dec B1 a).
        ++ contradiction.
        ++ destruct (eqA_dec B2 a).
          --- contradiction.
          --- intro x. split.
            +++ intro. destruct (proj1 (InA_cons eqA _ _ _) H0).
              ---- apply (InA_cons_hd _ H1).
              ---- apply (InA_cons_tl a (proj1 (IHL x) H1)).
            +++ intro. destruct (proj1 (InA_cons eqA _ _ _) H0).
              ---- apply (InA_cons_hd _ H1).
              ---- apply (InA_cons_tl a (proj2 (IHL x) H1)).
Qed. 

Lemma eqA_not_symmetry [A: Type] {eqA : relation A} `{Equivalence A eqA} :
  forall {A1 A2 : A}, ~ eqA A1 A2 -> ~ eqA A2 A1.
Proof.
intros. intro. symmetry in H1. contradiction. Qed.

Lemma inclA_removeA_iff [A: Type] {eqA : relation A} `{Equivalence A eqA} 
  (eqA_dec : forall x y, {eqA x y} + {~ eqA x y}) :
  forall {B : A} {L1 L2: list A},
  inclA eqA L1 (B :: L2) <->
  (InA eqA B L1 /\ inclA eqA (removeA eqA_dec B L1) L2) \/
  (~InA eqA B L1 /\ inclA eqA L1 L2).
Proof.
  intros B L1 L2. revert L1. induction L2 ; intro ; split ; intro.
  - destruct (InA_dec eqA_dec B L1).
    + left. split. apply i. intro x. intro.
      destruct (proj1 (removeA_InA H eqA_dec L1 B x) H1).
      specialize (H0 x H2).
      destruct (proj1 (InA_cons eqA x B nil) H0).
      -- symmetry in H4. contradiction.
      -- apply H4.
    + right. split. apply n. intro x. intro.
      specialize (H0 x H1).
      destruct (proj1 (InA_cons eqA x B nil) H0).
      -- rewrite H2 in H1. contradiction.
      -- apply H2.
  - destruct H0 ; destruct H0.
    + apply (inclA_removeA eqA_dec H1).
    + intro x. intro. 
      exfalso. apply (proj1 (InA_nil eqA x ) (H1 x H2)).
  - destruct (InA_dec eqA_dec B L1).
    + left. split. apply i.
      destruct (InA_dec eqA_dec a L1).
      -- assert (inclA eqA (removeA eqA_dec a L1) (B :: L2)).
        ++ intro x. intro.
          destruct (proj1 (removeA_InA H eqA_dec L1 a x) H1).
          specialize (H0 x H2).
          destruct (proj1 (InA_cons eqA x B (a :: L2)) H0).
          --- apply (InA_cons_hd L2 H4).
          --- destruct (proj1 (InA_cons eqA x a L2) H4).
            +++ symmetry in H5. contradiction.
            +++ apply (InA_cons_tl B H5).
        ++ destruct (proj1 (IHL2 _) H1).
          --- destruct H2. intro x. intro.
            destruct (eqA_dec x a).
            +++ apply (InA_cons_hd L2 e).
            +++ destruct (proj1 (removeA_InA H eqA_dec L1 B x) H4).
              assert (~ eqA a x). intro. symmetry in H7. contradiction.
              specialize (proj2 (removeA_InA H eqA_dec L1 a x) (conj H5 H7)) ; intro.
              specialize (proj2 (removeA_InA H eqA_dec _ B x) (conj H8 H6)) ; intro.
              apply (InA_cons_tl a (H3 x H9)).
          --- destruct H2. intro x. intro.
            destruct (eqA_dec x a).
            +++ apply (InA_cons_hd L2 e).
            +++ destruct (proj1 (removeA_InA H eqA_dec L1 B x) H4).
              assert (~ eqA a x). intro. symmetry in H7. contradiction.
              specialize (proj2 (removeA_InA H eqA_dec L1 a x) (conj H5 H7)) ; intro.
              specialize (H1 x H8).
              destruct (proj1 (InA_cons eqA x B L2) H1).
              ---- symmetry in H9. contradiction.
              ---- apply (InA_cons_tl a H9).
      -- assert (inclA eqA L1 (B :: L2)).
        ++ intro x. intro. specialize (H0 x H1).
          destruct (proj1 (InA_cons eqA x B (a :: L2)) H0).
          --- apply (InA_cons_hd L2 H2).
          --- destruct (proj1 (InA_cons eqA x a L2) H2).
            +++ rewrite H3 in H1. contradiction.
            +++ apply (InA_cons_tl B H3).
        ++ destruct (proj1 (IHL2 _) H1).
          --- destruct H2. apply (inclA_cons_2 a H3).
          --- destruct H2. contradiction.
    + right. split. apply n.
      intro x. intro. specialize (H0 x H1).
      destruct (proj1 (InA_cons eqA x B (a :: L2)) H0).
      -- rewrite H2 in H1. contradiction.
      -- apply H2.
  - destruct H0 ; destruct H0.
    + apply (inclA_removeA eqA_dec H1).
    + apply (inclA_cons_2 B H1).
Qed.

Lemma inclA_nil [A: Type] {eqA : relation A} `{Equivalence A eqA} :
  forall {L : list A}, inclA eqA L nil -> L = nil.
Proof.
  intros. destruct L.
  - reflexivity.
  - assert (eqA a a). reflexivity.
    exfalso. apply (proj1 (InA_nil eqA a) (H0 a (InA_cons_hd L H1))).
Qed.

Lemma NoDupA_removeA [A: Type] {eqA : relation A} `{Equivalence A eqA} 
  (eqA_dec : forall x y, {eqA x y} + {~ eqA x y}) :
  forall (B: A) {L : list A},
  NoDupA eqA L ->
  NoDupA eqA (removeA eqA_dec B L).
Proof.
  induction L ; intros.
  - simpl. apply NoDupA_nil.
  - simpl. destruct (eqA_dec B a).
    + inversion H0. subst. apply (IHL H4).
    + inversion H0. subst. apply NoDupA_cons.
      -- intro. destruct (proj1 (removeA_InA H eqA_dec L B a) H1). contradiction.
      -- apply (IHL H4).
Qed.


Lemma NoDupA_removeA_length [A: Type] {eqA : relation A} `{Equivalence A eqA} 
  (eqA_dec : forall x y, {eqA x y} + {~ eqA x y}) :
  forall (B: A) {L : list A},
  NoDupA eqA L -> 
    (InA eqA B L /\ length L = S (length (removeA eqA_dec B L))) \/
    (~InA eqA B L /\ length L = length (removeA eqA_dec B L)).
Proof.
  induction L.
  - intros. simpl. right. split. intro. inversion H1. reflexivity.
  - intros. inversion H0 ; subst. destruct (IHL H4).
    + destruct H1. left. split. apply (InA_cons_tl a H1).
      simpl. destruct (eqA_dec B a).
      -- rewrite e in H1. contradiction. 
      -- simpl. apply (f_equal S H2).
    + destruct H1. simpl. destruct (eqA_dec B a).
      -- left. split.
        ++ apply (InA_cons_hd L e).
        ++ apply (f_equal S H2).
      -- right. split.
        ++ intro. inversion H5 ; subst. contradiction. contradiction.
        ++ simpl. apply (f_equal S H2).
Qed. 

Lemma NoDupA_inclA_length [A: Type] {eqA : relation A} `{Equivalence A eqA} 
  (eqA_dec : forall x y, {eqA x y} + {~ eqA x y}) :
  forall {L1 L2 : list A},
  NoDupA eqA L1 -> 
  inclA eqA L1 L2 ->
  length L1 <= length L2.
Proof.
  intros L1 L2. revert L1. induction L2.
  - intros. apply inclA_nil in H1. subst. simpl. reflexivity. apply H.
  - intros. destruct (proj1 (inclA_removeA_iff eqA_dec) H1) ; destruct H2.
    + specialize (NoDupA_removeA eqA_dec a H0) ; intro.
      specialize (IHL2 _ H4 H3).
      destruct (NoDupA_removeA_length eqA_dec a H0) ; destruct H5.
      -- simpl. transitivity (S (length (removeA (eqA:=eqA) eqA_dec a L1))).
        apply (Nat.eq_le_incl _ _ H6). apply (le_n_S _ _ IHL2).
      -- simpl. contradiction.
    + specialize (IHL2 L1 H0 H3). simpl. apply (le_S _ _ IHL2).
Qed.
