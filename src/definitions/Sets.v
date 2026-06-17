From Stdlib Require Import List.

Definition set_eq [A: Type] (C1 C2 : list A) : Prop :=
   incl C1 C2 /\ incl C2 C1.

Lemma set_eq_refl [A: Type] (C1: list A) : set_eq C1 C1.
Proof.
   unfold set_eq. split. apply incl_refl. apply incl_refl.
Qed.

Lemma set_eq_dec [A: Type] :
      (forall (A1 A2 : A), {A1 = A2} + {~ A1 = A2}) ->
      forall (C1 C2: list A), {set_eq C1 C2} + {~ set_eq C1 C2}.
Proof.
   intros. 
   unfold set_eq.
   unfold incl.
   destruct (Forall_dec (fun a => In a C1) (fun A => in_dec X _ C1) C2) ;
   destruct (Forall_dec (fun a => In a C2) (fun A => in_dec X _ C2) C1).
   - left. split ; apply Forall_forall ; assumption.
   - right. intro. destruct H. apply Forall_forall in H. contradiction.
   - right. intro. destruct H. apply Forall_forall in H0. contradiction.
   - right. intro. destruct H. apply Forall_forall in H. contradiction.
Defined.

Fixpoint prepend_all [A: Type] (B : A) (L : list (list A)) : list (list A) := 
    match L with
    | nil       => nil
    | L1 :: L'  => (B :: L1) :: (prepend_all B L')
    end
.

Lemma prepend_all_inv [A: Type] (a : A) (L : list (list A)) :
   forall {C: list A}, In C (prepend_all a L) -> exists C1, C = a :: C1 /\ In C1 L.
Proof.
   induction L.
   - intros. inversion H.
   - intros. simpl in H. destruct H.
      ++ eexists a0. split. symmetry. apply H. apply in_eq.
      ++ specialize (IHL C H). destruct IHL. destruct H0.
         subst. eexists x. split. reflexivity. apply in_cons. apply H1.
Qed.

Lemma prepend_all_In [A : Type] (a : A) (C : list A) (L : list (list A)) :
    In C L -> In (a :: C) (prepend_all a L).
Proof.
  induction L; intros H.
  - inversion H.
  - simpl. destruct H.
    + subst. left. reflexivity.
    + right. apply IHL. assumption.
Qed.

Fixpoint generate_subsets [A: Type] (L : list A) : list (list A) := 
    match L with
    | nil       => nil :: nil
    | B :: L'   => let L0 := generate_subsets L' in L0 ++ (prepend_all B L0)
    end
.

Lemma generate_subsets_nil {A: Type} :
    @generate_subsets A nil = nil :: nil.
Proof. reflexivity. Qed.   

Lemma generate_subsets_cons {A: Type} (a : A) (L : list A) :
      generate_subsets (a :: L) = generate_subsets L ++ prepend_all a (generate_subsets L).
Proof. reflexivity. Qed.

Lemma incl_remove [A: Type] (X : forall (A1 A2 : A), {A1 = A2} + {~ A1 = A2}) :
   forall {C C1 : list A} {a: A}, incl (remove X a C) C1 -> incl C (a :: C1).
Proof.
   induction C ; intros.
   - apply incl_nil_l.
   - destruct (X a a0).
      + subst. rewrite remove_cons in H. apply IHC in H. apply incl_cons.
         apply in_eq. apply H.
      + simpl in H. destruct (X a0 a).
         -- subst. destruct n. reflexivity.
         -- apply incl_cons_inv in H. destruct H.
            apply incl_cons. 
            ++ apply in_cons. apply H.
            ++ apply IHC. apply H0.
Qed.


Lemma generate_subsets_complete [A: Type] :
   (forall (A1 A2 : A), {A1 = A2} + {~ A1 = A2}) ->
   forall {C1 C0 : list A}, incl C0 C1 <-> Exists (fun C => set_eq C0 C) (generate_subsets C1).
Proof.
   intros X C1. induction C1 ; intros ; split ; intros.
   - apply incl_l_nil in H. subst. apply Exists_exists. eexists nil. split.
      rewrite generate_subsets_nil. apply in_eq. apply set_eq_refl.
   - rewrite generate_subsets_nil in H. inversion H ; subst.
      + inversion H1. apply incl_l_nil in H0. subst. apply incl_nil_l.
      + inversion H1.
   - rewrite generate_subsets_cons. destruct (in_dec X a C0).
      + apply Exists_app. right.
         assert (incl (remove X a C0) C1).
         -- unfold incl. intros. apply in_remove in H0.
             destruct H0. destruct (H a0).
             ++ apply H0.
             ++ subst. destruct H1. reflexivity.
             ++ unfold incl in H. 
               specialize (H a0). specialize (H H0). inversion H.
               --- subst. destruct H1. reflexivity.
               --- apply H3.
         -- apply IHC1 in H0. 
            apply Exists_exists in H0. 
            destruct H0.
            destruct H0.
            apply Exists_exists. eexists (a :: x). split.
            ++ apply prepend_all_In. apply H0.
            ++ unfold set_eq in*. destruct H1. split.
               --- eapply incl_remove. apply H1.
               --- apply incl_cons.
                  +++ apply i.
                  +++ eapply incl_tran. apply H2.
                     unfold incl. intros. apply in_remove in H3. destruct H3.
                     apply H3.
      + apply Exists_app. left.
         assert (incl C0 C1).
         -- unfold incl in H. unfold incl.
            intros. specialize (H a0). specialize (H H0).
            apply in_inv in H. destruct H.
            ++ subst. contradiction.
            ++ apply H.
         -- apply IHC1 in H0.
            apply H0.
   - rewrite generate_subsets_cons in H. 
      apply Exists_app in H.
      destruct H.
      ++ specialize (IHC1 C0). destruct IHC1. specialize (H1 H).
         apply incl_tl. apply H1.
      ++ apply Exists_exists in H. destruct H. destruct H.
         apply prepend_all_inv in H. destruct H. destruct H.
         subst.
         apply incl_tran with (m:= a :: x0).
         --- unfold set_eq in H0. destruct H0. apply H.
         --- apply incl_cons. apply in_eq. apply incl_tl. apply IHC1.
            apply Exists_exists. eexists x0. split. apply H1. apply set_eq_refl.
Qed.


         
