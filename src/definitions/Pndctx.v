From Stdlib Require Import List Permutation ProofIrrelevance.
From LJF Require Import SharedLogic Decidability.  

Definition raw_insert (A : o) (C : sctx) : sctx :=
  if permeable_dec A 
  then (if in_dec o_eq_dec A C then C else A :: C) 
  else C.

Lemma raw_insert_nodup :
  forall {A: o} {C: sctx},
  NoDup C ->
  NoDup (raw_insert A C).
Proof.
  intros. unfold raw_insert. destruct permeable_dec.
  - destruct in_dec. apply H. apply NoDup_cons. apply n. apply H.
  - apply H.
Qed.

Lemma raw_insert_permeable_ctx :
  forall {A: o} {C: sctx},
  permeable_ctx C ->
  permeable_ctx (raw_insert A C).
Proof.
  intros. unfold raw_insert. destruct permeable_dec.
  - destruct in_dec. apply H. apply Forall_cons. apply p. apply H. 
  - apply H.
Qed.
  
Definition pndctx : Type := { C : sctx | NoDup C & permeable_ctx C }.
Definition pndctx_list (C : pndctx) : sctx := proj1_sig (sig_of_sig2 C).
Definition pndctx_nodup (C : pndctx) : NoDup (pndctx_list C) := proj2_sig (sig_of_sig2 C).
Definition pndctx_permeable_ctx (C : pndctx) : permeable_ctx (pndctx_list C) := proj3_sig C.

Definition pndctx_empty : pndctx :=
  exist2 _ _ nil (NoDup_nil _) (Forall_nil _).

Definition pndctx_insert (A : o) (C : pndctx) : pndctx :=
  exist2 _ _
    (raw_insert A (pndctx_list C))
    (raw_insert_nodup (pndctx_nodup C))
    (raw_insert_permeable_ctx (pndctx_permeable_ctx C)).

Lemma pndctx_eq : forall (C1 C2 : pndctx),
    pndctx_list C1 = pndctx_list C2 -> C1 = C2.
Proof.
  intros.
  destruct C1.
  destruct C2.
  unfold pndctx_list in H.
  simpl in H. subst.
  f_equal.
  apply proof_irrelevance.
  apply proof_irrelevance.
Qed.

Lemma pndctx_insert_rewrite_in :
  forall {B: o} {C: pndctx}, In B (pndctx_list C) ->
    pndctx_insert B C = C.
Proof.
  intros.
  apply pndctx_eq.
  unfold pndctx_list. simpl.
  unfold raw_insert.
  destruct permeable_dec.
  - destruct in_dec. reflexivity.
    contradiction.
  - unfold pndctx_list. reflexivity.
Qed.

Lemma pndctx_insert_rewrite_fixed_point :
  forall {B: o} {C: pndctx}, 
    (~ permeable B \/ In B (pndctx_list C)) ->
    pndctx_insert B C = C.
Proof.
  intros.
  destruct H.
  - apply pndctx_eq.
    unfold pndctx_list. simpl.
    unfold raw_insert.
    destruct permeable_dec.
    + contradiction.
    + reflexivity.
  - apply pndctx_eq.
    unfold pndctx_list. simpl.
    unfold raw_insert.
    destruct permeable_dec.
    + destruct in_dec. reflexivity. contradiction.
    + unfold pndctx_list. reflexivity.
Qed.

Lemma pndctx_insert_rewrite_valid :
  forall {B: o} {C: pndctx} (Hperm : permeable B) (Hnotin : ~ In B (pndctx_list C)),
    pndctx_insert B C = 
      exist2 _ _ (B :: (pndctx_list C)) 
        (NoDup_cons B Hnotin (pndctx_nodup C))
        (Forall_cons B Hperm (pndctx_permeable_ctx C)).
Proof.
  intros. apply pndctx_eq.
  unfold pndctx_list. simpl.
  unfold raw_insert.
  destruct permeable_dec.
  - destruct in_dec.
    + contradiction.
    + reflexivity.
  - contradiction.
Qed.

Lemma pndctx_insert_perm_cons : 
  forall (B : o) (C C' : pndctx),
  Permutation (pndctx_list C) (pndctx_list C') ->
  Permutation (pndctx_list (pndctx_insert B C)) (pndctx_list (pndctx_insert B C')).
Proof.
  intros. 
  unfold pndctx_list in*. 
  unfold pndctx_insert. simpl.
  unfold raw_insert.
  destruct permeable_dec. 
  - destruct in_dec ; destruct in_dec.
    + apply H.
    + eapply Permutation_in in i. 2: apply H. contradiction.
    + eapply Permutation_in in i. 2: apply Permutation_sym ; apply H. contradiction.
    + apply Permutation_cons. reflexivity. apply H.
  - apply H.
Qed.

Lemma raw_insert_swap : forall (B1 B2 : o) (l : sctx),
  Permutation 
    (raw_insert B1 (raw_insert B2 l)) 
    (raw_insert B2 (raw_insert B1 l)).
Proof.
  intros.
  unfold raw_insert.
  destruct permeable_dec.
  - destruct in_dec.
    + destruct permeable_dec.
      -- destruct in_dec.
        ++ destruct in_dec.
          --- destruct in_dec.
            +++ reflexivity.
            +++ contradiction.
          --- destruct in_dec.
            +++ contradiction.
            +++ contradiction.
        ++ destruct in_dec.
          --- destruct in_dec.
            +++ contradiction.
            +++ apply in_inv in i.
              destruct i.
              ---- subst. reflexivity.
              ---- contradiction.
          --- destruct in_dec.
            +++ reflexivity.
            +++ exfalso.
              apply not_in_cons in n0.
              destruct i.
              ---- destruct n0. contradiction.
              ---- contradiction.
      -- destruct in_dec.
        ++ reflexivity.
        ++ contradiction.
    + destruct permeable_dec.
      -- destruct in_dec.
        ++ destruct in_dec.
          --- destruct in_dec.
            +++ contradiction.
            +++ reflexivity.
          --- destruct in_dec.
            +++ contradiction.
            +++ exfalso.
              apply n0.
              apply in_cons.
              apply i.
        ++ destruct in_dec.
          --- destruct in_dec.
            +++ contradiction.
            +++ exfalso.
              apply not_in_cons in n.
              destruct i.
              ---- destruct n. contradiction.
              ---- contradiction.
          --- destruct in_dec.
            +++ exfalso.
              apply n.
              apply in_cons.
              apply i.
            +++ apply perm_swap.
      -- destruct in_dec.
        ++ contradiction.
        ++ reflexivity.
  - destruct permeable_dec.
    + reflexivity.
    + reflexivity.
Qed.

Lemma pndctx_insert_swap : forall (B1 B2 : o) (C : pndctx),
  Permutation 
    (pndctx_list (pndctx_insert B1 (pndctx_insert B2 C))) 
    (pndctx_list (pndctx_insert B2 (pndctx_insert B1 C))).
Proof.
  intros.
  unfold pndctx_list.
  simpl.
  apply raw_insert_swap.
Qed.

Lemma pndctx_insert_perm_swap : 
  forall (B1 B2 : o) (C C' : pndctx),
  Permutation 
    (pndctx_list (pndctx_insert B2 (pndctx_insert B1 C))) 
    (pndctx_list C') ->
  Permutation 
    (pndctx_list (pndctx_insert B1 (pndctx_insert B2 C))) 
    (pndctx_list C').
Proof.
  intros.
  eapply perm_trans.
  2: apply H.
  apply pndctx_insert_swap.
Qed.

(*
Definition mk_pndctx (C : sctx) : pndctx :=
    exist _ (nodup o_eq_dec C) (NoDup_nodup o_eq_dec C).

Lemma pndctx_insert_mk_pndctx_eq : forall B C,
    pndctx_insert B (mk_pndctx C) = mk_pndctx (B :: C).
Proof.
    intros. apply pndctx_eq. simpl. unfold raw_insert.
    destruct (in_dec o_eq_dec B (nodup o_eq_dec C)).
    - rewrite nodup_In in i.
        destruct (in_dec o_eq_dec B C). reflexivity. contradiction.
    - rewrite nodup_In in n.
        destruct (in_dec o_eq_dec B C). contradiction. reflexivity.
Qed. *)