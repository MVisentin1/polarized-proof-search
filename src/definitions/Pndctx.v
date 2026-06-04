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

(*Lemma pndctx_insert_perm_cons : 
  forall (B : o) (C C' : pndctx),
  Permutation C C' ->
  Permutation (pndctx_insert B C) (pndctx_insert B C').
Proof.
  intros. simpl. unfold raw_insert. unfold pndctx_list in *.
  destruct (in_dec o_eq_dec B (proj1_sig C)), (in_dec o_eq_dec B (proj1_sig C')).
  - apply H.
  - exfalso. apply n. eapply Permutation_in. apply H. apply i.
  - exfalso. apply n. eapply Permutation_in. apply Permutation_sym. apply H. apply i.
  - apply Permutation_cons. reflexivity. apply H.
Qed.

Lemma pndctx_insert_swap : forall (B1 B2 : o) (C : pndctx),
  Permutation (pndctx_insert B1 (pndctx_insert B2 C)) (pndctx_insert B2 (pndctx_insert B1 C)).
Proof.
  intros. simpl. unfold raw_insert.
  destruct 
  (in_dec o_eq_dec B1),
  (in_dec o_eq_dec B2 (proj1_sig C)).
  - destruct
    (in_dec o_eq_dec B2),
    (in_dec o_eq_dec B1 (proj1_sig C)).
    + apply Permutation_refl.
    + contradiction.
    + contradiction.
    + contradiction.
  - destruct
    (in_dec o_eq_dec B2),
    (in_dec o_eq_dec B1 (proj1_sig C)).
    + contradiction.
    + apply in_inv in i. destruct i.
      -- subst. apply Permutation_cons. reflexivity. apply Permutation_refl.
      -- contradiction.
    + apply Permutation_cons. reflexivity. apply Permutation_refl.
    + apply in_inv in i. destruct i.
      -- subst. exfalso. apply n0. apply in_eq.
      -- contradiction.
  - destruct
    (in_dec o_eq_dec B2),
    (in_dec o_eq_dec B1 (proj1_sig C)).
    + contradiction.
    + apply Permutation_cons. reflexivity. apply Permutation_refl.
    + contradiction.
    + exfalso. apply n0. apply in_cons. apply i.
  - destruct
    (in_dec o_eq_dec B2),
    (in_dec o_eq_dec B1 (proj1_sig C)).
    + contradiction.
    + apply in_inv in i. destruct i.
      -- subst. exfalso. apply n. apply in_eq.
      -- contradiction.
    + exfalso. apply n. apply in_cons. apply i.
    + apply perm_swap.
Qed.

Lemma pndctx_insert_perm_swap : 
  forall (B1 B2 : o) (C C' : pndctx),
  Permutation (pndctx_insert B2 (pndctx_insert B1 C)) C' ->
  Permutation (pndctx_insert B1 (pndctx_insert B2 C)) C'.
Proof.
  intros.
  transitivity (pndctx_insert B2 (pndctx_insert B1 C)).
  - apply pndctx_insert_swap.
  - apply H.
Qed.

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
Qed.*)