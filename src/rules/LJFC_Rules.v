From Stdlib Require Import List Permutation ProofIrrelevance.
From LJF Require Import SharedLogic.

Definition raw_insert (A : o) (C : sctx) : sctx :=
    if in_dec o_eq_dec A C then C else A :: C.

Lemma raw_insert_nodup :
    forall {A: o} {C: sctx},
    NoDup C ->
    NoDup (raw_insert A C).
Proof.
    intros. unfold raw_insert. destruct (in_dec o_eq_dec A C).
    - apply H.
    - apply NoDup_cons. apply n. apply H.
Qed.

Definition ndctx : Type := { C : sctx | NoDup C }.
Definition ndctx_list (C : ndctx) : sctx := proj1_sig C.
Definition ndctx_nodup (C : ndctx) : NoDup (ndctx_list C) := proj2_sig C.

Arguments ndctx_list _ /.

Coercion ndctx_list : ndctx >-> sctx.

Definition ndctx_empty : ndctx := exist _ nil (NoDup_nil _).

Definition ndctx_insert (A : o) (C : ndctx) : ndctx :=
    exist _ (raw_insert A C) (raw_insert_nodup (ndctx_nodup C)).

Lemma ndctx_eq : forall (C1 C2 : ndctx),
    ndctx_list C1 = ndctx_list C2 -> C1 = C2.
Proof.
    intros. simpl in H. 
    destruct C1.
    destruct C2.
    simpl in H.
    subst.
    f_equal. 
    apply proof_irrelevance.
Qed.


Inductive bctC : ndctx -> octx -> o -> Prop :=
| bctC_boxR :
  forall {C: ndctx} {L: octx} {D: o},
    bracketable D ->
    eptC C L D ->
    bctC C L D
| bctC_AndNR :
  forall {C: ndctx} {L: octx} {B1 B2: o},
    bctC C L B1 ->
    bctC C L B2 ->
    bctC C L (AndN B1 B2)
| bctC_ImpR :
  forall {C: ndctx} {L: octx} {B1 B2: o},
    bctC C (B1 :: L) B2 ->
    bctC C L (Imp B1 B2)
with eptC : ndctx -> octx -> o -> Prop :=
| eptC_Lf :
  forall {C: ndctx} (N : o) {K : o},
    In N (ndctx_list C) ->
    bracketable K ->
    negative N ->
    lfcC C N K ->
    eptC C nil K
| eptC_Rf :
  forall {C: ndctx} {P: o},
    positive P ->
    rfcC C P ->
    eptC C nil P
| eptC_boxL :
  forall {C: ndctx} {L: octx} (B: o) {K: o},
    bracketable K ->
    permeable B ->
    eptC (ndctx_insert B C) L K ->
    eptC C (B :: L) K
| eptC_AndPL :
  forall {C: ndctx} {L: octx} (B1 B2 : o) {K: o},
    bracketable K ->
    eptC C (B2 :: B1 :: L) K ->
    eptC C ((AndP B1 B2) :: L) K
| eptC_OrL :
  forall {C: ndctx} {L: octx} (B1 B2 : o)  {K: o},
    bracketable K ->
    eptC C (B1 :: L) K ->
    eptC C (B2 :: L) K ->
    eptC C ((Or B1 B2) :: L) K
| eptC_TrueL :
  forall {C: ndctx} {L: octx} {K: o},
    bracketable K ->
    eptC C L K ->
    eptC C (TT :: L) K
| eptC_FalseL :
  forall {C: ndctx} {L: octx} {K: o},
    bracketable K ->
    eptC C (FF :: L) K
with lfcC : ndctx -> o -> o -> Prop :=
| lfcC_Rl :
  forall {C : ndctx} {P : o}  {K : o},
    bracketable K ->
    positive P ->
    eptC C (P :: nil) K ->
    lfcC C P K
| lfcC_Il :
  forall {C: ndctx} {N : o},
    negative N ->
    atomic N ->
    lfcC C N N
| lfcC_AndNL_1 :
  forall {C: ndctx} {B1 B2 : o}  {K : o},
    bracketable K ->
    lfcC C B1 K ->
    lfcC C (AndN B1 B2) K
| lfcC_AndNL_2 :
  forall {C: ndctx} {B1 B2 : o}  {K : o},
    bracketable K ->
    lfcC C B2 K ->
    lfcC C (AndN B1 B2) K
| lfcC_ImpL :
  forall {C: ndctx} {B1 B2 : o}  {K : o},
    bracketable K ->
    rfcC C B1 ->
    lfcC C B2 K ->
    lfcC C (Imp B1 B2) K
with rfcC : ndctx -> o -> Prop :=
| rfcC_Rr :
  forall {C: ndctx} {N: o},
    negative N ->
    bctC C nil N ->
    rfcC C N
| rfcC_Ir :
  forall {C: ndctx} {P: o},
    In P (ndctx_list C) ->
    positive P ->
    atomic P ->
    rfcC C P
| rfcC_AndPR :
  forall {C: ndctx} {B1 B2: o},
    rfcC C B1 ->
    rfcC C B2 ->
    rfcC C (AndP B1 B2)
| rfcC_OrR_1 :
  forall {C: ndctx} {B1 B2: o},
    rfcC C B1 ->
    rfcC C (Or B1 B2)
| rfcC_OrR_2 :
  forall {C: ndctx} {B1 B2: o},
    rfcC C B2 ->
    rfcC C (Or B1 B2)
| rfcC_TrueR :
  forall {C: ndctx},
    rfcC C TT
.

Lemma ndctx_insert_perm_cons : 
  forall (B : o) (C C' : ndctx),
  Permutation C C' ->
  Permutation (ndctx_insert B C) (ndctx_insert B C').
Proof.
  intros. simpl. unfold raw_insert. unfold ndctx_list in *.
  destruct (in_dec o_eq_dec B (proj1_sig C)), (in_dec o_eq_dec B (proj1_sig C')).
  - apply H.
  - exfalso. apply n. eapply Permutation_in. apply H. apply i.
  - exfalso. apply n. eapply Permutation_in. apply Permutation_sym. apply H. apply i.
  - apply Permutation_cons. reflexivity. apply H.
Qed.

Lemma ndctx_insert_swap : forall (B1 B2 : o) (C : ndctx),
  Permutation (ndctx_insert B1 (ndctx_insert B2 C)) (ndctx_insert B2 (ndctx_insert B1 C)).
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

Lemma ndctx_insert_perm_swap : 
  forall (B1 B2 : o) (C C' : ndctx),
  Permutation (ndctx_insert B2 (ndctx_insert B1 C)) C' ->
  Permutation (ndctx_insert B1 (ndctx_insert B2 C)) C'.
Proof.
  intros.
  transitivity (ndctx_insert B2 (ndctx_insert B1 C)).
  - apply ndctx_insert_swap.
  - apply H.
Qed.

Definition mk_ndctx (C : sctx) : ndctx :=
    exist _ (nodup o_eq_dec C) (NoDup_nodup o_eq_dec C).

Lemma ndctx_insert_mk_ndctx_eq : forall B C,
    ndctx_insert B (mk_ndctx C) = mk_ndctx (B :: C).
Proof.
    intros. apply ndctx_eq. simpl. unfold raw_insert.
    destruct (in_dec o_eq_dec B (nodup o_eq_dec C)).
    - rewrite nodup_In in i.
        destruct (in_dec o_eq_dec B C). reflexivity. contradiction.
    - rewrite nodup_In in n.
        destruct (in_dec o_eq_dec B C). contradiction. reflexivity.
Qed.