From Stdlib Require Import List.

From LJF Require Import SharedLogic Predicates Pndctx LJFPS_Rules.

Lemma bct_boxR_inv : forall {C: pndctx} {L: octx} {D: o},
    bracketable D -> bct C L D -> ept C L D.
Proof.
    intros. inversion H0 ; subst.
    - apply H2.
    - inversion H. inversion H3. inversion H3.
    - inversion H. inversion H2. inversion H2.
Qed.

Lemma bct_AndNR_inv : forall {C: pndctx} {L: octx} {B1 B2: o},
    bct C L (AndN B1 B2) -> (bct C L B1 /\ bct C L B2).
Proof.
    intros. inversion H ; subst.
    - inversion H0. inversion H2. inversion H2.
    - split. apply H4. apply H5.
Qed.

Lemma bct_ImpR_inv : forall {C: pndctx} {L: octx} {B1 B2: o},
    bct C L (Imp B1 B2) -> bct C (B1 :: L) B2.
Proof.
    intros. inversion H ; subst.
    - inversion H0. inversion H2. inversion H2.
    - apply H3.
Qed.

Lemma ept_boxL_inv : forall {C: pndctx} {L: octx} {B: o} {K: o},
    permeable B -> ept C (B :: L) K -> ept (pndctx_insert B C) L K.
Proof.
    intros. inversion H0 ; subst.
    - apply H7.
    - inversion H. inversion H1. inversion H1.
    - inversion H. inversion H1. inversion H1.
    - inversion H. inversion H1. inversion H1.
    - inversion H. inversion H1. inversion H1.
Qed.

Lemma ept_AndPL_inv : forall {C: pndctx} {L: octx} {B1 B2 : o} {K: o},
    ept C ((AndP B1 B2) :: L) K -> ept C (B2 :: B1 :: L) K.
Proof.
    intros. inversion H ; subst.
    - inversion H4. inversion H0. inversion H0.
    - apply H6 .
Qed.

Lemma ept_OrL_inv : forall {C: pndctx} {L: octx} {B1 B2 : o}  {K: o},
    ept C ((Or B1 B2) :: L) K -> (ept C (B1 :: L) K /\ ept C (B2 :: L) K).
Proof.
    intros. inversion H ; subst.
    - inversion H4. inversion H0. inversion H0.
    - split. apply H6. apply H7.
Qed.

Lemma ept_TrueL_inv : forall {C: pndctx} {L: octx} {K: o},
    ept C (TT :: L) K -> ept C L K.
Proof.
    intros. inversion H ; subst.
    - inversion H4. inversion H0. inversion H0.
    - apply H3.
Qed.

Lemma lfc_Rl_inv : forall {C : pndctx} {P : o}  {K : o},
    positive P -> lfc C P K -> ept C (P :: nil) K.
Proof.
    intros. inversion H0 ; subst.
    - apply H3.
    - inversion H2. subst. inversion H1. inversion H. subst. discriminate H6.
    - inversion H.
    - inversion H.
    - inversion H.
Qed.

Lemma lfc_Il_NK_eq : forall {C: pndctx} {N K : o},
    atomic N -> negative N -> lfc C N K -> N = K.
Proof.
    intros. inversion H. subst. inversion H0. subst. inversion H1 ; subst.
    - inversion H3.
    - reflexivity.
Qed. 

Lemma lfc_AndNL_inv : forall {C: pndctx} {B1 B2 : o}  {K : o},
    lfc C (AndN B1 B2) K -> (lfc C B1 K \/ lfc C B2 K).
Proof.
    intros. inversion H ; subst.
    - inversion H1.
    - inversion H1.
    - left. apply H5.
    - right. apply H5.
Qed.

Lemma lfc_ImpL_inv : forall {C: pndctx} {B1 B2 : o}  {K : o},
    lfc C (Imp B1 B2) K -> (rfc C B1 /\ lfc C B2 K).
Proof.
    intros. inversion H ; subst.
    - inversion H1.
    - inversion H1.
    - split. apply H4. apply H6.
Qed.

Lemma rfc_Rr_inv : forall {C: pndctx} {N: o},
    negative N -> rfc C N -> bct C nil N.
Proof.
    intros. inversion H0 ; subst.
    - apply H2.
    - inversion H3 ; subst. inversion H2. inversion H. subst. discriminate.
    - inversion H.
    - inversion H.
    - inversion H.
    - inversion H.
Qed.

Lemma rfc_Ir_inv : forall {C: pndctx} {P: o},
    positive P -> atomic P -> rfc C P -> In P (pndctx_list C).
Proof.
    intros. inversion H0. subst. inversion H. subst. inversion H1 ; subst.
    - inversion H2.
    - apply H2.
Qed.

Lemma rfc_AndPR_inv : forall {C: pndctx} {B1 B2: o},
    rfc C (AndP B1 B2) -> (rfc C B1 /\ rfc C B2).
Proof.
    intros. inversion H ; subst.
    - inversion H0.
    - inversion H2.
    - split. apply H3. apply H4.
Qed.

Lemma rfc_OrR_inv : forall {C: pndctx} {B1 B2: o},
    rfc C (Or B1 B2) -> (rfc C B1 \/ rfc C B2).
Proof.
    intros. inversion H ; subst.
    - inversion H0.
    - inversion H2.
    - left. apply H2.
    - right. apply H2.
Qed.

Lemma rfc_FF_unprovable : forall {C: pndctx}, ~ rfc C FF.
Proof.
    intros. intro. inversion H ; subst.
    - inversion H0.
    - inversion H2.
Qed.

Lemma ept_nil_inv : forall {C : pndctx} {K : o},
    ept C nil K ->
    (exists N, In N (pndctx_list C) /\ negative N /\ lfc C N K)
    \/ (positive K /\ rfc C K).
Proof.
  intros. inversion H ; subst.
  - left. exists N. split. assumption. split ; assumption.
  - right. split ; assumption.
Qed.

Lemma ept_nil_disproof_pos : forall {C : pndctx} {K : o},
    positive K -> ~ rfc C K ->
    Forall (fun N => ~ lfc C N K) (filter negative_b (pndctx_list C)) ->
    ~ ept C nil K.
Proof.
    intros. intro. destruct (ept_nil_inv H2).
    - destruct H3. destruct H3. destruct H4.
        rewrite Forall_forall in H1. 
        apply (H1 x).
        + apply filter_In. split. apply H3. apply negative_b_iff. apply H4.
        + apply H5.
    - destruct H3. contradiction.
Qed.

Lemma ept_nil_disproof_neg : forall {C : pndctx} {K : o},
    ~ positive K ->
    Forall (fun N => ~ lfc C N K) (filter negative_b (pndctx_list C)) ->
    ~ ept C nil K.
Proof.
    intros. intro. destruct (ept_nil_inv H1).
    - destruct H2. destruct H2. destruct H3.
        rewrite Forall_forall in H0.
        apply (H0 x).
        + apply filter_In. split. apply H2. apply negative_b_iff. apply H3.
        + apply H4.
    - destruct H2. contradiction.
Qed.
