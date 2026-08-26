From Stdlib Require Import List.

From LJF Require Import SharedLogic Predicates Pndctx LJFn_Rules.

Lemma bctn_boxR_inv : forall {n: nat} {C: pndctx} {L: octx} {D: o},
    bracketable D -> bctn (S n) C L D -> eptn n C L D.
Proof.
    intros. inversion H0 ; subst.
    - apply H3.
    - inversion H. inversion H1. inversion H1.
    - inversion H. inversion H1. inversion H1.
Qed.

Lemma bctn_AndNR_inv : forall {n: nat} {C: pndctx} {L: octx} {B1 B2: o},
    bctn (S n) C L (AndN B1 B2) -> (bctn n C L B1 /\ bctn n C L B2).
Proof.
    intros. inversion H ; subst.
    - inversion H1. inversion H0. inversion H0.
    - split. apply H5. apply H6.
Qed.

Lemma bctn_ImpR_inv : forall {n: nat} {C: pndctx} {L: octx} {B1 B2: o},
    bctn (S n) C L (Imp B1 B2) -> bctn n C (B1 :: L) B2.
Proof.
    intros. inversion H ; subst.
    - inversion H1. inversion H0. inversion H0.
    - apply H4.
Qed.

Lemma eptn_boxL_inv : forall {n: nat} {C: pndctx} {L: octx} {B: o} {K: o},
    permeable B -> eptn (S n) C (B :: L) K -> eptn n (pndctx_insert B C) L K.
Proof.
    intros. inversion H0 ; subst.
    - apply H8.
    - inversion H. inversion H1. inversion H1.
    - inversion H. inversion H1. inversion H1.
    - inversion H. inversion H1. inversion H1.
    - inversion H. inversion H1. inversion H1.
Qed.

Lemma eptn_AndPL_inv : forall {n: nat} {C: pndctx} {L: octx} {B1 B2 : o} {K: o},
    eptn (S n) C ((AndP B1 B2) :: L) K -> eptn n C (B2 :: B1 :: L) K.
Proof.
    intros. inversion H ; subst.
    - inversion H5. inversion H0. inversion H0.
    - apply H7.
Qed.

Lemma eptn_OrL_inv : forall {n: nat} {C: pndctx} {L: octx} {B1 B2 : o}  {K: o},
    eptn (S n) C ((Or B1 B2) :: L) K -> (eptn n C (B1 :: L) K /\ eptn n C (B2 :: L) K).
Proof.
    intros. inversion H ; subst.
    - inversion H5. inversion H0. inversion H0.
    - split. apply H7. apply H8.
Qed.

Lemma eptn_TrueL_inv : forall {n: nat} {C: pndctx} {L: octx} {K: o},
    eptn (S n) C (TT :: L) K -> eptn n C L K.
Proof.
    intros. inversion H ; subst.
    - inversion H5. inversion H0. inversion H0.
    - apply H4.
Qed.

Lemma lfcn_Rl_inv : forall {n: nat} {C: pndctx} {P : o}  {K : o},
    positive P -> lfcn (S n) C P K -> eptn n C (P :: nil) K.
Proof.
    intros. inversion H0 ; subst.
    - apply H4.
    - inversion H ; inversion H2 ; subst ; discriminate H4.
    - inversion H.
    - inversion H.
    - inversion H.
Qed.

Lemma lfcn_Il_NK_eq : forall {n: nat} {C: pndctx} {N K : o},
    atomic N -> negative N -> lfcn (S n) C N K -> N = K.
Proof.
    intros. inversion H. subst. inversion H0. subst. inversion H1 ; subst ; inversion H4 ; reflexivity.
Qed. 

Lemma lfcn_AndNL_inv : forall {n: nat} {C: pndctx} {B1 B2 : o}  {K : o},
    lfcn (S n) C (AndN B1 B2) K -> (lfcn n C B1 K \/ lfcn n C B2 K).
Proof.
    intros. inversion H ; subst.
    - inversion H2.
    - inversion H2.
    - left. apply H6.
    - right. apply H6.
Qed.

Lemma lfcn_ImpL_inv : forall {n: nat} {C: pndctx} {B1 B2 : o}  {K : o},
    lfcn (S n) C (Imp B1 B2) K -> (rfcn n C B1 /\ lfcn n C B2 K).
Proof.
    intros. inversion H ; subst.
    - inversion H2.
    - inversion H2.
    - split. apply H5. apply H7.
Qed.

Lemma rfcn_Rr_inv : forall {n: nat} {C: pndctx} {N: o},
    negative N -> rfcn (S n) C N -> bctn n C nil N.
Proof.
    intros. inversion H0 ; subst.
    - apply H3.
    - inversion H4 ; subst. inversion H3. inversion H. subst. discriminate.
    - inversion H.
    - inversion H.
    - inversion H.
    - inversion H.
Qed.

Lemma rfcn_Ir_inv : forall {n: nat} {C: pndctx} {P: o},
    positive P -> atomic P -> rfcn (S n) C P -> In P (pndctx_list C).
Proof.
    intros. inversion H ; subst ; inversion H0 ; subst ; inversion H1 ; subst.
    - inversion H3.
    - apply H3.
Qed.

Lemma rfcn_AndPR_inv : forall {n: nat} {C: pndctx} {B1 B2: o},
    rfcn (S n) C (AndP B1 B2) -> (rfcn n C B1 /\ rfcn n C B2).
Proof.
    intros. inversion H ; subst.
    - inversion H1.
    - inversion H3.
    - split. apply H4. apply H5.
Qed.

Lemma rfcn_OrR_inv : forall {n: nat} {C: pndctx} {B1 B2: o},
    rfcn (S n) C (Or B1 B2) -> (rfcn n C B1 \/ rfcn n C B2).
Proof.
    intros. inversion H ; subst.
    - inversion H1.
    - inversion H3.
    - left. apply H3.
    - right. apply H3.
Qed.

Lemma rfcn_FF_unprovable : forall {n: nat} {C: pndctx}, ~ rfcn (S n) C FF.
Proof.
    intros. intro. inversion H ; subst.
    - inversion H1.
    - inversion H3.
Qed.

Lemma eptn_nil_inv : forall {n: nat} {C: pndctx} {K : o},
    eptn (S n) C nil K ->
    (exists N, In N (pndctx_list C) /\ negative N /\ lfcn n C N K)
    \/ (positive K /\ rfcn n C K).
Proof.
  intros. inversion H ; subst.
  - left. exists N. repeat split ; assumption.
  - right. split ; assumption.
Qed.

Lemma eptn_nil_disproof_pos : forall {n: nat} {C: pndctx} {K : o},
    positive K -> ~ rfcn n C K ->
    Forall (fun N => ~ lfcn n C N K) (filter negative_b (pndctx_list C)) ->
    ~ eptn (S n) C nil K.
Proof.
    intros. intro. destruct (eptn_nil_inv H2).
    - destruct H3. destruct H3. destruct H4.
        rewrite Forall_forall in H1. 
        apply (H1 x).
        + apply filter_In. split. apply H3. apply negative_b_iff. apply H4.
        + apply H5.
    - destruct H3. contradiction.
Qed.

Lemma eptn_nil_disproof_neg : forall {n: nat} {C: pndctx} {K : o},
    ~ positive K ->
    Forall (fun N => ~ lfcn n C N K) (filter negative_b (pndctx_list C)) ->
    ~ eptn (S n) C nil K.
Proof.
    intros. intro. destruct (eptn_nil_inv H1).
    - destruct H2. destruct H2. destruct H3.
        rewrite Forall_forall in H0.
        apply (H0 x).
        + apply filter_In. split. apply H2. apply negative_b_iff. apply H3.
        + apply H4.
    - destruct H2. contradiction.
Qed.
