From Stdlib Require Import List.
From LJF Require Import SharedLogic Predicates 
    Pndctx Decidability Subformula LJFPS_Rules Sequents.

Lemma subp_bct_boxR : 
    forall {C: pndctx} {L: octx} {D: o} {S: sequent},
    subsequent (Sbct C L D) S ->
    subsequent (Sept C L D) S.
Proof.
    intros. unfold subsequent in*. apply H. 
Qed.

Lemma subp_bct_AndNR : 
    forall {C: pndctx} {L: octx} {B1 B2: o} {S: sequent},
    subsequent (Sbct C L (AndN B1 B2)) S ->
    subsequent (Sbct C L B1) S /\ subsequent (Sbct C L B2) S. 
Proof.
    intros. unfold subsequent in H. destruct H. destruct H0.
    unfold subsequent. split. all : split.
    apply H.
    split. apply H0.
    apply sequent_subformulas_transitivity with (B:= AndN B1 B2).
    apply Sub_AndNL. apply Sub_Refl.
    apply H1.
    apply H.
    split.
    apply H0.
    apply sequent_subformulas_transitivity with (B:= AndN B1 B2).
    apply Sub_AndNR. apply Sub_Refl.
    apply H1.
Qed.

Lemma subp_bct_ImpR :
    forall {C: pndctx} {L: octx} {B1 B2: o} {S: sequent},
    subsequent (Sbct C L (Imp B1 B2)) S ->
    subsequent (Sbct C (B1 :: L) B2) S.
Proof.
    intros. unfold subsequent in H. destruct H. destruct H0.
    unfold subsequent. split. apply H.
    split. apply Forall_cons.
    apply sequent_subformulas_transitivity with (B:= Imp B1 B2).
    apply Sub_ImpL. apply Sub_Refl.
    apply H1.
    apply H0.
    apply sequent_subformulas_transitivity with (B:= Imp B1 B2).
    apply Sub_ImpR. apply Sub_Refl.
    apply H1.
Qed.

Lemma subp_ept_Lf : 
    forall {C: pndctx} {N K : o} {S: sequent},
    In N (pndctx_list C) ->
    subsequent (Sept C nil K) S ->
    subsequent (Slfc C N K) S.
Proof.
    intros. unfold subsequent in*.
    destruct H0. destruct H1.
    split. apply H0.
    split. 2: apply H2.
    rewrite Forall_forall in H0.
    specialize (H0 N).
    specialize (H0 H).
    unfold sequent_subformulas_permeable in H0.
    apply filter_In in H0.
    destruct H0. apply H0.
Qed.

Lemma subp_ept_Rf :
    forall {C: pndctx} {P: o} {S: sequent},
    subsequent (Sept C nil P) S -> 
    subsequent (Srfc C P) S.
Proof.
    intros. unfold subsequent in*. destruct H. destruct H0.
    split. apply H. apply H1.
Qed.

Lemma subp_ept_boxL:
    forall {C: pndctx} {L: octx} {B K: o} {S: sequent},
    subsequent (Sept C (B :: L) K) S ->
    subsequent (Sept (pndctx_insert B C) L K) S.
Proof.
    intros. unfold subsequent in*. destruct H. destruct H0.
    inversion H0. subst.
    split.
    - unfold pndctx_insert.
        unfold pndctx_list.
        simpl. unfold raw_insert.
        destruct permeable_dec.
        + destruct in_dec.
            -- apply H.
            -- apply Forall_cons.
                ++ unfold sequent_subformulas_permeable.
                    apply filter_In. split. apply H4. apply permeable_b_iff. apply p.
                ++ apply H.
        + apply H.
    - split.
        + eapply Forall_cons_iff. apply H0.
        + apply H1.
Qed.
    
Lemma subp_ept_AndPL:
    forall {C: pndctx} {L: octx} {B1 B2 : o} {K: o} {S: sequent},
    subsequent (Sept C ((AndP B1 B2) :: L) K) S ->
    subsequent (Sept C (B2 :: B1 :: L) K) S.
Proof.
    intros. unfold subsequent in*. destruct H. destruct H0.
    split. apply H.
    split. 2: apply H1.
    apply Forall_cons.
    - inversion H0. subst. 
        eapply sequent_subformulas_transitivity with (B:= AndP B1 B2).
        apply Sub_AndPR. apply Sub_Refl.
        apply H4.
    - apply Forall_cons.
        +  inversion H0. subst. 
            eapply sequent_subformulas_transitivity with (B:= AndP B1 B2).
            apply Sub_AndPL. apply Sub_Refl.
            apply H4.
        + inversion H0. subst. apply H5.
Qed.

Lemma subp_ept_OrL :
  forall {C: pndctx} {L: octx} {B1 B2 : o} {K: o} {S: sequent},
    subsequent (Sept C ((Or B1 B2) :: L) K) S ->
    subsequent (Sept C (B1 :: L) K) S /\ 
    subsequent (Sept C (B2 :: L) K) S.
Proof.
    intros. unfold subsequent in*. destruct H. destruct H0.
    split.
    - split. apply H.
        inversion H0. subst. split.
        + apply Forall_cons.
            -- eapply sequent_subformulas_transitivity with (B:= Or B1 B2).
                apply Sub_OrL. apply Sub_Refl.
                apply H4.
            -- apply H5.
        + apply H1.
    - split. apply H.
        inversion H0. subst. split.
        + apply Forall_cons.
            -- eapply sequent_subformulas_transitivity with (B:= Or B1 B2).
                apply Sub_OrR. apply Sub_Refl.
                apply H4.
            -- apply H5.
        + apply H1.
Qed.

Lemma subp_ept_TrueL :
  forall {C: pndctx} {L: octx} {K: o} {S: sequent},
    subsequent (Sept C (TT :: L) K) S ->
    subsequent (Sept C L K) S.
Proof.
    intros. unfold subsequent in*. destruct H. destruct H0.
    split. apply H.
    split. inversion H0. subst. apply H5.
    apply H1.
Qed.

Lemma subp_lfc_Rl :
  forall {C : pndctx} {P : o}  {K : o} {S: sequent},
    subsequent (Slfc C P K) S ->
    subsequent (Sept C (P :: nil) K) S.
Proof.
    intros. unfold subsequent in*. destruct H. destruct H0.
    split. apply H.
    split. apply Forall_cons. apply H0. apply Forall_nil. apply H1.
Qed.

Lemma subp_lfc_AndNL_1 :
  forall {C: pndctx} {B1 B2 : o}  {K : o} {S: sequent},
    subsequent (Slfc C (AndN B1 B2) K) S ->
    subsequent (Slfc C B1 K) S.
Proof.
    intros. unfold subsequent in*. destruct H. destruct H0.
    split. apply H.
    split. eapply sequent_subformulas_transitivity with (B:= AndN B1 B2).
    apply Sub_AndNL. apply Sub_Refl.
    apply H0.
    apply H1.
Qed.

Lemma subp_lfc_AndNL_2 :
  forall {C: pndctx} {B1 B2 : o}  {K : o} {S: sequent},
    subsequent (Slfc C (AndN B1 B2) K) S ->
    subsequent (Slfc C B2 K) S.
Proof.
    intros. unfold subsequent in*. destruct H. destruct H0.
    split. apply H.
    split. eapply sequent_subformulas_transitivity with (B:= AndN B1 B2).
    apply Sub_AndNR. apply Sub_Refl.
    apply H0.
    apply H1.
Qed.


Lemma subp_lfc_ImpL :
  forall {C: pndctx} {B1 B2 : o}  {K : o} {S: sequent},
    subsequent (Slfc C (Imp B1 B2) K) S ->
    subsequent (Srfc C B1) S /\ subsequent (Slfc C B2 K) S.
Proof.
    intros. unfold subsequent in*. destruct H. destruct H0.
    split ; split.
    apply H.
    eapply sequent_subformulas_transitivity with (B:= Imp B1 B2).
    apply Sub_ImpL. apply Sub_Refl. apply H0.
    apply H.
    split.
    eapply sequent_subformulas_transitivity with (B:= Imp B1 B2).
    apply Sub_ImpR. apply Sub_Refl. apply H0.
    apply H1.
Qed.

Lemma subp_rfc_Rr :
  forall {C: pndctx} {N: o} {S: sequent},
    subsequent (Srfc C N) S ->
    subsequent (Sbct C nil N) S.
Proof.
    intros. unfold subsequent in*. destruct H.
    split. apply H.
    split. apply Forall_nil. apply H0.
Qed.

Lemma subp_rfc_AndPR :
  forall {C: pndctx} {B1 B2: o} {S: sequent},
    subsequent (Srfc C (AndP B1 B2)) S ->
    subsequent (Srfc C B1) S /\
    subsequent (Srfc C B2) S.
Proof.
    intros. unfold subsequent in*. destruct H.
    split ; split.
    apply H.
    eapply sequent_subformulas_transitivity with (B:= AndP B1 B2).
    apply Sub_AndPL. apply Sub_Refl. apply H0.
    apply H.
    eapply sequent_subformulas_transitivity with (B:= AndP B1 B2).
    apply Sub_AndPR. apply Sub_Refl. apply H0.
Qed.

Lemma subp_rfc_OrR_1 :
  forall {C: pndctx} {B1 B2: o} {S: sequent},
    subsequent (Srfc C (Or B1 B2)) S ->
    subsequent (Srfc C B1) S.
Proof.
    intros. unfold subsequent in*. destruct H.
    split. apply H.
    eapply sequent_subformulas_transitivity with (B:= Or B1 B2).
    apply Sub_OrL. apply Sub_Refl. apply H0.
Qed.

Lemma subp_rfc_OrR_2 :
  forall {C: pndctx} {B1 B2: o} {S: sequent},
    subsequent (Srfc C (Or B1 B2)) S ->
    subsequent (Srfc C B2) S.
Proof.
    intros. unfold subsequent in*. destruct H.
    split. apply H.
    eapply sequent_subformulas_transitivity with (B:= Or B1 B2).
    apply Sub_OrR. apply Sub_Refl. apply H0.
Qed.

