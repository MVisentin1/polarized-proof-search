From Stdlib Require Import List.
From CARVe Require Import contexts.list.
From CARVe Require Import algebras.dill.
From LJF Require Import LJF_Rules LJF4_Rules SharedLogic LJFPS_Prover LJF4_Exchange.

Lemma admissibility_L_false_star : forall {K: o} {C: dctx}, 
    has_entry C (FF, one) -> 
    bct4 C K.
Proof. 
    induction K ; intros.
        - apply bct4_R_box.
            + destruct p. T_bracketable. T_bracketable.
            + apply ept4_L_False. apply H. destruct p. T_bracketable. T_bracketable.
        - apply bct4_R_box.
            + T_bracketable. 
            + apply ept4_L_False. apply H. T_bracketable.
        - apply bct4_R_box.
            + T_bracketable.
            + apply ept4_L_False. apply H. T_bracketable.
        - apply bct4_R_box.
            + T_bracketable.
            + apply ept4_L_False. apply H. T_bracketable.
        - apply bct4_R_AndN.
            + apply IHK1. apply H.
            + apply IHK2. apply H.  
        - apply bct4_R_box.
            + T_bracketable.
            + apply ept4_L_False. apply H. T_bracketable.
        - apply bct4_R_Impl. apply IHK2. apply in_cons. apply H.
Qed.


Lemma admissibility_L_box_star :
  forall (B : o), permeable B ->
  forall {C1 : dctx} {K : o}, bct4 C1 K ->
  forall {C : dctx},
    has_entry C (B, one) ->
    upd_rel_ex C (B, one) (B, omega) C1 ->
    bct4 C K.
Proof.
    intros B H0 C1 K H1. induction H1; intros C' H2 H3.
        - apply bct4_R_box. apply H. eapply ept4_L_box with (B := B).
            apply H2. apply H3. apply H. apply H0. apply H1.
        - apply bct4_R_AndN. 
            + apply IHbct4_1. apply H2. apply H3.
            + apply IHbct4_2. apply H2. apply H3.  
        - apply bct4_R_Impl. apply IHbct4.
            + apply in_cons. apply H2.
            + apply upd_rel_ex_cons. apply H3.
Qed.

Lemma admissibility_L_true_star :
    forall {C1 : dctx} {K : o}, bct4 C1 K ->
    forall {C: dctx}, 
        has_entry C (TT, one) ->
        upd_rel_ex C (TT, one) (TT, zero) C1 ->
        bct4 C K.
Proof. intros C1 K H1. induction H1 ; intros C' H2 H3.
    - apply bct4_R_box. apply H. eapply ept4_L_True.
        apply H2. apply H3. apply H. apply H0.
    - apply bct4_R_AndN.
        + apply IHbct4_1. apply H2. apply H3.
        + apply IHbct4_2. apply H2. apply H3.
    - apply bct4_R_Impl. apply IHbct4. 
        + apply in_cons. apply H2.
        + apply upd_rel_ex_cons. apply H3.
Qed.

Lemma admissibility_L_AndP_star :
    forall {C1: dctx} (B1 B2: o) {K: o}, bct4 ((B2, one) :: (B1, one) :: C1) K ->
    forall {C: dctx}, 
        has_entry C ((AndP B1 B2), one) ->
        upd_rel_ex C ((AndP B1 B2), one) ((AndP B1 B2), zero) C1 ->
        bct4 C K.
Proof. intros C1 B1 B2 K H. remember ((B2, one) :: (B1, one) :: C1) as L eqn:HL. revert C1 HL.
    induction H ; intros C1 HL C0 H2 H3. subst C.
    - apply bct4_R_box. apply H. eapply ept4_L_AndP with (B1 := B1) (B2 := B2).
        apply H2. apply H3. apply H. apply H0.  
    - apply bct4_R_AndN. 
        + eapply IHbct4_1. exact HL. apply H2. apply H3.
        + eapply IHbct4_2. exact HL. apply H2. apply H3.
    -
