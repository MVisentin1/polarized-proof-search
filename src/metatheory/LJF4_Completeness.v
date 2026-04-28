From Stdlib Require Import List.
From CARVe Require Import contexts.list.
From CARVe Require Import algebras.dill.
From LJF Require Import SharedLogic LJF_Rules LJF4_Rules LJF4_Prover.

Lemma admissibility_L_false : forall (R : o) (C: dctx), 
    has_entry C (FF, one) -> bctLJF4 C R.
Proof. 
    induction R ; intros.
        - apply bctLJF4_R_box.
            + destruct p; T_bracketable.
            + apply eptLJF4_L_False. apply H.
        - apply bctLJF4_R_box.
            + T_bracketable. 
            + apply eptLJF4_L_False. apply H.
        - apply bctLJF4_R_box.
            + T_bracketable.
            + apply eptLJF4_L_False. apply H.
        - apply bctLJF4_R_box.
            + T_bracketable.
            + apply eptLJF4_L_False. apply H.
        - apply bctLJF4_R_AndN.
            + apply IHR1. apply H.
            + apply IHR2. apply H.  
        - apply bctLJF4_R_box.
            + T_bracketable.
            + apply eptLJF4_L_False. apply H.
        - apply bctLJF4_R_Impl. apply IHR2. apply in_cons. apply H.
Qed.

Lemma admissibility_L_box : forall (R: o) (C: dctx) (K: o),
    bctLJF4 C R->
    forall (C1: dctx),
      has_entry C (K, omega) ->
      upd_rel_ex C (K, omega) (K, one) C1 ->
      bctLJF4 C1 R.
Admitted.


