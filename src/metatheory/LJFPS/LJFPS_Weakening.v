From Stdlib Require Import List Permutation.
From LJF Require Import SharedLogic LJFPS_Rules LJFPS_Exchange Schemes.

Lemma LJFPS_structural_cons_weakening : 
    (forall {C: sctx} {L: octx} {K: o}, bct C L K ->
        forall {E: o}, bct (E :: C) L K) /\
    (forall {C: sctx} {L: octx} {K: o}, ept C L K ->
        forall {E: o}, ept (E :: C) L K) /\
    (forall {C: sctx} {N K: o}, lfc C N K ->
        forall {E: o}, lfc (E :: C) N K) /\
    (forall {C: sctx} {K: o}, rfc C K ->
        forall {E: o}, rfc (E :: C) K).
    apply LJFPS_mutind_all ; intros.
    - apply bct_boxR. apply b. apply H.
    - apply bct_AndNR. apply H. apply H0.
    - apply bct_ImpR. apply H. 
    - eapply ept_Lf. apply in_cons. apply i. apply b. apply n. apply H.
    - apply ept_Rf. apply p. apply H.
    - apply ept_boxL. apply b. apply p. eapply LJFPS_exchange_structural_ept.
        apply H. apply perm_swap.
    - apply ept_AndPL. apply b. apply H. 
    - apply ept_OrL. apply b. apply H. 
        apply H0. 
    - apply ept_TrueL. apply b. apply H. 
    - apply ept_FalseL. apply b.
    - apply lfc_Rl. apply b. apply p. apply H. 
    - apply lfc_Il. apply n. apply a.
    - apply lfc_AndNL_1. apply b. apply H. 
    - apply lfc_AndNL_2. apply b. apply H. 
    - apply lfc_ImpL. apply b. apply H. 
        apply H0. 
    - apply rfc_Rr. apply n. apply H. 
    - apply rfc_Ir. apply in_cons. apply i. apply p. apply a.
    - apply rfc_AndPR. apply H.  apply H0. 
    - apply rfc_OrR_1. apply H. 
    - apply rfc_OrR_2. apply H. 
    - apply rfc_TrueR.
Qed.

Lemma LJFPS_structural_cons_weakening_ept : 
    forall {C: sctx} {L: octx} {K: o}, ept C L K ->
        forall {E: o}, ept (E :: C) L K.
Proof.        
    destruct LJFPS_structural_cons_weakening. destruct H0. apply H0.
Qed.
