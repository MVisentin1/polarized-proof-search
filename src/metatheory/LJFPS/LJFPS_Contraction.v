From Stdlib Require Import List Permutation.
From LJF Require Import SharedLogic LJFPS_Rules LJFPS_Exchange Schemes.

Lemma LJFPS_structural_cons_contraction : 
    (forall {C: sctx} {L: octx} {K: o}, bct C L K ->
        forall {C1: sctx} {E: o}, Permutation C (E :: C1) -> In E C1 ->  bct C1 L K) /\
    (forall {C: sctx} {L: octx} {K: o}, ept C L K ->
        forall {C1: sctx} {E: o}, Permutation C (E :: C1) -> In E C1 ->  ept C1 L K) /\
    (forall {C: sctx} {N K: o}, lfc C N K ->
        forall {C1: sctx} {E: o}, Permutation C (E :: C1) -> In E C1 ->  lfc C1 N K) /\
    (forall {C: sctx} {K: o}, rfc C K ->
        forall {C1: sctx} {E: o}, Permutation C (E :: C1) -> In E C1 ->  rfc C1 K).
Proof.
    apply LJFPS_mutind_all ; intros.
    - apply bct_boxR. apply b. eapply H. apply H0. apply H1.
    - apply bct_AndNR. 
        eapply H. apply H1. apply H2.
        eapply H0. apply H1. apply H2.
    - apply bct_ImpR. eapply H. apply H0. apply H1.
    - eapply ept_Lf. 3: apply n. eapply Permutation_in in i.
        2: apply H0. inversion i.
        subst. apply H1. apply H2.
        apply b.
        eapply H. apply H0. apply H1.
    - apply ept_Rf. apply p. eapply H. apply H0. apply H1.
    - apply ept_boxL. apply b. apply p. eapply H.
        apply Permutation_sym. eapply perm_trans.
        apply perm_swap. apply Permutation_cons. reflexivity.
        apply Permutation_sym. apply H0. apply in_cons. apply H1.
    - apply ept_AndPL. apply b. eapply H. apply H0. apply H1.
    - apply ept_OrL. apply b. eapply H. apply H1. apply H2. 
        eapply H0. apply H1. apply H2.
    - apply ept_TrueL. apply b. eapply H. apply H0. apply H1.
    - apply ept_FalseL. apply b.
    - apply lfc_Rl. apply b. apply p. eapply H. apply H0. apply H1.
    - apply lfc_Il. apply n. apply a.
    - apply lfc_AndNL_1. apply b. eapply H. apply H0. apply H1.
    - apply lfc_AndNL_2. apply b. eapply H. apply H0. apply H1.
    - apply lfc_ImpL. apply b. eapply H. apply H1. apply H2.
        eapply H0. apply H1. apply H2.
    - apply rfc_Rr. apply n. eapply H. apply H0. apply H1.
    - apply rfc_Ir. eapply Permutation_in in i. 2: apply H.
        inversion i. subst. apply H0. apply H1. apply p. apply a.
    - apply rfc_AndPR. eapply H. apply H1. apply H2. eapply H0. apply H1. apply H2.
    - apply rfc_OrR_1. eapply H. apply H0. apply H1.
    - apply rfc_OrR_2. eapply H. apply H0. apply H1.
    - apply rfc_TrueR.
Qed.

Lemma LJFPS_structural_cons_contraction_ept : 
    forall {C: sctx} {L: octx} {K: o}, ept C L K ->
        forall {C1: sctx} {E: o}, Permutation C (E :: C1) -> In E C1 ->  ept C1 L K.
Proof.        
    destruct LJFPS_structural_cons_contraction. destruct H0. apply H0.
Qed.
