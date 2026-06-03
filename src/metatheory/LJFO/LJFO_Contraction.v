From Stdlib Require Import List Permutation.
From LJF Require Import SharedLogic LJFO_Rules LJFO_Exchange Schemes.

Lemma LJFO_structural_cons_contraction : 
    (forall {C: sctx} {L: octx} {K: o}, bctO C L K ->
        forall {C1: sctx} {E: o}, Permutation C (E :: C1) -> In E C1 ->  bctO C1 L K) /\
    (forall {C: sctx} {L: octx} {K: o}, eptO C L K ->
        forall {C1: sctx} {E: o}, Permutation C (E :: C1) -> In E C1 ->  eptO C1 L K) /\
    (forall {C: sctx} {N K: o}, lfcO C N K ->
        forall {C1: sctx} {E: o}, Permutation C (E :: C1) -> In E C1 ->  lfcO C1 N K) /\
    (forall {C: sctx} {K: o}, rfcO C K ->
        forall {C1: sctx} {E: o}, Permutation C (E :: C1) -> In E C1 ->  rfcO C1 K).
Proof.
    apply LJFO_mutind_all ; intros.
    - apply bctO_boxR. apply b. eapply H. apply H0. apply H1.
    - apply bctO_AndNR. 
        eapply H. apply H1. apply H2.
        eapply H0. apply H1. apply H2.
    - apply bctO_ImpR. eapply H. apply H0. apply H1.
    - eapply eptO_Lf. 3: apply n. eapply Permutation_in in i.
        2: apply H0. inversion i.
        subst. apply H1. apply H2.
        apply b.
        eapply H. apply H0. apply H1.
    - apply eptO_Rf. apply p. eapply H. apply H0. apply H1.
    - apply eptO_boxL. apply b. apply p. eapply H.
        apply Permutation_sym. eapply perm_trans.
        apply perm_swap. apply Permutation_cons. reflexivity.
        apply Permutation_sym. apply H0. apply in_cons. apply H1.
    - apply eptO_AndPL. apply b. eapply H. apply H0. apply H1.
    - apply eptO_OrL. apply b. eapply H. apply H1. apply H2. 
        eapply H0. apply H1. apply H2.
    - apply eptO_TrueL. apply b. eapply H. apply H0. apply H1.
    - apply eptO_FalseL. apply b.
    - apply lfcO_Rl. apply b. apply p. eapply H. apply H0. apply H1.
    - apply lfcO_Il. apply n. apply a.
    - apply lfcO_AndNL_1. apply b. eapply H. apply H0. apply H1.
    - apply lfcO_AndNL_2. apply b. eapply H. apply H0. apply H1.
    - apply lfcO_ImpL. apply b. eapply H. apply H1. apply H2.
        eapply H0. apply H1. apply H2.
    - apply rfcO_Rr. apply n. eapply H. apply H0. apply H1.
    - apply rfcO_Ir. eapply Permutation_in in i. 2: apply H.
        inversion i. subst. apply H0. apply H1. apply p. apply a.
    - apply rfcO_AndPR. eapply H. apply H1. apply H2. eapply H0. apply H1. apply H2.
    - apply rfcO_OrR_1. eapply H. apply H0. apply H1.
    - apply rfcO_OrR_2. eapply H. apply H0. apply H1.
    - apply rfcO_TrueR.
Qed.

Lemma LJFO_structural_cons_contraction_eptO : 
    forall {C: sctx} {L: octx} {K: o}, eptO C L K ->
        forall {C1: sctx} {E: o}, Permutation C (E :: C1) -> In E C1 ->  eptO C1 L K.
Proof.        
    destruct LJFO_structural_cons_contraction. destruct H0. apply H0.
Qed.
