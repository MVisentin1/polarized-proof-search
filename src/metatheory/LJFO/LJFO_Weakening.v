From Stdlib Require Import List Permutation.
From LJF Require Import SharedLogic LJFO_Rules LJFO_Exchange Schemes.

Lemma LJFO_structural_cons_weakening : 
    (forall {C: sctx} {L: octx} {K: o}, bctO C L K ->
        forall {E: o}, bctO (E :: C) L K) /\
    (forall {C: sctx} {L: octx} {K: o}, eptO C L K ->
        forall {E: o}, eptO (E :: C) L K) /\
    (forall {C: sctx} {N K: o}, lfcO C N K ->
        forall {E: o}, lfcO (E :: C) N K) /\
    (forall {C: sctx} {K: o}, rfcO C K ->
        forall {E: o}, rfcO (E :: C) K).
    apply LJFO_mutind_all ; intros.
    - apply bctO_boxR. apply b. apply H.
    - apply bctO_AndNR. apply H. apply H0.
    - apply bctO_ImpR. apply H. 
    - eapply eptO_Lf. apply in_cons. apply i. apply b. apply n. apply H.
    - apply eptO_Rf. apply p. apply H.
    - apply eptO_boxL. apply b. apply p. eapply LJFO_exchange_structural_eptO.
        apply H. apply perm_swap.
    - apply eptO_AndPL. apply b. apply H. 
    - apply eptO_OrL. apply b. apply H. 
        apply H0. 
    - apply eptO_TrueL. apply b. apply H. 
    - apply eptO_FalseL. apply b.
    - apply lfcO_Rl. apply b. apply p. apply H. 
    - apply lfcO_Il. apply n. apply a.
    - apply lfcO_AndNL_1. apply b. apply H. 
    - apply lfcO_AndNL_2. apply b. apply H. 
    - apply lfcO_ImpL. apply b. apply H. 
        apply H0. 
    - apply rfcO_Rr. apply n. apply H. 
    - apply rfcO_Ir. apply in_cons. apply i. apply p. apply a.
    - apply rfcO_AndPR. apply H.  apply H0. 
    - apply rfcO_OrR_1. apply H. 
    - apply rfcO_OrR_2. apply H. 
    - apply rfcO_TrueR.
Qed.

Lemma LJFO_structural_cons_weakening_eptO : 
    forall {C: sctx} {L: octx} {K: o}, eptO C L K ->
        forall {E: o}, eptO (E :: C) L K.
Proof.        
    destruct LJFO_structural_cons_weakening. destruct H0. apply H0.
Qed.
