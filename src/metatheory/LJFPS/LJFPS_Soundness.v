From Stdlib Require Import List Permutation.

From LJF Require Import SharedLogic Decidability Pndctx LJFO_Rules LJFO_Weakening LJFPS_Rules Schemes.

Theorem LJFC_soundness :
    (forall {C: pndctx} {L: octx} {K: o}, bct C L K -> bctO (pndctx_list C) L K) /\
    (forall {C: pndctx} {L: octx} {K: o}, ept C L K -> eptO (pndctx_list C) L K) /\
    (forall {C: pndctx} {N K: o}, lfc C N K -> lfcO (pndctx_list C) N K) /\
    (forall {C: pndctx} {K: o}, rfc C K -> rfcO (pndctx_list C) K).
Proof.
    apply LJFPS_mutind_all ; intros.
    - apply bctO_boxR. apply b. apply H.
    - apply bctO_AndNR. apply H. apply H0.
    - apply bctO_ImpR. apply H.
    - eapply eptO_Lf. apply i. apply b. apply n. apply H.
    - apply eptO_Rf. apply p. apply H.
    - eapply eptO_boxL. apply b. apply p. 
        unfold pndctx_list in*. simpl in*.
        unfold raw_insert in H.
        destruct permeable_dec in H.
        + destruct in_dec in H.
            -- apply LJFO_structural_cons_weakening.
                apply H.
            -- apply H.
        + contradiction.
    - eapply eptO_AndPL. apply b. apply H.
    - eapply eptO_OrL. apply b. apply H. apply H0.
    - eapply eptO_TrueL. apply b. apply H.
    - apply eptO_FalseL. apply b.
    - apply lfcO_Rl. apply b. apply p. apply H.
    - apply lfcO_Il. apply n. apply a.
    - apply lfcO_AndNL_1. apply b. apply H.
    - apply lfcO_AndNL_2. apply b. apply H.
    - apply lfcO_ImpL. apply b. apply H. apply H0.
    - apply rfcO_Rr. apply n. apply H.
    - apply rfcO_Ir. apply i. apply p. apply a.
    - apply rfcO_AndPR. apply H. apply H0.
    - apply rfcO_OrR_1. apply H.
    - apply rfcO_OrR_2. apply H.
    - apply rfcO_TrueR.
Qed.