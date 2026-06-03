From Stdlib Require Import List Permutation.
From LJF Require Import SharedLogic LJF4_Rules LJFO_Rules LJFO_Exchange Schemes.

Theorem LJFO_completeness : 
    (forall {C: sctx} {L: lctx} {K: o}, bct4 C L K -> bctO C L K) /\
    (forall {C: sctx} {L: lctx} {K: o}, ept4 C L K -> eptO C L K) /\
    (forall {C: sctx} {N K: o}, lfc4 C N K -> lfcO C N K) /\
    (forall {C: sctx} {K: o}, rfc4 C K -> rfcO C K).
Proof.
    apply LJF4_mutind_all ; intros.
        - apply bctO_boxR. apply b. apply H.
        - apply bctO_AndNR. apply H. apply H0.
        - apply bctO_ImpR. apply H.
        - eapply eptO_Lf. apply i. apply b. apply n. apply H.
        - apply eptO_Rf. apply p. apply H.
        - eapply LJFO_exchange_ordered_eptO. 2: apply Permutation_sym. 2: apply p.
            apply eptO_boxL. apply b. apply p0. apply H.
        - eapply LJFO_exchange_ordered_eptO. 2: apply Permutation_sym. 2: apply p.
            apply eptO_AndPL. apply b. apply H.
        - eapply LJFO_exchange_ordered_eptO. 2: apply Permutation_sym. 2: apply p.
            apply eptO_OrL. apply b. apply H. apply H0.
        - eapply LJFO_exchange_ordered_eptO. 2: apply Permutation_sym. 2: apply p.
            apply eptO_TrueL. apply b. apply H.
        - apply eager_FalseL. apply b. apply i.
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

            
        


