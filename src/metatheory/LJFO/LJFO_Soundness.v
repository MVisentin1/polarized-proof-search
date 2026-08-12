From Stdlib Require Import List Permutation.
From LJF Require Import SharedLogic LJF4_Rules LJFO_Rules Schemes.

Theorem LJFO_soundness : 
    (forall {C: sctx} {L: lctx} {K: o}, bctO C L K -> bct4 C L K) /\
    (forall {C: sctx} {L: lctx} {K: o}, eptO C L K -> ept4 C L K) /\
    (forall {C: sctx} {N K: o}, lfcO C N K -> lfc4 C N K) /\
    (forall {C: sctx} {K: o}, rfcO C K -> rfc4 C K).
Proof.
    apply LJFO_mutind_all ; intros.
    - apply bct4_boxR. apply b. apply H.
    - apply bct4_AndNR. apply H. apply H0.
    - apply bct4_ImpR. apply H.
    - eapply ept4_Lf. apply i. apply b. apply n. apply H.
    - apply ept4_Rf. apply p. apply H.
    - eapply ept4_boxL. apply Permutation_refl. apply b. apply p. apply H.
    - eapply ept4_AndPL. apply Permutation_refl. apply b. apply H.
    - eapply ept4_OrL. apply Permutation_refl. apply b. apply H. apply H0.
    - eapply ept4_TrueL. apply Permutation_refl. apply b. apply H.
    - apply ept4_FalseL. apply in_eq. apply b.
    - apply lfc4_Rl. apply b. apply p. apply H.
    - apply lfc4_Il. apply n. apply a.
    - apply lfc4_AndNL_1. apply b. apply H.
    - apply lfc4_AndNL_2. apply b. apply H.
    - apply lfc4_ImpL. apply b. apply H. apply H0.
    - apply rfc4_Rr. apply n. apply H.
    - apply rfc4_Ir. apply i. apply p. apply a.
    - apply rfc4_AndPR. apply H. apply H0.
    - apply rfc4_OrR_1. apply H.
    - apply rfc4_OrR_2. apply H.
    - apply rfc4_TrueR.
Qed.
