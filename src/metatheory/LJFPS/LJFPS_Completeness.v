From Stdlib Require Import List Permutation.

From LJF Require Import SharedLogic LJFPS_Rules LJFC_Rules Schemes.

Theorem LJFC_completeness :
    (forall {C: sctx} {L: octx} {K: o}, bctO C L K -> bct (mk_ndctx C) L K) /\
    (forall {C: sctx} {L: octx} {K: o}, eptO C L K -> ept (mk_ndctx C) L K) /\
    (forall {C: sctx} {N K: o}, lfcO C N K -> lfc (mk_ndctx C) N K) /\
    (forall {C: sctx} {K: o}, rfcO C K -> rfc (mk_ndctx C) K).
Proof.
    apply LJFPS_mutind_all ; intros.
    - apply bct_boxR. apply b. apply H.
    - apply bct_AndNR. apply H. apply H0.
    - apply bct_ImpR. apply H.
    - eapply ept_Lf. apply nodup_In. apply i. apply b. apply n. apply H.
    - apply ept_Rf. apply p. apply H.
    - apply ept_boxL. apply b. apply p.
        rewrite ndctx_insert_mk_ndctx_eq. apply H.
    - apply ept_AndPL. apply b. apply H.
    - apply ept_OrL. apply b. apply H. apply H0.
    - apply ept_TrueL. apply b. apply H.
    - apply ept_FalseL. apply b.
    - apply lfc_Rl. apply b. apply p. apply H.
    - apply lfc_Il. apply n. apply a.
    - apply lfc_AndNL_1. apply b. apply H.
    - apply lfc_AndNL_2. apply b. apply H.
    - apply lfc_ImpL. apply b. apply H. apply H0.
    - apply rfc_Rr. apply n. apply H.
    - apply rfc_Ir. apply nodup_In. apply i. apply p. apply a.
    - apply rfc_AndPR. apply H. apply H0.
    - apply rfc_OrR_1. apply H.
    - apply rfc_OrR_2. apply H.
    - apply rfc_TrueR.
Qed.