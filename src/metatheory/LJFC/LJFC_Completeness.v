From Stdlib Require Import List Permutation.

From LJF Require Import SharedLogic LJFPS_Rules LJFC_Rules Schemes.

Theorem LJFC_completeness :
    (forall {C: sctx} {L: octx} {K: o}, bct C L K -> bctC (mk_ndctx C) L K) /\
    (forall {C: sctx} {L: octx} {K: o}, ept C L K -> eptC (mk_ndctx C) L K) /\
    (forall {C: sctx} {N K: o}, lfc C N K -> lfcC (mk_ndctx C) N K) /\
    (forall {C: sctx} {K: o}, rfc C K -> rfcC (mk_ndctx C) K).
Proof.
    apply LJFPS_mutind_all ; intros.
    - apply bctC_boxR. apply b. apply H.
    - apply bctC_AndNR. apply H. apply H0.
    - apply bctC_ImpR. apply H.
    - eapply eptC_Lf. apply nodup_In. apply i. apply b. apply n. apply H.
    - apply eptC_Rf. apply p. apply H.
    - apply eptC_boxL. apply b. apply p.
        rewrite ndctx_insert_mk_ndctx_eq. apply H.
    - apply eptC_AndPL. apply b. apply H.
    - apply eptC_OrL. apply b. apply H. apply H0.
    - apply eptC_TrueL. apply b. apply H.
    - apply eptC_FalseL. apply b.
    - apply lfcC_Rl. apply b. apply p. apply H.
    - apply lfcC_Il. apply n. apply a.
    - apply lfcC_AndNL_1. apply b. apply H.
    - apply lfcC_AndNL_2. apply b. apply H.
    - apply lfcC_ImpL. apply b. apply H. apply H0.
    - apply rfcC_Rr. apply n. apply H.
    - apply rfcC_Ir. apply nodup_In. apply i. apply p. apply a.
    - apply rfcC_AndPR. apply H. apply H0.
    - apply rfcC_OrR_1. apply H.
    - apply rfcC_OrR_2. apply H.
    - apply rfcC_TrueR.
Qed.