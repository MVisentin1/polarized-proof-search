From Stdlib Require Import List Permutation.

From LJF Require Import SharedLogic Decidability Predicates LJFO_Rules Pndctx LJFPS_Rules Schemes.

Theorem LJFPS_completeness :
    (forall {C: sctx} {L: octx} {K: o}, bctO C L K -> bct (mk_pndctx C) L K) /\
    (forall {C: sctx} {L: octx} {K: o}, eptO C L K -> ept (mk_pndctx C) L K) /\
    (forall {C: sctx} {N K: o}, lfcO C N K -> lfc (mk_pndctx C) N K) /\
    (forall {C: sctx} {K: o}, rfcO C K -> rfc (mk_pndctx C) K).
Proof.
    apply LJFO_mutind_all ; intros.
    - apply bct_boxR. apply b. apply H.
    - apply bct_AndNR. apply H. apply H0.
    - apply bct_ImpR. apply H.
    - eapply ept_Lf. 3: apply n. unfold pndctx_list. unfold mk_pndctx. simpl.
        apply filter_In. split.
        + apply nodup_In. apply i.
        + apply permeable_b_iff. apply Permeable_neg. apply n.
        + apply b.
        + apply H.
    - apply ept_Rf. apply p. apply H.
    - apply ept_boxL. apply b. apply p.
        rewrite pndctx_insert_mk_pndctx_eq. apply H.
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
    - apply rfc_Ir. unfold pndctx_list. unfold mk_pndctx. simpl. 
        apply filter_In. split. apply nodup_In. apply i. 
        apply permeable_b_iff. apply Permeable_pos_atom. apply a. apply p. apply p. apply a.
    - apply rfc_AndPR. apply H. apply H0.
    - apply rfc_OrR_1. apply H.
    - apply rfc_OrR_2. apply H.
    - apply rfc_TrueR.
Qed.