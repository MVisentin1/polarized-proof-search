From Stdlib Require Import List Permutation.

From LJF Require Import SharedLogic LJFPS_Rules LJFC_Rules Schemes LJFPS_Weakening.

Theorem LJFC_soundness :
    (forall {C: ndctx} {L: octx} {K: o}, bctC C L K -> bct C L K) /\
    (forall {C: ndctx} {L: octx} {K: o}, eptC C L K -> ept C L K) /\
    (forall {C: ndctx} {N K: o}, lfcC C N K -> lfc C N K) /\
    (forall {C: ndctx} {K: o}, rfcC C K -> rfc C K).
Proof.
    apply LJFC_mutind_all ; intros.
    - apply bct_boxR. apply b. apply H.
    - apply bct_AndNR. apply H. apply H0.
    - apply bct_ImpR. apply H.
    - eapply ept_Lf. apply i. apply b. apply n. apply H.
    - apply ept_Rf. apply p. apply H.
    - eapply ept_boxL. apply b. apply p. 
        unfold ndctx_list.
        unfold ndctx_insert in H. simpl in H.
        unfold raw_insert in H.
        destruct (in_dec o_eq_dec B (proj1_sig C)) in H.
        + apply LJFPS_structural_cons_weakening_ept.
            apply H.
        + apply H.
    - eapply ept_AndPL. apply b. apply H.
    - eapply ept_OrL. apply b. apply H. apply H0.
    - eapply ept_TrueL. apply b. apply H.
    - apply ept_FalseL. apply b.
    - apply lfc_Rl. apply b. apply p. apply H.
    - apply lfc_Il. apply n. apply a.
    - apply lfc_AndNL_1. apply b. apply H.
    - apply lfc_AndNL_2. apply b. apply H.
    - apply lfc_ImpL. apply b. apply H. apply H0.
    - apply rfc_Rr. apply n. apply H.
    - apply rfc_Ir. apply i. apply p. apply a.
    - apply rfc_AndPR. apply H. apply H0.
    - apply rfc_OrR_1. apply H.
    - apply rfc_OrR_2. apply H.
    - apply rfc_TrueR.
Qed.