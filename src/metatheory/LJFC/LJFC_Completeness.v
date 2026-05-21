From Stdlib Require Import List Permutation.

From LJF Require Import SharedLogic LJFPS_Rules LJFC_Rules.

Scheme bct_mut := Induction for bct Sort Prop
  with ept_mut := Induction for ept Sort Prop
  with lfc_mut := Induction for lfc Sort Prop
  with rfc_mut := Induction for rfc Sort Prop.

Combined Scheme LJFPS_mutind_all from bct_mut, ept_mut, lfc_mut, rfc_mut.

Theorem LJFC_completeness : 
    (forall {C: sctx} {L: octx} {K: o}, bct C L K -> bctC (nodup o_eq_dec C) L K) /\
    (forall {C: sctx} {L: octx} {K: o}, ept C L K -> eptC (nodup o_eq_dec C) L K) /\
    (forall {C: sctx} {N K: o}, lfc C N K -> lfcC (nodup o_eq_dec C) N K) /\
    (forall {C: sctx} {K: o}, rfc C K -> rfcC (nodup o_eq_dec C) K).
Proof.
    apply LJFPS_mutind_all ; intros.
    - apply bctC_boxR. apply NoDup_nodup. apply b. apply H.
    - apply bctC_AndNR. apply NoDup_nodup. apply H. apply H0.
    - apply bctC_ImpR. apply NoDup_nodup. apply H.
    - eapply eptC_Lf. apply NoDup_nodup. apply nodup_In. apply i. apply b. apply n. apply H.
    - apply eptC_Rf. apply NoDup_nodup. apply p. apply H.
    - apply eptC_boxL. apply NoDup_nodup. apply b. apply p. unfold ndctx_insert.
        destruct (in_dec o_eq_dec B (nodup o_eq_dec C)).
        + rewrite nodup_In in i. simpl nodup in H.
            destruct (in_dec o_eq_dec B C) in H.
            -- apply H.
            -- contradiction.
        + rewrite nodup_In in n. simpl nodup in H.
            destruct (in_dec o_eq_dec B C) in H.
            -- contradiction.
            -- apply H.
    - apply eptC_AndPL. apply NoDup_nodup. apply b. apply H.
    - apply eptC_OrL. apply NoDup_nodup. apply b. apply H. apply H0.
    - apply eptC_TrueL. apply NoDup_nodup. apply b. apply H.
    - apply eptC_FalseL. apply NoDup_nodup. apply b.
    - apply lfcC_Rl. apply NoDup_nodup. apply b. apply p. apply H.
    - apply lfcC_Il. apply NoDup_nodup. apply n. apply a.
    - apply lfcC_AndNL_1. apply NoDup_nodup. apply b. apply H.
    - apply lfcC_AndNL_2. apply NoDup_nodup. apply b. apply H.
    - apply lfcC_ImpL. apply NoDup_nodup. apply b. apply H. apply H0.
    - apply rfcC_Rr. apply NoDup_nodup. apply n. apply H.
    - apply rfcC_Ir. apply NoDup_nodup. apply nodup_In. apply i. apply p. apply a.
    - apply rfcC_AndPR. apply NoDup_nodup. apply H. apply H0.
    - apply rfcC_OrR_1. apply NoDup_nodup. apply H.
    - apply rfcC_OrR_2. apply NoDup_nodup. apply H.
    - apply rfcC_TrueR. apply NoDup_nodup.
Qed.
