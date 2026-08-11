From Stdlib Require Import List SetoidList PeanoNat.
From LJF Require Import SharedLogic Pndctx LJFn_Rules Schemes.

Theorem LJFn_exchange_structural :
  (forall {n: nat} {C: pndctx} {L: octx} {K: o}, bctn n C L K -> 
    forall {C0: pndctx}, pndctx_set_eq C C0 -> bctn n C0 L K) /\
  (forall {n: nat} {C: pndctx} {L: octx} {K: o}, eptn n C L K -> 
    forall {C0: pndctx}, pndctx_set_eq C C0 -> eptn n C0 L K) /\
  (forall {n: nat} {C: pndctx} {N K: o}, lfcn n C N K -> 
    forall {C0: pndctx}, pndctx_set_eq C C0 -> lfcn n C0 N K) /\
  (forall {n: nat} {C: pndctx} {P: o}, rfcn n C P -> 
    forall {C0: pndctx}, pndctx_set_eq C C0 -> rfcn n C0 P). 
Proof.
    apply LJFn_mutind_all ; intros.
    - apply (bctn_boxR b (H C0 H0)).
    - apply (bctn_AndNR (H C0 H1) (H0 C0 H1)).
    - apply (bctn_ImpR (H C0 H0)).
    - assert (In N (pndctx_list C0)).
        + specialize (proj2 (InA_alt eq N (pndctx_list C))) ; intro.
            specialize (proj1 (H0 N)) ; intro.
            specialize (proj1 (InA_alt eq N (pndctx_list C0))) ; intro.
            destruct H3.
            -- apply H2. apply H1. eexists N. split. reflexivity. apply i.
            -- destruct H3. subst. apply H4.
        + apply (eptn_Lf N H1 b n0 (H C0 H0)).
    - apply (eptn_Rf p (H C0 H0)).
    - apply (eptn_boxL b p (H (pndctx_insert B C0) (pndctx_set_eq_pndctx_insert H0))).
    - apply (eptn_AndPL b (H C0 H0)).
    - apply (eptn_OrL b (H C0 H1) (H0 C0 H1)).
    - apply (eptn_TrueL b (H C0 H0)).
    - apply (eptn_FalseL n b).
    - apply (lfcn_Rl b p (H C0 H0)).
    - apply (lfcn_Il n n0 a).
    - apply (lfcn_AndNL_1 b (H C0 H0)).
    - apply (lfcn_AndNL_2 b (H C0 H0)).
    - apply (lfcn_ImpL b (H C0 H1) (H0 C0 H1)).
    - apply (rfcn_Rr n0 (H C0 H0)).
    - assert (In P (pndctx_list C0)).
        + specialize (proj2 (InA_alt eq P (pndctx_list C))) ; intro.
            specialize (proj1 (H P)) ; intro.
            specialize (proj1 (InA_alt eq P (pndctx_list C0))) ; intro.
            destruct H2.
            -- apply H1. apply H0. eexists P. split. reflexivity. apply i.
            -- destruct H2. subst. apply H3.
        + apply (rfcn_Ir n H0 p a).
    - apply (rfcn_AndPR (H C0 H1) (H0 C0 H1)).
    - apply (rfcn_OrR_1 (H C0 H0)).
    - apply (rfcn_OrR_2 (H C0 H0)).
    - apply (rfcn_TrueR n).
Qed.