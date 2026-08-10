From Stdlib Require Import List PeanoNat.
From LJF Require Import SharedLogic Pndctx LJFPS_Rules LJFn_Rules LJFn_Monotone Schemes.

Theorem LJFn_soundness :
    (forall {n: nat} {C: pndctx} {L: octx} {K: o}, bctn n C L K -> bct C L K) /\
    (forall {n: nat} {C: pndctx} {L: octx} {K: o}, eptn n C L K -> ept C L K) /\
    (forall {n: nat} {C: pndctx} {N K: o}, lfcn n C N K -> lfc C N K) /\
    (forall {n: nat} {C: pndctx} {K: o}, rfcn n C K -> rfc C K).
Proof.
    apply LJFn_mutind_all ; intros.
    - apply (bct_boxR b H).
    - apply (bct_AndNR H H0).
    - apply (bct_ImpR H).
    - apply (ept_Lf N i b n0 H).
    - apply (ept_Rf p H).
    - apply (ept_boxL b p H).
    - apply (ept_AndPL b H).
    - apply (ept_OrL b H H0).
    - apply (ept_TrueL b H).
    - apply (ept_FalseL b).
    - apply (lfc_Rl b p H).
    - apply (lfc_Il n0 a).
    - apply (lfc_AndNL_1 b H).
    - apply (lfc_AndNL_2 b H).
    - apply (lfc_ImpL b H H0).
    - apply (rfc_Rr n0 H).
    - apply (rfc_Ir i p a).
    - apply (rfc_AndPR H H0).
    - apply (rfc_OrR_1 H).
    - apply (rfc_OrR_2 H).
    - apply (rfc_TrueR).
Qed.
