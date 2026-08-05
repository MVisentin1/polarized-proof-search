From Stdlib Require Import List PeanoNat.
From LJF Require Import SharedLogic Pndctx LJFn_Rules Schemes.

Theorem LJFn_monotone : 
    (forall {m: nat} {C: pndctx} {L: octx} {K: o}, bctn m C L K -> forall {n: nat}, m <= n -> bctn n C L K) /\
    (forall {m: nat} {C: pndctx} {L: octx} {K: o}, eptn m C L K -> forall {n: nat}, m <= n -> eptn n C L K) /\
    (forall {m: nat} {C: pndctx} {N K: o}, lfcn m C N K -> forall {n: nat}, m <= n -> lfcn n C N K) /\
    (forall {m: nat} {C: pndctx} {K: o}, rfcn m C K -> forall {n: nat}, m <= n -> rfcn n C K).
Proof.
    apply LJFn_mutind_all ; intros.
    - destruct n0. inversion H0. apply (bctn_boxR b (H n0 (le_S_n n n0 H0))).
    - destruct n0. inversion H1. apply (bctn_AndNR (H n0 (le_S_n n n0 H1)) (H0 n0 (le_S_n n n0 H1))).
    - destruct n0. inversion H0. apply (bctn_ImpR (H n0 (le_S_n n n0 H0))).
    - destruct n1. inversion H0. apply (eptn_Lf N i b n0 (H n1 (le_S_n n n1 H0))).
    - destruct n0. inversion H0. apply (eptn_Rf p (H n0 (le_S_n n n0 H0))).
    - destruct n0. inversion H0. apply (eptn_boxL b p (H n0 (le_S_n n n0 H0))).
    - destruct n0. inversion H0. apply (eptn_AndPL b (H n0 (le_S_n n n0 H0))).
    - destruct n0. inversion H1. apply (eptn_OrL b (H n0 (le_S_n n n0 H1)) (H0 n0 (le_S_n n n0 H1))).
    - destruct n0. inversion H0. apply (eptn_TrueL b (H n0 (le_S_n n n0 H0))).
    - destruct n0. inversion H. apply (eptn_FalseL n0 b).
    - destruct n0. inversion H0. apply (lfcn_Rl b p (H n0 (le_S_n n n0 H0))).
    - destruct n1. inversion H. apply (lfcn_Il n1 n0 a).
    - destruct n0. inversion H0. apply (lfcn_AndNL_1 b (H n0 (le_S_n n n0 H0))).
    - destruct n0. inversion H0. apply (lfcn_AndNL_2 b (H n0 (le_S_n n n0 H0))).
    - destruct n0. inversion H1. apply (lfcn_ImpL b (H n0 (le_S_n n n0 H1)) (H0 n0 (le_S_n n n0 H1))).
    - destruct n1. inversion H0. apply (rfcn_Rr n0 (H n1 (le_S_n n n1 H0))).
    - destruct n0. inversion H. apply (rfcn_Ir n0 i p a).
    - destruct n0. inversion H1. apply (rfcn_AndPR (H n0 (le_S_n n n0 H1)) (H0 n0 (le_S_n n n0 H1))).
    - destruct n0. inversion H0. apply (rfcn_OrR_1 (H n0 (le_S_n n n0 H0))).
    - destruct n0. inversion H0. apply (rfcn_OrR_2 (H n0 (le_S_n n n0 H0))).
    - destruct n0. inversion H. apply (rfcn_TrueR n0).
Qed.    