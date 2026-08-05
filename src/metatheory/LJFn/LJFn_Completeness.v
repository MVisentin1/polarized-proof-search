From Stdlib Require Import List PeanoNat.
From LJF Require Import SharedLogic Pndctx LJFPS_Rules LJFn_Rules LJFn_Monotone Schemes.

Theorem LJFn_completeness :
    (forall {C: pndctx} {L: octx} {K: o}, bct C L K -> exists (n: nat), bctn n C L K) /\
    (forall {C: pndctx} {L: octx} {K: o}, ept C L K -> exists (n: nat), eptn n C L K) /\
    (forall {C: pndctx} {N K: o}, lfc C N K -> exists (n: nat), lfcn n C N K) /\
    (forall {C: pndctx} {K: o}, rfc C K -> exists (n: nat), rfcn n C K).
Proof.
    apply LJFPS_mutind_all ; intros.
    - destruct H as [x H] ; eexists (S x). apply (bctn_boxR b H).
    - destruct H as [x H] ; destruct H0 as [y H0] ; eexists (S (max x y)).
        apply (bctn_AndNR (LJFn_monotone_bctn H (Nat.le_max_l x y)) (LJFn_monotone_bctn H0 (Nat.le_max_r x y))).
    - destruct H as [x H] ; eexists (S x). apply (bctn_ImpR H).
    - destruct H as [x H] ; eexists (S x). apply (eptn_Lf N i b n H).
    - destruct H as [x H] ; eexists (S x). apply (eptn_Rf p H).
    - destruct H as [x H] ; eexists (S x). apply (eptn_boxL b p H).
    - destruct H as [x H] ; eexists (S x). apply (eptn_AndPL b H).
    - destruct H as [x H] ; destruct H0 as [y H0] ; eexists (S (max x y)).
        apply (eptn_OrL b (LJFn_monotone_eptn H (Nat.le_max_l x y)) (LJFn_monotone_eptn H0 (Nat.le_max_r x y))).
    - destruct H as [x H] ; eexists (S x). apply (eptn_TrueL b H).
    - eexists (S 0). apply (eptn_FalseL 0 b).
    - destruct H as [x H] ; eexists (S x). apply (lfcn_Rl b p H).
    - eexists (S 0). apply (lfcn_Il 0 n a).
    - destruct H as [x H] ; eexists (S x). apply (lfcn_AndNL_1 b H).
    - destruct H as [x H] ; eexists (S x). apply (lfcn_AndNL_2 b H).
    - destruct H as [x H] ; destruct H0 as [y H0] ; eexists (S (max x y)).
        apply (lfcn_ImpL b (LJFn_monotone_rfcn H (Nat.le_max_l x y)) (LJFn_monotone_lfcn H0 (Nat.le_max_r x y))).
    - destruct H as [x H] ; eexists (S x). apply (rfcn_Rr n H).
    - eexists (S 0). apply (rfcn_Ir 0 i p a).
    - destruct H as [x H] ; destruct H0 as [y H0] ; eexists (S (max x y)).
        apply (rfcn_AndPR (LJFn_monotone_rfcn H (Nat.le_max_l x y)) (LJFn_monotone_rfcn H0 (Nat.le_max_r x y))).
    - destruct H as [x H] ; eexists (S x). apply (rfcn_OrR_1 H).
    - destruct H as [x H] ; eexists (S x). apply (rfcn_OrR_2 H).
    - eexists (S 0). apply (rfcn_TrueR 0).
Qed.
