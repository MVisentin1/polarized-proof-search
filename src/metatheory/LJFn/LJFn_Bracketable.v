From Stdlib Require Import List.

From LJF Require Import SharedLogic Pndctx LJFn_Rules Schemes.

Lemma LJFn_bracketable_goal :
  (forall {n: nat} {C: pndctx} {L: octx} {K: o}, eptn n C L K -> bracketable K) /\
  (forall {n: nat} {C: pndctx} {N K: o}, lfcn n C N K -> bracketable K).
Proof.
  apply LJFn_bracketable_mutind.
  all : intros ; auto.
  apply Bracketable_pos. apply p.
  apply Bracketable_neg_atom. apply a. apply n0.
Qed.

Lemma LJFn_bracketable_goal_ept :
  forall {n: nat} {C: pndctx} {L: octx} {K: o}, eptn n C L K -> bracketable K.
Proof.
  destruct LJFn_bracketable_goal. apply H. Qed.

Lemma LJFn_bracketable_goal_lfc :
  forall {n: nat} {C: pndctx} {N K: o}, lfcn n C N K -> bracketable K.
Proof.
  destruct LJFn_bracketable_goal. apply H0. Qed.