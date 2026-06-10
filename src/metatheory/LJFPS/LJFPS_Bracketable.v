From Stdlib Require Import List.

From LJF Require Import SharedLogic Pndctx LJFPS_Rules Schemes.

Lemma LJFPS_bracketable_goal :
  (forall {C: pndctx} {L: octx} {K: o}, ept C L K -> bracketable K) /\
  (forall {C: pndctx} {N K: o}, lfc C N K -> bracketable K).
Proof.
  apply LJFPS_bracketable_mutind.
  all : intros ; auto.
  apply Bracketable_pos. apply p.
  apply Bracketable_neg_atom. apply a. apply n.
Qed.