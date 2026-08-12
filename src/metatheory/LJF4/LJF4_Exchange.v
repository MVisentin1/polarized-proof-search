From Stdlib Require Import List Permutation.
From LJF Require Import LJF4_Rules SharedLogic Schemes.

Lemma LJF4_exchange_structural :
  (forall {C: sctx} {L: lctx} {K: o}, bct4 C L K -> forall C1, Permutation C C1 -> bct4 C1 L K) /\
  (forall {C: sctx} {L: lctx} {K: o}, ept4 C L K -> forall C1, Permutation C C1 -> ept4 C1 L K) /\
  (forall {C: sctx} {N K: o}, lfc4 C N K -> forall C1, Permutation C C1 -> lfc4 C1 N K) /\
  (forall {C: sctx} {P: o}, rfc4 C P -> forall C1, Permutation C C1 -> rfc4 C1 P).
Proof.
  apply LJF4_mutind_all ; intros.
    - apply bct4_boxR. apply b. apply H. apply H0.
    - apply bct4_AndNR. apply H. apply H1. apply H0. apply H1.
    - apply bct4_ImpR. apply H. apply H0.
    - eapply ept4_Lf. eapply Permutation_in in i. 2: apply H0. apply i. apply b. apply n.
      apply H. apply H0.
    - apply ept4_Rf. apply p. apply H. apply H0.
    - eapply ept4_boxL. apply p. apply b. apply p0. apply H. apply Permutation_cons. reflexivity. apply H0.
    - eapply ept4_AndPL. apply p. apply b. apply H. apply H0.
    - eapply ept4_OrL. apply p. apply b. apply H. apply H1. apply H0. apply H1.
    - eapply ept4_TrueL. apply p. apply b. apply H. apply H0.
    - eapply ept4_FalseL. apply i. apply b.
    - apply lfc4_Rl. apply b. apply p. apply H. apply H0.
    - apply lfc4_Il. apply n. apply a.
    - apply lfc4_AndNL_1. apply b. apply H. apply H0.
    - apply lfc4_AndNL_2. apply b. apply H. apply H0.
    - apply lfc4_ImpL. apply b. apply H. apply H1. apply H0. apply H1.
    - apply rfc4_Rr. apply n. apply H. apply H0.
    - apply rfc4_Ir. eapply Permutation_in in i. 2: apply H. apply i. apply p. apply a.
    - apply rfc4_AndPR. apply H. apply H1. apply H0. apply H1.
    - apply rfc4_OrR_1. apply H. apply H0.
    - apply rfc4_OrR_2. apply H. apply H0.
    - apply rfc4_TrueR.
Qed.

Lemma LJF4_exchange_structural_bct4 :
    forall {C: sctx} {L: lctx} {K: o}, bct4 C L K -> forall {C': sctx}, Permutation C C' -> bct4 C' L K.
Proof.
  destruct LJF4_exchange_structural. apply H.
Qed.

Lemma LJF4_exchange_structural_ept4 :
    forall {C: sctx} {L: lctx} {K: o}, ept4 C L K -> forall {C': sctx}, Permutation C C' -> ept4 C' L K.
Proof.
  destruct LJF4_exchange_structural. destruct H0. apply H0.
Qed.

Lemma LJF4_exchange_structural_lfc4 :
  forall {C: sctx} {N K: o}, lfc4 C N K -> forall {C': sctx}, Permutation C C' -> lfc4 C' N K.
Proof.
  destruct LJF4_exchange_structural. destruct H0. destruct H1. apply H1.
Qed.

Lemma LJF4_exchange_structural_rfc4 :
  forall {C: sctx} {K: o}, rfc4 C K -> forall {C': sctx}, Permutation C C' -> rfc4 C' K.
Proof.
  destruct LJF4_exchange_structural. destruct H0. destruct H1. apply H2.
Qed.

Lemma LJF4_exchange_linear :
  (forall {C: sctx} {L: lctx} {K: o}, bct4 C L K -> forall L1, Permutation L L1 -> bct4 C L1 K) /\
  (forall {C: sctx} {L: lctx} {K: o}, ept4 C L K -> forall L1, Permutation L L1 -> ept4 C L1 K).
Proof.
  eapply LJF4_mutind_async ; intros.
    - apply bct4_boxR. apply b. apply H. apply H0.
    - apply bct4_AndNR. apply H. apply H1. apply H0. apply H1.
    - apply bct4_ImpR. apply H. apply Permutation_cons. reflexivity. apply H0.
    - apply Permutation_nil in H. subst.
      eapply ept4_Lf. apply i. apply b. apply n. apply l.
    - apply Permutation_nil in H. subst.
      eapply ept4_Rf. apply p. apply r.
    - eapply ept4_boxL. 
      apply Permutation_sym in H0. eapply perm_trans. apply H0. apply p.
      apply b. apply p0. apply e.
    - eapply ept4_AndPL. 
      apply Permutation_sym in H0. eapply perm_trans. apply H0. apply p.
      apply b. apply e.
    - eapply ept4_OrL. 
      apply Permutation_sym in H1. eapply perm_trans. apply H1. apply p.
      apply b. apply e. apply e0.
    - eapply ept4_TrueL. 
      apply Permutation_sym in H0. eapply perm_trans. apply H0. apply p.
      apply b. apply e.
    - eapply ept4_FalseL. eapply Permutation_in in i. 2: apply H. apply i. apply b.
Qed.

Lemma LJF4_exchange_linear_bct4 :
  forall {C: sctx} {L: lctx} {K: o}, bct4 C L K -> forall {L1: octx}, Permutation L L1 -> bct4 C L1 K.
Proof.
  destruct LJF4_exchange_linear. apply H.
Qed.

Lemma LJF4_exchange_linear_ept4 :
  forall {C: sctx} {L: lctx} {K: o}, ept4 C L K -> forall {L1: octx}, Permutation L L1 -> ept4 C L1 K.
Proof.
  destruct LJF4_exchange_linear. apply H0.
Qed.

