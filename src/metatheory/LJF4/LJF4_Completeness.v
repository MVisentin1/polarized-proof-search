From Stdlib Require Import List Permutation.
From LJF Require Import SharedLogic LJF_Rules LJF4_Rules LJF4_Exchange Schemes.

Lemma admissibility_boxL_star :
  forall {C: sctx} {L1: lctx} (B: o) {K: o},
    permeable B ->
    bct4 (B :: C) L1 K ->
    forall {L: lctx},
      Permutation L (B :: L1) ->
      bct4 C L K.
Proof.
  intros C L1 B K p H. remember (B :: C). induction H ; intros ; subst.
    - eapply LJF4_exchange_linear_bct4.
      2: apply Permutation_sym ; apply H1.
      apply bct4_boxR. apply H.
      eapply ept4_boxL. apply Permutation_refl. apply H. apply p. apply H0. 
    - apply bct4_AndNR.
      + apply IHbct4_1. reflexivity. apply H1.
      + apply IHbct4_2. reflexivity. apply H1.
    - apply bct4_ImpR. 
      apply IHbct4. reflexivity. 
      assert (Permutation (B1 :: B :: L) (B :: B1 :: L)). apply perm_swap.
      eapply perm_trans. 2: apply H1.
      apply Permutation_cons. reflexivity. apply H0.
Qed.

Lemma admissibility_TrueL_star :
  forall {C: sctx} {L1: lctx} {K: o},
    bct4 C L1 K ->
    forall {L: lctx},
      Permutation L (TT :: L1) ->
      bct4 C L K.
Proof.
  intros C L1 K H. induction H ; intros.
    - apply bct4_boxR. apply H.
      eapply ept4_TrueL. apply H1. apply H. apply H0.
    - apply bct4_AndNR. apply IHbct4_1. apply H1. apply IHbct4_2. apply H1.
    - apply bct4_ImpR. apply IHbct4. 
      apply Permutation_sym. rewrite perm_swap. apply Permutation_cons.
      reflexivity. apply Permutation_sym. apply H0.
Qed.

Lemma admissibility_FalseL_star :
  forall {C: sctx} {L: lctx} {K: o},
    In FF L ->
    bct4 C L K.
Proof.
  intros C L K. revert C L. induction K ; intros.
    - destruct p.
      + apply bct4_boxR. apply Bracketable_pos. apply Pos_atom.
        apply ept4_FalseL. apply H. apply Bracketable_pos. apply Pos_atom.
      + apply bct4_boxR. apply Bracketable_neg_atom. apply Is_atom. apply Neg_atom.
        apply ept4_FalseL. apply H. apply Bracketable_neg_atom. apply Is_atom. apply Neg_atom.
    - apply bct4_boxR. apply Bracketable_pos. apply Pos_true.
        apply ept4_FalseL. apply H. apply Bracketable_pos. apply Pos_true.
    - apply bct4_boxR. apply Bracketable_pos. apply Pos_false.
        apply ept4_FalseL. apply H. apply Bracketable_pos. apply Pos_false.
    - apply bct4_boxR. apply Bracketable_pos. apply Pos_and.
        apply ept4_FalseL. apply H. apply Bracketable_pos. apply Pos_and.
    - apply bct4_AndNR. apply IHK1. apply H. apply IHK2. apply H.
    - apply bct4_boxR. apply Bracketable_pos. apply Pos_or.
        apply ept4_FalseL. apply H. apply Bracketable_pos. apply Pos_or.
    - apply bct4_ImpR. apply IHK2. apply in_cons. apply H.
Qed.

Lemma admissibility_AndPL_star :
  forall {C: sctx} {L0: lctx} {K: o},
    bct4 C L0 K ->
    forall (B1 B2 : o) {L1: lctx},
      Permutation L0 (B2 :: B1 :: L1) ->   (* permutation, not equation *)
      forall {L: lctx},
        Permutation L ((AndP B1 B2) :: L1) ->
        bct4 C L K.
Proof.
  intros C L0 K H. induction H ; intros.
  - apply bct4_boxR. apply H.
    eapply LJF4_exchange_linear_ept4.
    2: apply Permutation_sym ; apply H2.
    eapply ept4_AndPL. reflexivity. apply H.
    eapply LJF4_exchange_linear_ept4.
    2: apply H1.
    apply H0.
  - apply bct4_AndNR.
    + eapply LJF4_exchange_linear_bct4.
      2: apply Permutation_sym ; apply H2.
      eapply IHbct4_1.
      2: reflexivity.
      apply H1.
   + eapply LJF4_exchange_linear_bct4.
      2: apply Permutation_sym ; apply H2.
      eapply IHbct4_2.
      2: reflexivity.
      apply H1.
  - apply bct4_ImpR.
    assert (Permutation (B1 :: AndP B0 B3 :: L1) (B1 :: L0)).
    apply Permutation_sym. apply Permutation_cons. reflexivity. apply H1.
    eapply LJF4_exchange_linear_bct4.
    2: apply H2.
    eapply IHbct4 with (L1 := B1 :: L1) (B2 := B3) (B1 := B0).
      + eapply perm_trans.
        apply Permutation_cons. reflexivity. exact H0.
        eapply perm_trans.
        apply perm_swap.
        apply Permutation_cons. reflexivity.
        apply perm_swap.
      + apply perm_swap.
Qed.

Lemma admissibility_OrL_star :
  forall {C: sctx} {L1 L2: lctx} {K: o},
    bct4 C L1 K ->
    bct4 C L2 K ->
    forall (B1 B2 : o) {L0: lctx},
      Permutation L1 (B1 :: L0) ->  
      Permutation L2 (B2 :: L0) -> 
      forall {L: lctx},
        Permutation L ((Or B1 B2) :: L0) ->
        bct4 C L K.
Proof.
  intros C L1 L2 K H. revert L2. induction H ; intros.
  - apply bct4_boxR. apply H.
    eapply LJF4_exchange_linear_ept4.
    2: apply Permutation_sym ; apply H4.
    eapply ept4_OrL. reflexivity. apply H.
      + eapply LJF4_exchange_linear_ept4. 2: apply H2. apply H0.
      + inversion H1 ; subst.
        -- eapply LJF4_exchange_linear_ept4. apply H6. apply H3.
        -- inversion H. inversion H7. inversion H7.
        -- inversion H. inversion H6. inversion H6.
  - apply bct4_AndNR.
    + eapply IHbct4_1.
      2: apply H2.
      2: apply H3.
      2: apply H4.
      inversion H1 ; subst.
        -- inversion H5. inversion H7. inversion H7.
        -- apply H9.  
    + eapply LJF4_exchange_linear_bct4.
      eapply IHbct4_2.
      2: apply H2.
      2: apply H3.
      2: apply H4.
      2: reflexivity.
      inversion H1 ; subst.
        -- inversion H5. inversion H7. inversion H7.
        -- apply H10.
  - apply bct4_ImpR.
    assert (Permutation (B1 :: L1) (B1 :: Or B0 B3 :: L0)).
    apply Permutation_cons. reflexivity. apply H3.
    eapply LJF4_exchange_linear_bct4. 2: apply Permutation_sym ; apply H4.
    inversion H0. subst. inversion H5. inversion H7. inversion H7. subst.  
    eapply IHbct4.
    apply H8.
    3: apply perm_swap.
    apply Permutation_sym. rewrite perm_swap. apply Permutation_cons.
    reflexivity. apply Permutation_sym. apply H1.
    apply Permutation_sym. rewrite perm_swap. apply Permutation_cons.
    reflexivity. apply Permutation_sym. apply H2.
Qed.


Theorem LJF4_completeness : 
  (forall {C: sctx} {L: lctx} {K: o} {u: state}, ufcL C L K u -> 
    match u with 
    | Unbracketed => bct4 C L K
    | Bracketed => ept4 C L K
    end) /\
  (forall {C: sctx} {N K: o}, lfcL C N K -> lfc4 C N K) /\
  (forall {C: sctx} {K: o}, rfcL C K -> rfc4 C K).
Proof.
  apply LJF_mutind_all ; intros.
    - eapply ept4_Lf. apply i. apply b. apply n. apply H.
    - apply ept4_Rf. apply p. apply H.
    - eapply ept4_boxL. apply p. apply b. apply p0. apply H.
    - eapply admissibility_boxL_star. apply p0. apply H. apply p.
    - apply bct4_boxR. apply b. apply H.
    - eapply ept4_AndPL. apply p. apply b. apply H.
    - eapply admissibility_AndPL_star. apply H. reflexivity. apply p.
    - apply bct4_AndNR. apply H. apply H0.
    - eapply ept4_OrL. apply p. apply b. apply H. apply H0.
    - eapply admissibility_OrL_star. apply H. apply H0. reflexivity.
      reflexivity. apply p.
    - apply bct4_ImpR. apply H.
    - eapply ept4_TrueL. apply p. apply b. apply H.
    - eapply admissibility_TrueL_star. apply H. apply p.
    - apply ept4_FalseL. apply i. apply b.
    - apply admissibility_FalseL_star. apply i.
    - apply lfc4_Rl. apply b. apply p. apply H.
    - apply lfc4_Il. apply n. apply a.
    - apply lfc4_AndNL_1. apply b. apply H.
    - apply lfc4_AndNL_2. apply b. apply H.
    - apply lfc4_ImpL. apply b. apply H. apply H0.
    - apply rfc4_Rr. apply n. apply H.
    - apply rfc4_Ir. apply i. apply p. apply a.
    - apply rfc4_AndPR. apply H. apply H0.
    - apply rfc4_OrR_1. apply H.
    - apply rfc4_OrR_2. apply H.
    - apply rfc4_TrueR.
Qed.


      




