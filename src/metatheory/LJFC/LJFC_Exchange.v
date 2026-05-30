From Stdlib Require Import List Permutation.
From Stdlib Require Import Wellfounded Nat Arith Lia.

From LJF Require Import SharedLogic Measures LJFC_Rules Schemes.

Theorem LJFC_exchange_structural :
  (forall {C: ndctx} {L: octx} {K: o}, bctC C L K -> forall {C': ndctx}, Permutation C C' -> bctC C' L K) /\
  (forall {C: ndctx} {L: octx} {K: o}, eptC C L K -> forall {C': ndctx}, Permutation C C' -> eptC C' L K) /\
  (forall {C: ndctx} {N K: o}, lfcC C N K -> forall {C': ndctx}, Permutation C C' -> lfcC C' N K) /\
  (forall {C: ndctx} {P: o}, rfcC C P -> forall {C': ndctx}, Permutation C C' -> rfcC C' P). 
Proof.
    apply LJFC_mutind_all ; intros.
        - apply bctC_boxR. apply b. apply H. apply H0.
        - apply bctC_AndNR. apply H. apply H1. apply H0. apply H1.
        - apply bctC_ImpR. apply H. apply H0.
        - eapply eptC_Lf. eapply Permutation_in. apply H0. apply i. apply b. apply n. apply H. apply H0.
        - apply eptC_Rf. apply p. apply H. apply H0.
        - apply eptC_boxL. apply b. apply p. apply H.
          apply ndctx_insert_perm_cons. apply H0.
        - apply eptC_AndPL. apply b. apply H. apply H0.
        - apply eptC_OrL. apply b. apply H. apply H1. apply H0. apply H1.
        - apply eptC_TrueL. apply b. apply H. apply H0.
        - apply eptC_FalseL. apply b.
        - apply lfcC_Rl. apply b. apply p. apply H. apply H0.
        - apply lfcC_Il. apply n. apply a.
        - apply lfcC_AndNL_1. apply b. apply H. apply H0.
        - apply lfcC_AndNL_2. apply b. apply H. apply H0.
        - apply lfcC_ImpL. apply b. apply H. apply H1. apply H0. apply H1.
        - apply rfcC_Rr. apply n. apply H. apply H0.
        - apply rfcC_Ir. eapply Permutation_in. apply H. apply i. apply p. apply a.
        - apply rfcC_AndPR. apply H. apply H1. apply H0. apply H1.
        - apply rfcC_OrR_1. apply H. apply H0.
        - apply rfcC_OrR_2. apply H. apply H0.
        - apply rfcC_TrueR.
Qed.

Lemma LJFC_exchange_structural_bctC :
    forall {C: ndctx} {L: octx} {K: o}, bctC C L K -> forall {C': ndctx}, Permutation C C' -> bctC C' L K.
Proof.
  destruct LJFC_exchange_structural. apply H.
Qed.

Lemma LJFC_exchange_structural_eptC :
    forall {C: ndctx} {L: octx} {K: o}, eptC C L K -> forall {C': ndctx}, Permutation C C' -> eptC C' L K.
Proof.
  destruct LJFC_exchange_structural. destruct H0. apply H0.
Qed.

Lemma LJFC_exchange_structural_lfcC :
  forall {C: ndctx} {N K: o}, lfcC C N K -> forall {C': ndctx}, Permutation C C' -> lfcC C' N K.
Proof.
  destruct LJFC_exchange_structural. destruct H0. destruct H1. apply H1.
Qed.

Lemma LJFC_exchange_structural_rfcC :
  forall {C: ndctx} {K: o}, rfcC C K -> forall {C': ndctx}, Permutation C C' -> rfcC C' K.
Proof.
  destruct LJFC_exchange_structural. destruct H0. destruct H1. apply H2.
Qed.

Lemma eager_boxL :
  forall {C0: ndctx} {L: octx} {B: o} {K: o},
    bracketable K ->
    permeable B ->
    eptC C0 L K ->
    forall {C: ndctx} {L1 L2: octx},
      Permutation C0 (ndctx_insert B C) ->
      L = L1 ++ L2 ->
      eptC C (L1 ++ B :: L2) K.
Proof.
  intros C0 L B K b p H ; induction H ; intros.
    - symmetry in H4. apply app_eq_nil in H4. destruct H4. subst. simpl.
      apply eptC_boxL. apply b. apply p.
      eapply eptC_Lf. eapply Permutation_in.
        unfold ndctx_list in *.
        apply H3. apply H. apply b. apply H1.
      eapply LJFC_exchange_structural_lfcC. apply H2. apply H3.
    - symmetry in H2. apply app_eq_nil in H2. destruct H2. subst. simpl.
      apply eptC_boxL. apply b. apply p.
      apply eptC_Rf. apply H. 
      eapply LJFC_exchange_structural_rfcC. apply H0. apply H1.
    - symmetry in H3. apply app_eq_cons in H3. destruct H3. 
      + destruct H3. subst. simpl.
        apply eptC_boxL. apply b. apply p. 
        eapply LJFC_exchange_structural_eptC. 2: apply H2.
        apply eptC_boxL. apply H. apply H0. apply H1.
      + destruct H3. destruct H3. subst. simpl. 
        apply eptC_boxL. apply H. apply H0.
        apply IHeptC. apply H.
        apply Permutation_sym.
        apply ndctx_insert_perm_swap.
        apply ndctx_insert_perm_cons.
        apply Permutation_sym.
        apply H2.
        reflexivity.
    - symmetry in H2. apply app_eq_cons in H2. destruct H2 ; destruct H2.
      + subst. simpl. apply eptC_boxL. apply b. apply p.
        apply eptC_AndPL. apply b.
        eapply LJFC_exchange_structural_eptC. apply H0. apply H1.
      + destruct H2. subst. simpl.
        apply eptC_AndPL. apply H.
        eapply IHeptC with (L1 := B2 :: B1 :: x). apply b. apply H1. reflexivity.
    - symmetry in H3. apply app_eq_cons in H3. destruct H3 ; destruct H3.
      + subst. simpl.
        apply eptC_boxL. apply b. apply p.
        apply eptC_OrL. apply b.
          -- eapply LJFC_exchange_structural_eptC. apply H0. apply H2.
          -- eapply LJFC_exchange_structural_eptC. apply H1. apply H2.
      + destruct H3. subst. simpl. 
        apply eptC_OrL. apply b.
          -- eapply IHeptC1 with (L1 := B1 :: x). apply b. apply H2. reflexivity.
          -- eapply IHeptC2 with (L1 := B2 :: x). apply b. apply H2. reflexivity.
    - symmetry in H2. apply app_eq_cons in H2. destruct H2 ; destruct H2.
      + subst. simpl. apply eptC_boxL. apply b. apply p.
        apply eptC_TrueL. apply b.
        eapply LJFC_exchange_structural_eptC. apply H0. apply H1.
      + destruct H2. subst. simpl.
        apply eptC_TrueL. apply H.
        eapply IHeptC with (L1 := x). apply b. apply H1. reflexivity.
    - symmetry in H1. apply app_eq_cons in H1. destruct H1 ; destruct H1.
      + subst. simpl. apply eptC_boxL. apply b. apply p.
        apply eptC_FalseL. apply b.
      + destruct H1. subst. simpl.
        apply eptC_FalseL. apply H.
Qed.        
        
Lemma eager_AndPL :
  forall {C: ndctx} {L: octx} {B1 B2 K: o},
    bracketable K ->
    eptC C L K ->
      forall {L1 L2: octx},
      L = L1 ++ B2 :: B1 :: L2 ->
      eptC C (L1 ++ (AndP B1 B2) :: L2) K.
Proof.
  intros C L B1 B2 K b H. induction H ; intros L1 L2 Ho.
    - symmetry in Ho. apply app_eq_nil in Ho. destruct Ho. discriminate H4.
    - symmetry in Ho. apply app_eq_nil in Ho. destruct Ho. discriminate H2.
    - symmetry in Ho. apply app_eq_cons in Ho. destruct Ho.
      + destruct H2. inversion H3. subst. clear H3. simpl.
        apply eptC_AndPL. apply H.
        apply eptC_boxL. apply H. apply H0. apply H1. 
      + destruct H2. destruct H2. subst. simpl.
        apply eptC_boxL. apply H. apply H0. 
        apply IHeptC. apply H. reflexivity.
    - symmetry in Ho. apply app_eq_cons in Ho. destruct Ho.
      + destruct H1. inversion H2. subst. simpl.
        apply eptC_AndPL. apply H. 
        apply eptC_AndPL. apply H. apply H0. 
      + destruct H1. destruct H1. subst. simpl.
        apply eptC_AndPL. apply H.
        apply IHeptC with (L1 := B3 :: B0 :: x). apply b. reflexivity.
    - symmetry in Ho. apply app_eq_cons in Ho. destruct Ho.
      + destruct H2. inversion H3. subst. simpl. clear H3.
        apply eptC_AndPL. apply H. 
        apply eptC_OrL. apply H. apply H0. apply H1.
      + destruct H2. destruct H2. subst. simpl.
        apply eptC_OrL. apply H.
        -- apply IHeptC1 with (L1 := (B0 :: x)). apply H. reflexivity.
        -- apply IHeptC2 with (L1 := (B3 :: x)). apply H. reflexivity.
    - symmetry in Ho. apply app_eq_cons in Ho. destruct Ho.
      + destruct H1. inversion H2. subst. simpl.
        apply eptC_AndPL. apply H.
        apply eptC_TrueL. apply H.
        apply H0.
      + destruct H1. destruct H1. subst. simpl.
        apply eptC_TrueL. apply H. 
        apply IHeptC. apply H. reflexivity.
    - symmetry in Ho. apply app_eq_cons in Ho. destruct Ho.
      + destruct H0. inversion H1. subst. simpl. 
        apply eptC_AndPL. apply H. apply eptC_FalseL. apply H.
      + destruct H0. destruct H0. subst. simpl.
        apply eptC_FalseL. apply H.
Qed.

Lemma LJFC_inversion_boxL :
  forall {C: ndctx} {L: octx} {B K: o},
    bracketable K ->
    permeable B ->
    eptC C L K ->
    forall {L1: octx},
      L = B :: L1 ->  
      eptC (ndctx_insert B C) L1 K.
Proof.
  intros C L B K b p H. induction H ; intros L1 Ho.
    - discriminate Ho.
    - discriminate Ho.
    - inversion Ho. subst. apply H1.
    - inversion Ho. subst. inversion p. inversion H1. inversion H1.
    - inversion Ho. subst. inversion p. inversion H2. inversion H2.
    - inversion Ho. subst. inversion p. inversion H1. inversion H1.
    - inversion Ho. subst. inversion p. inversion H0. inversion H0.
Qed.

Lemma eager_OrL :
  forall {C: ndctx} {L: octx} {B1 B2 K: o},
    bracketable K ->
    eptC C L K ->
    forall {L' : octx},
      eptC C L' K ->
      forall {L1 L2: octx},
        L = L1 ++ B1 :: L2 ->
        L' = L1 ++ B2 :: L2 ->
        eptC C (L1 ++ (Or B1 B2) :: L2) K.
Proof.
  intros C L B1 B2 K b H. induction H ; intros L' H' L1 L2 Ho Ho'.
    - subst. symmetry in Ho. apply app_eq_nil in Ho. destruct Ho.
      inversion H4.
    - subst. symmetry in Ho. apply app_eq_nil in Ho. destruct Ho.
      inversion H2.
    - subst. symmetry in Ho. apply app_eq_cons in Ho. destruct Ho.
      + destruct H2. inversion H3. subst. simpl. 
        apply eptC_OrL. apply H.
          -- apply eptC_boxL. apply H. apply H0. apply H1.
          -- apply H'.
      + destruct H2. destruct H2. subst. simpl.
        apply eptC_boxL. apply H. apply H0.
        simpl in H'.
        eapply IHeptC with (L' := x ++ B2 :: L2). apply H.
        eapply LJFC_inversion_boxL. apply H. apply H0.
        apply H'. reflexivity. reflexivity. reflexivity.
    - symmetry in Ho. apply app_eq_cons in Ho. destruct Ho.
      + destruct H1. inversion H2. subst. simpl. 
        apply eptC_OrL. apply H. apply eptC_AndPL. apply H. apply H0. apply H'.
      + destruct H1. destruct H1. subst.
        simpl. apply eptC_AndPL. apply H.
        eapply IHeptC with (L1 := B3 :: B0 :: x). apply H.
        inversion H'. subst. inversion H5. inversion H1. inversion H1. subst.
        apply H7. reflexivity. reflexivity.
    - subst. symmetry in Ho. apply app_eq_cons in Ho. destruct Ho.
      + destruct H2. inversion H3. subst. simpl.
        apply eptC_OrL. apply H. apply eptC_OrL. apply H.
        apply H0. apply H1. apply H'.
      + destruct H2. destruct H2. subst. simpl.
        apply eptC_OrL. apply H. 
        inversion H'. subst. inversion H6. inversion H2. inversion H2. subst.
        eapply IHeptC1 with (L1 := B0 :: x). apply H. apply H8. reflexivity. reflexivity.
        inversion H'. subst. inversion H6. inversion H2. inversion H2. subst.
        eapply IHeptC2 with (L1 := B3 :: x). apply H. apply H9. reflexivity. reflexivity.
    - symmetry in Ho. apply app_eq_cons in Ho. destruct Ho.
      + destruct H1. inversion H2. subst. simpl.
        apply eptC_OrL. apply H.
        apply eptC_TrueL. apply H. apply H0.
        apply H'.
      + destruct H1. destruct H1. subst. simpl.
        apply eptC_TrueL. apply H.
        eapply IHeptC. apply H.
        inversion H'. subst. inversion H5. inversion H1. inversion H1.
        subst. apply H4. reflexivity. reflexivity.
    - symmetry in Ho. apply app_eq_cons in Ho. destruct Ho.
      + destruct H0. inversion H1. subst. simpl.
        apply eptC_OrL. apply H. apply eptC_FalseL. apply H. apply H'.
      + destruct H0. destruct H0. subst. simpl. apply eptC_FalseL. apply H.
Qed. 

Lemma eager_TrueL :
  forall {C: ndctx} {L: octx} {K: o},
    bracketable K ->
    eptC C L K ->
    forall {L1 L2: octx},
      L = L1 ++ L2 ->
      eptC C (L1 ++ TT :: L2) K.
Proof.
  intros C L K b H. induction H ; intros L1 L2 Ho.
    - symmetry in Ho. apply app_eq_nil in Ho. destruct Ho. subst. simpl.
      apply eptC_TrueL. apply b. eapply eptC_Lf. apply H. apply H0.
      apply H1. apply H2.
    - symmetry in Ho. apply app_eq_nil in Ho. destruct Ho. subst. simpl.
      apply eptC_TrueL. apply b. apply eptC_Rf. apply H. apply H0.
    - destruct L1.
      + simpl in Ho. subst. simpl. apply eptC_TrueL. apply H.
        apply eptC_boxL. apply H. apply H0. apply H1.
      + simpl in Ho. inversion Ho. subst. simpl.
        apply eptC_boxL. apply H. apply H0.
        apply IHeptC. apply H. reflexivity.
    - destruct L1.
      + simpl in Ho. subst. simpl. apply eptC_TrueL. apply H.
        apply eptC_AndPL. apply H. apply H0.
      + simpl in Ho. inversion Ho. subst. simpl.
        apply eptC_AndPL. apply H.
        eapply IHeptC with (L1 := B2 :: B1 :: L1) (L2 := L2). apply H. reflexivity.
    - destruct L1.
      + simpl in Ho. subst. simpl. apply eptC_TrueL. apply H.
        apply eptC_OrL. apply H. apply H0. apply H1.
      + simpl in Ho. inversion Ho. subst. simpl.
        apply eptC_OrL. apply H.
        -- eapply IHeptC1 with (L1 := B1 :: L1). apply H. reflexivity.
        -- eapply IHeptC2 with (L1 := B2 :: L1). apply H. reflexivity.
    - destruct L1.
      + simpl in Ho. subst. simpl. apply eptC_TrueL. apply H.
        apply eptC_TrueL. apply H. apply H0.
      + simpl in Ho. inversion Ho. subst. simpl.
        apply eptC_TrueL. apply H. apply IHeptC. apply H. reflexivity.
    - destruct L1.
      + simpl in Ho. subst. simpl. apply eptC_TrueL. apply H.
        apply eptC_FalseL. apply H.
      + simpl in Ho. inversion Ho. subst. simpl.
        apply eptC_FalseL. apply H.
Qed.

Lemma eager_FalseL : 
  forall {C: ndctx} {L: octx} {K: o},
    bracketable K ->
    In FF L ->
    eptC C L K.
Proof.
  intros C L K b. revert C.
  induction L using (well_founded_ind (wf_inverse_image octx nat lt octx_size PeanoNat.Nat.lt_wf_0)).
  destruct L ; intros C I. inversion I. destruct o.
    + apply eptC_boxL. apply b. destruct p. 
      apply Permeable_pos_atom. apply Is_atom. apply Pos_atom.
      apply Permeable_neg. apply Neg_atom. apply H.
      cbn [octx_size]. inversion I. discriminate H0.
      apply Nat.lt_add_pos_l. cbn [osize]. apply Nat.lt_0_1.
      inversion I. discriminate H0. apply H0.
    + apply eptC_TrueL. apply b. apply H.
      cbn [octx_size]. inversion I. discriminate H0. 
      apply Nat.lt_add_pos_l. cbn [osize]. apply Nat.lt_0_1.
      inversion I. discriminate H0. apply H0.
    + apply eptC_FalseL. apply b.
    + apply eptC_AndPL. apply b. apply H.
      cbn [octx_size]. cbn [osize].
      simpl. rewrite Nat.add_shuffle3. rewrite Nat.add_assoc. apply Nat.lt_succ_diag_r.
      inversion I. discriminate H0. apply in_cons. apply in_cons. apply H0.
    + apply eptC_boxL. apply b. apply Permeable_neg. apply Neg_and.
      apply H. cbn [octx_size]. apply Nat.lt_add_pos_l. 
      cbn [osize]. apply Nat.lt_lt_add_r. apply Nat.lt_lt_add_r. apply Nat.lt_0_1.
      inversion I. discriminate H0. apply H0.
    + apply eptC_OrL. apply b.
      -- apply H. cbn [octx_size]. cbn [osize]. simpl.
        apply Nat.lt_succ_r.
        apply add_le_mono_r_proj_l2r. apply Nat.le_add_r.
        inversion I. discriminate H0. apply in_cons. apply H0.
      -- apply H. cbn [octx_size]. cbn [osize]. simpl.
        apply Nat.lt_succ_r.
        apply add_le_mono_r_proj_l2r. apply Nat.le_add_l.
        inversion I. discriminate H0. apply in_cons. apply H0.
    + apply eptC_boxL. apply b. apply Permeable_neg. apply Neg_imp.
      apply H. cbn [octx_size]. apply Nat.lt_add_pos_l. 
      cbn [osize]. apply Nat.lt_lt_add_r. apply Nat.lt_lt_add_r. apply Nat.lt_0_1.
      inversion I. discriminate H0. apply H0.
Qed.


Theorem LJFC_exchange_ordered :
  (forall {C: ndctx} {L: octx} {K: o}, bctC C L K -> forall {L': octx}, Permutation L L' -> bctC C L' K) /\
  (forall {C: ndctx} {L: octx} {K: o}, eptC C L K -> forall {L': octx}, Permutation L L' -> eptC C L' K).
Proof.
    apply LJFC_mutind_async ; intros.
      - apply bctC_boxR. apply b. apply H. apply H0.
      - apply bctC_AndNR. apply H. apply H1. apply H0. apply H1.
      - apply bctC_ImpR. apply H. apply Permutation_cons. reflexivity. apply H0.
      - apply Permutation_nil in H. subst. eapply eptC_Lf. apply i. apply b. apply n. apply l.
      - apply Permutation_nil in H. subst. apply eptC_Rf. apply p. apply r.
      - pose proof H0.
        symmetry in H1. apply Permutation_vs_cons_inv in H1. destruct H1. destruct H1. subst.
        eapply eager_boxL. apply b. apply p. 3: reflexivity. 2: apply Permutation_refl.
        apply H. eapply Permutation_cons_app_inv. apply H0.
      - pose proof H0.
        symmetry in H1. apply Permutation_vs_cons_inv in H1. destruct H1. destruct H1. subst.
        eapply eager_AndPL. apply b. 2: reflexivity.
        apply H. apply Permutation_cons_app. apply Permutation_cons_app. eapply Permutation_cons_app_inv. apply H0.
      - pose proof H1.
        symmetry in H1. apply Permutation_vs_cons_inv in H1. destruct H1. destruct H1. subst.
        eapply eager_OrL. apply b. 4: reflexivity. 3:reflexivity.
          + apply H. apply Permutation_cons_app. eapply Permutation_cons_app_inv. apply H2.
          + apply H0. apply Permutation_cons_app. eapply Permutation_cons_app_inv. apply H2.
      - pose proof H0.
        symmetry in H1. apply Permutation_vs_cons_inv in H1. destruct H1. destruct H1. subst.
        eapply eager_TrueL. apply b. 2: reflexivity.
        apply H. eapply Permutation_cons_app_inv. apply H0. 
      - apply eager_FalseL. apply b. apply Permutation_in with (x:= FF) in H.
        apply H. apply in_eq.
Qed.

Lemma LJFC_exchange_ordered_bctC :
  forall {C: ndctx} {L: octx} {K: o}, bctC C L K -> forall {L': octx}, Permutation L L' -> bctC C L' K.
Proof.
  destruct LJFC_exchange_ordered. apply H.
Qed.

Lemma LJFC_exchange_ordered_eptC :
  forall {C: ndctx} {L: octx} {K: o}, eptC C L K -> forall {L': octx}, Permutation L L' -> eptC C L' K.
Proof.
  destruct LJFC_exchange_ordered. apply H0.
Qed.