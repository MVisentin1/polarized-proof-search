From Equations Require Import Equations.
From Stdlib Require Import List Permutation.
From Stdlib Require Import Wellfounded Nat Arith Lia.

From LJF Require Import SharedLogic Measures LJFPS_Rules.

Scheme bct_mut := Induction for bct Sort Prop
  with ept_mut := Induction for ept Sort Prop
  with lfc_mut := Induction for lfc Sort Prop
  with rfc_mut := Induction for rfc Sort Prop.

Combined Scheme LJFPS_mutind_all from bct_mut, ept_mut, lfc_mut, rfc_mut.

Theorem LJFPS_exchange_structural :
  (forall {C: sctx} {L: octx} {K: o}, bct C L K -> forall {C': sctx}, Permutation C C' -> bct C' L K) /\
  (forall {C: sctx} {L: octx} {K: o}, ept C L K -> forall {C': sctx}, Permutation C C' -> ept C' L K) /\
  (forall {C: sctx} {N K: o}, lfc C N K -> forall {C': sctx}, Permutation C C' -> lfc C' N K) /\
  (forall {C: sctx} {P: o}, rfc C P -> forall {C': sctx}, Permutation C C' -> rfc C' P). 
Proof.
    apply LJFPS_mutind_all ; intros.
        - apply bct_boxR. apply b. apply H. apply H0.
        - apply bct_AndNR. apply H. apply H1. apply H0. apply H1.
        - apply bct_ImpR. apply H. apply H0.
        - eapply ept_Lf. eapply Permutation_in. apply H0. apply i. apply b. apply n. apply H. apply H0.
        - apply ept_Rf. apply p. apply H. apply H0.
        - apply ept_boxL. apply b. apply p. apply H. apply Permutation_cons. reflexivity. apply H0.
        - apply ept_AndPL. apply b. apply H. apply H0.
        - apply ept_OrL. apply b. apply H. apply H1. apply H0. apply H1.
        - apply ept_TrueL. apply b. apply H. apply H0.
        - apply ept_FalseL. apply b.
        - apply lfc_Rl. apply b. apply p. apply H. apply H0.
        - apply lfc_Il. apply n. apply a.
        - apply lfc_AndNL_1. apply b. apply H. apply H0.
        - apply lfc_AndNL_2. apply b. apply H. apply H0.
        - apply lfc_ImpL. apply b. apply H. apply H1. apply H0. apply H1.
        - apply rfc_Rr. apply n. apply H. apply H0.
        - apply rfc_Ir. eapply Permutation_in. apply H. apply i. apply p. apply a.
        - apply rfc_AndPR. apply H. apply H1. apply H0. apply H1.
        - apply rfc_OrR_1. apply H. apply H0.
        - apply rfc_OrR_2. apply H. apply H0.
        - apply rfc_TrueR.
Qed.

Lemma LJFPS_exchange_structural_bct :
    forall {C: sctx} {L: octx} {K: o}, bct C L K -> forall {C': sctx}, Permutation C C' -> bct C' L K.
Proof.
  destruct LJFPS_exchange_structural. apply H.
Qed.

Lemma LJFPS_exchange_structural_ept :
    forall {C: sctx} {L: octx} {K: o}, ept C L K -> forall {C': sctx}, Permutation C C' -> ept C' L K.
Proof.
  destruct LJFPS_exchange_structural. destruct H0. apply H0.
Qed.

Lemma LJFPS_exchange_structural_lfc :
  forall {C: sctx} {N K: o}, lfc C N K -> forall {C': sctx}, Permutation C C' -> lfc C' N K.
Proof.
  destruct LJFPS_exchange_structural. destruct H0. destruct H1. apply H1.
Qed.

Lemma LJFPS_exchange_structural_rfc :
  forall {C: sctx} {K: o}, rfc C K -> forall {C': sctx}, Permutation C C' -> rfc C' K.
Proof.
  destruct LJFPS_exchange_structural. destruct H0. destruct H1. apply H2.
Qed.

Lemma eager_boxL :
  forall {C0: sctx} {L: octx} {B: o} {K: o},
    bracketable K ->
    permeable B ->
    ept C0 L K ->
    forall {C: sctx} {L1 L2: octx},
      Permutation C0 (B :: C) ->
      L = L1 ++ L2 ->
      ept C (L1 ++ B :: L2) K.
Proof.
  intros C0 L B K b p H ; induction H ; intros.
    - symmetry in H4. apply app_eq_nil in H4. destruct H4. subst. simpl.
      apply ept_boxL. apply b. apply p.
      eapply ept_Lf. eapply Permutation_in. apply H3. apply H. apply b. apply H1.
      eapply LJFPS_exchange_structural_lfc. apply H2. apply H3.
    - symmetry in H2. apply app_eq_nil in H2. destruct H2. subst. simpl.
      apply ept_boxL. apply b. apply p.
      apply ept_Rf. apply H. 
      eapply LJFPS_exchange_structural_rfc. apply H0. apply H1.
    - symmetry in H3. apply app_eq_cons in H3. destruct H3. 
      + destruct H3. subst. simpl.
        apply ept_boxL. apply b. apply p. 
        eapply LJFPS_exchange_structural_ept. 2: apply H2.
        apply ept_boxL. apply H. apply H0. apply H1.
      + destruct H3. destruct H3. subst. simpl. 
        apply ept_boxL. apply H. apply H0.
        apply IHept. apply H.
        assert (Permutation (B :: B0 :: C0) (B0 :: B :: C0)). apply perm_swap.
        apply Permutation_sym in H3. eapply perm_trans.
          -- apply perm_skip with (x := B0)  in H2. apply H2.
          -- apply H3.
          -- reflexivity.
    - symmetry in H2. apply app_eq_cons in H2. destruct H2 ; destruct H2.
      + subst. simpl. apply ept_boxL. apply b. apply p.
        apply ept_AndPL. apply b.
        eapply LJFPS_exchange_structural_ept. apply H0. apply H1.
      + destruct H2. subst. simpl.
        apply ept_AndPL. apply H.
        eapply IHept with (L1 := B2 :: B1 :: x). apply b. apply H1. reflexivity.
    - symmetry in H3. apply app_eq_cons in H3. destruct H3 ; destruct H3.
      + subst. simpl.
        apply ept_boxL. apply b. apply p.
        apply ept_OrL. apply b.
          -- eapply LJFPS_exchange_structural_ept. apply H0. apply H2.
          -- eapply LJFPS_exchange_structural_ept. apply H1. apply H2.
      + destruct H3. subst. simpl. 
        apply ept_OrL. apply b.
          -- eapply IHept1 with (L1 := B1 :: x). apply b. apply H2. reflexivity.
          -- eapply IHept2 with (L1 := B2 :: x). apply b. apply H2. reflexivity.
    - symmetry in H2. apply app_eq_cons in H2. destruct H2 ; destruct H2.
      + subst. simpl. apply ept_boxL. apply b. apply p.
        apply ept_TrueL. apply b.
        eapply LJFPS_exchange_structural_ept. apply H0. apply H1.
      + destruct H2. subst. simpl.
        apply ept_TrueL. apply H.
        eapply IHept with (L1 := x). apply b. apply H1. reflexivity.
    - symmetry in H1. apply app_eq_cons in H1. destruct H1 ; destruct H1.
      + subst. simpl. apply ept_boxL. apply b. apply p.
        apply ept_FalseL. apply b.
      + destruct H1. subst. simpl.
        apply ept_FalseL. apply H.
Qed.        
        
Lemma eager_AndPL :
  forall {C: sctx} {L: octx} {B1 B2 K: o},
    bracketable K ->
    ept C L K ->
      forall {L1 L2: octx},
      L = L1 ++ B2 :: B1 :: L2 ->
      ept C (L1 ++ (AndP B1 B2) :: L2) K.
Proof.
  intros C L B1 B2 K b H. induction H ; intros L1 L2 Ho.
    - symmetry in Ho. apply app_eq_nil in Ho. destruct Ho. discriminate H4.
    - symmetry in Ho. apply app_eq_nil in Ho. destruct Ho. discriminate H2.
    - symmetry in Ho. apply app_eq_cons in Ho. destruct Ho.
      + destruct H2. inversion H3. subst. clear H3. simpl.
        apply ept_AndPL. apply H.
        apply ept_boxL. apply H. apply H0. apply H1. 
      + destruct H2. destruct H2. subst. simpl.
        apply ept_boxL. apply H. apply H0. 
        apply IHept. apply H. reflexivity.
    - symmetry in Ho. apply app_eq_cons in Ho. destruct Ho.
      + destruct H1. inversion H2. subst. simpl.
        apply ept_AndPL. apply H. 
        apply ept_AndPL. apply H. apply H0. 
      + destruct H1. destruct H1. subst. simpl.
        apply ept_AndPL. apply H.
        apply IHept with (L1 := B3 :: B0 :: x). apply b. reflexivity.
    - symmetry in Ho. apply app_eq_cons in Ho. destruct Ho.
      + destruct H2. inversion H3. subst. simpl. clear H3.
        apply ept_AndPL. apply H. 
        apply ept_OrL. apply H. apply H0. apply H1.
      + destruct H2. destruct H2. subst. simpl.
        apply ept_OrL. apply H.
        -- apply IHept1 with (L1 := (B0 :: x)). apply H. reflexivity.
        -- apply IHept2 with (L1 := (B3 :: x)). apply H. reflexivity.
    - symmetry in Ho. apply app_eq_cons in Ho. destruct Ho.
      + destruct H1. inversion H2. subst. simpl.
        apply ept_AndPL. apply H.
        apply ept_TrueL. apply H.
        apply H0.
      + destruct H1. destruct H1. subst. simpl.
        apply ept_TrueL. apply H. 
        apply IHept. apply H. reflexivity.
    - symmetry in Ho. apply app_eq_cons in Ho. destruct Ho.
      + destruct H0. inversion H1. subst. simpl. 
        apply ept_AndPL. apply H. apply ept_FalseL. apply H.
      + destruct H0. destruct H0. subst. simpl.
        apply ept_FalseL. apply H.
Qed.

Lemma LJFPS_inversion_boxL :
  forall {C: sctx} {L: octx} {B K: o},
    bracketable K ->
    permeable B ->
    ept C L K ->
    forall {L1: octx},
      L = B :: L1 ->  
      ept (B :: C) L1 K.
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
  forall {C: sctx} {L: octx} {B1 B2 K: o},
    bracketable K ->
    ept C L K ->
    forall {L' : octx},
      ept C L' K ->
      forall {L1 L2: octx},
        L = L1 ++ B1 :: L2 ->
        L' = L1 ++ B2 :: L2 ->
        ept C (L1 ++ (Or B1 B2) :: L2) K.
Proof.
  intros C L B1 B2 K b H. induction H ; intros L' H' L1 L2 Ho Ho'.
    - subst. symmetry in Ho. apply app_eq_nil in Ho. destruct Ho.
      inversion H4.
    - subst. symmetry in Ho. apply app_eq_nil in Ho. destruct Ho.
      inversion H2.
    - subst. symmetry in Ho. apply app_eq_cons in Ho. destruct Ho.
      + destruct H2. inversion H3. subst. simpl. 
        apply ept_OrL. apply H.
          -- apply ept_boxL. apply H. apply H0. apply H1.
          -- apply H'.
      + destruct H2. destruct H2. subst. simpl.
        apply ept_boxL. apply H. apply H0.
        simpl in H'.
        eapply IHept with (L' := x ++ B2 :: L2). apply H.
        eapply LJFPS_inversion_boxL. apply H. apply H0.
        apply H'. reflexivity. reflexivity. reflexivity.
    - symmetry in Ho. apply app_eq_cons in Ho. destruct Ho.
      + destruct H1. inversion H2. subst. simpl. 
        apply ept_OrL. apply H. apply ept_AndPL. apply H. apply H0. apply H'.
      + destruct H1. destruct H1. subst.
        simpl. apply ept_AndPL. apply H.
        eapply IHept with (L1 := B3 :: B0 :: x). apply H.
        inversion H'. subst. inversion H5. inversion H1. inversion H1. subst.
        apply H7. reflexivity. reflexivity.
    - subst. symmetry in Ho. apply app_eq_cons in Ho. destruct Ho.
      + destruct H2. inversion H3. subst. simpl.
        apply ept_OrL. apply H. apply ept_OrL. apply H.
        apply H0. apply H1. apply H'.
      + destruct H2. destruct H2. subst. simpl.
        apply ept_OrL. apply H. 
        inversion H'. subst. inversion H6. inversion H2. inversion H2. subst.
        eapply IHept1 with (L1 := B0 :: x). apply H. apply H8. reflexivity. reflexivity.
        inversion H'. subst. inversion H6. inversion H2. inversion H2. subst.
        eapply IHept2 with (L1 := B3 :: x). apply H. apply H9. reflexivity. reflexivity.
    - symmetry in Ho. apply app_eq_cons in Ho. destruct Ho.
      + destruct H1. inversion H2. subst. simpl.
        apply ept_OrL. apply H.
        apply ept_TrueL. apply H. apply H0.
        apply H'.
      + destruct H1. destruct H1. subst. simpl.
        apply ept_TrueL. apply H.
        eapply IHept. apply H.
        inversion H'. subst. inversion H5. inversion H1. inversion H1.
        subst. apply H4. reflexivity. reflexivity.
    - symmetry in Ho. apply app_eq_cons in Ho. destruct Ho.
      + destruct H0. inversion H1. subst. simpl.
        apply ept_OrL. apply H. apply ept_FalseL. apply H. apply H'.
      + destruct H0. destruct H0. subst. simpl. apply ept_FalseL. apply H.
Qed. 

Lemma eager_TrueL :
  forall {C: sctx} {L: octx} {K: o},
    bracketable K ->
    ept C L K ->
    forall {L1 L2: octx},
      L = L1 ++ L2 ->
      ept C (L1 ++ TT :: L2) K.
Proof.
  intros C L K b H. induction H ; intros L1 L2 Ho.
    - symmetry in Ho. apply app_eq_nil in Ho. destruct Ho. subst. simpl.
      apply ept_TrueL. apply b. eapply ept_Lf. apply H. apply H0.
      apply H1. apply H2.
    - symmetry in Ho. apply app_eq_nil in Ho. destruct Ho. subst. simpl.
      apply ept_TrueL. apply b. apply ept_Rf. apply H. apply H0.
    - destruct L1.
      + simpl in Ho. subst. simpl. apply ept_TrueL. apply H.
        apply ept_boxL. apply H. apply H0. apply H1.
      + simpl in Ho. inversion Ho. subst. simpl.
        apply ept_boxL. apply H. apply H0.
        apply IHept. apply H. reflexivity.
    - destruct L1.
      + simpl in Ho. subst. simpl. apply ept_TrueL. apply H.
        apply ept_AndPL. apply H. apply H0.
      + simpl in Ho. inversion Ho. subst. simpl.
        apply ept_AndPL. apply H.
        eapply IHept with (L1 := B2 :: B1 :: L1) (L2 := L2). apply H. reflexivity.
    - destruct L1.
      + simpl in Ho. subst. simpl. apply ept_TrueL. apply H.
        apply ept_OrL. apply H. apply H0. apply H1.
      + simpl in Ho. inversion Ho. subst. simpl.
        apply ept_OrL. apply H.
        -- eapply IHept1 with (L1 := B1 :: L1). apply H. reflexivity.
        -- eapply IHept2 with (L1 := B2 :: L1). apply H. reflexivity.
    - destruct L1.
      + simpl in Ho. subst. simpl. apply ept_TrueL. apply H.
        apply ept_TrueL. apply H. apply H0.
      + simpl in Ho. inversion Ho. subst. simpl.
        apply ept_TrueL. apply H. apply IHept. apply H. reflexivity.
    - destruct L1.
      + simpl in Ho. subst. simpl. apply ept_TrueL. apply H.
        apply ept_FalseL. apply H.
      + simpl in Ho. inversion Ho. subst. simpl.
        apply ept_FalseL. apply H.
Qed.

Lemma eager_FalseL : 
  forall {C: sctx} {L: octx} {K: o},
    bracketable K ->
    In FF L ->
    ept C L K.
Proof.
  intros C L K b. revert C.
  induction L using (well_founded_ind (wf_inverse_image octx nat lt octx_size PeanoNat.Nat.lt_wf_0)).
  destruct L ; intros C I. inversion I. destruct o.
    + apply ept_boxL. apply b. destruct p. 
      apply Permeable_pos_atom. apply Is_atom. apply Pos_atom.
      apply Permeable_neg. apply Neg_atom. apply H.
      simp octx_size. inversion I. discriminate H0. apply H0.
    + apply ept_TrueL. apply b. apply H.
      simp octx_size. inversion I. discriminate H0. apply H0.
    + apply ept_FalseL. apply b.
    + apply ept_AndPL. apply b. apply H.
      simp octx_size. simp osize.
      simpl. rewrite Nat.add_shuffle3. rewrite Nat.add_assoc. apply Nat.lt_succ_diag_r.
      inversion I. discriminate H0. apply in_cons. apply in_cons. apply H0.
    + apply ept_boxL. apply b. apply Permeable_neg. apply Neg_and.
      apply H. simp octx_size. apply Nat.lt_add_pos_l. 
      simp osize. apply Nat.lt_lt_add_r. apply Nat.lt_lt_add_r. apply Nat.lt_0_1.
      inversion I. discriminate H0. apply H0.
    + apply ept_OrL. apply b.
      -- apply H. simp octx_size. simp osize. simpl.
        apply Nat.lt_succ_r.
        apply add_le_mono_r_proj_l2r. apply Nat.le_add_r.
        inversion I. discriminate H0. apply in_cons. apply H0.
      -- apply H. simp octx_size. simp osize. simpl.
        apply Nat.lt_succ_r.
        apply add_le_mono_r_proj_l2r. apply Nat.le_add_l.
        inversion I. discriminate H0. apply in_cons. apply H0.
    + apply ept_boxL. apply b. apply Permeable_neg. apply Neg_imp.
      apply H. simp octx_size. apply Nat.lt_add_pos_l. 
      simp osize. apply Nat.lt_lt_add_r. apply Nat.lt_lt_add_r. apply Nat.lt_0_1.
      inversion I. discriminate H0. apply H0.
Qed.

Scheme bct_mut_async := Induction for bct Sort Prop
  with ept_mut_async := Induction for ept Sort Prop.
Combined Scheme LJFPS_mutind_async from bct_mut_async, ept_mut_async.

Theorem LJFPS_exchange_ordered :
  (forall {C: sctx} {L: octx} {K: o}, bct C L K -> forall {L': octx}, Permutation L L' -> bct C L' K) /\
  (forall {C: sctx} {L: octx} {K: o}, ept C L K -> forall {L': octx}, Permutation L L' -> ept C L' K).
Proof.
    apply LJFPS_mutind_async ; intros.
      - apply bct_boxR. apply b. apply H. apply H0.
      - apply bct_AndNR. apply H. apply H1. apply H0. apply H1.
      - apply bct_ImpR. apply H. apply Permutation_cons. reflexivity. apply H0.
      - apply Permutation_nil in H. subst. eapply ept_Lf. apply i. apply b. apply n. apply l.
      - apply Permutation_nil in H. subst. apply ept_Rf. apply p. apply r.
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

Lemma LJFPS_exchange_ordered_bct :
  forall {C: sctx} {L: octx} {K: o}, bct C L K -> forall {L': octx}, Permutation L L' -> bct C L' K.
Proof.
  destruct LJFPS_exchange_ordered. apply H.
Qed.

Lemma LJFPS_exchange_ordered_ept :
  forall {C: sctx} {L: octx} {K: o}, ept C L K -> forall {L': octx}, Permutation L L' -> ept C L' K.
Proof.
  destruct LJFPS_exchange_ordered. apply H0.
Qed.

