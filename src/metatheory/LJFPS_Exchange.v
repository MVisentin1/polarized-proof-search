From Equations Require Import Equations.
From Stdlib Require Import List.
From CARVe Require Import contexts.list.
From CARVe Require Import algebras.structural.
From LJF Require Import SharedLogic LJFPS_Rules.
From Stdlib Require Import Permutation.


Scheme bct_mut := Induction for bct Sort Prop
  with ept_mut := Induction for ept Sort Prop
  with lfc_mut := Induction for lfc Sort Prop
  with rfc_mut := Induction for rfc Sort Prop.

Combined Scheme LJFPS_mutind_all from bct_mut, ept_mut, lfc_mut, rfc_mut.

Theorem LJFPS_exchange_structural_perm :
  (forall {C: sctx} {D: octx} {K: o}, bct C D K -> forall {C': sctx}, Permutation C C' -> bct C' D K) /\
  (forall {C: sctx} {D: octx} {K: o}, ept C D K -> forall {C': sctx}, Permutation C C' -> ept C' D K) /\
  (forall {C: sctx} {N K: o}, lfc C N K -> forall {C': sctx}, Permutation C C' -> lfc C' N K) /\
  (forall {C: sctx} {P: o}, rfc C P -> forall {C': sctx}, Permutation C C' -> rfc C' P). 
Proof.
    apply LJFPS_mutind_all ; intros.
        - apply bct_R_box. apply b. apply H. apply H0.
        - apply bct_R_AndN. 
            + apply H. apply H1.
            + apply H0. apply H1.
        - apply bct_R_Impl. apply H. apply H0.
        - apply ept_L_f with (N := N). apply b. apply n. apply perm_has_entry with (l := S).
            apply h. apply H0. apply H. apply H0.
        - apply ept_R_f. apply p. apply H. apply H0.
        - apply ept_L_box. apply b. apply p. apply H. apply Permutation_cons. 
            reflexivity. apply H0.
        - apply ept_L_AndP. apply b. apply H. apply H0.
        - apply ept_L_Or. apply b. apply H. apply H1. apply H0. apply H1.
        - apply ept_L_True. apply b. apply H. apply H0.
        - apply ept_L_False. apply b.
        - apply lfc_R_l. apply b. apply p. apply H. apply H0.
        - apply lfc_I_l. apply n. apply a.
        - apply lfc_L_AndN_1. apply b. apply H. apply H0.
        - apply lfc_L_AndN_2. apply b. apply H. apply H0.
        - apply lfc_L_Impl. apply b. apply H. apply H1. apply H0. apply H1.
        - apply rfc_R_r. apply n. apply H. apply H0.
        - apply rfc_I_r. apply p. apply a. apply perm_has_entry with (l := S).
            apply h. apply H.
        - apply rfc_R_AndP. apply H. apply H1. apply H0. apply H1.
        - apply rfc_R_Or_1. apply H. apply H0.
        - apply rfc_R_Or_2. apply H. apply H0.
        - apply rfc_R_True.
Qed.

Lemma LJFPS_exchange_structural_perm_bct :
    forall {C: sctx} {D: octx} {K: o}, bct C D K -> forall {C': sctx}, Permutation C C' -> bct C' D K.
Proof.
  destruct LJFPS_exchange_structural_perm. apply H.
Qed.

Lemma LJFPS_exchange_structural_perm_ept :
    forall {C: sctx} {D: octx} {K: o}, ept C D K -> forall {C': sctx}, Permutation C C' -> ept C' D K.
Proof.
  destruct LJFPS_exchange_structural_perm. destruct H0. apply H0.
Qed.

Lemma LJFPS_exchange_structural_perm_lfc :
  forall {C: sctx} {N K: o}, lfc C N K -> forall {C': sctx}, Permutation C C' -> lfc C' N K.
Proof.
  destruct LJFPS_exchange_structural_perm. destruct H0. destruct H1. apply H1.
Qed.

Lemma LJFPS_exchange_structural_perm_rfc :
  forall {C: sctx} {K: o}, rfc C K -> forall {C': sctx}, Permutation C C' -> rfc C' K.
Proof.
  destruct LJFPS_exchange_structural_perm. destruct H0. destruct H1. apply H2.
Qed.


Lemma Permutation_singleton : 
  forall {B: o} {C: octx},
    Permutation (B :: nil) C -> C = (B :: nil).
Proof.
  intros B C H. remember (B :: nil) as b. induction H.
    - reflexivity.
    - inversion Heqb. subst. apply Permutation_nil in H. subst. reflexivity. 
    - exfalso. inversion Heqb.
    - transitivity l'. apply IHPermutation2. symmetry. transitivity l. symmetry. apply Heqb.
      symmetry. apply IHPermutation1. apply Heqb. apply IHPermutation1. apply Heqb.
Qed.
  

Lemma LJFPS_eager_box :
  forall {S': sctx} {O: octx} {K: o}, 
    bracketable K ->
    ept S' O K ->
  forall {S: sctx} {B: o},
    Permutation S' ((B, tt) :: S) ->
    permeable B ->
    forall {O1 O2: octx}, 
    O = O1 ++ O2 ->
    ept S (O1 ++ B :: O2) K.
Proof.
  intros S' O K Br H. induction H ; intros S0 B0 Pt Pb O1 O2 Ho.
    - symmetry in Ho. apply app_eq_nil in Ho. destruct Ho. subst.
      simpl. apply ept_L_box. apply H. apply Pb.
      apply ept_L_f with (N := N). apply H. apply H0.
        + apply perm_has_entry with (l := S). apply H1. apply Pt.
        + eapply LJFPS_exchange_structural_perm_lfc. apply H2. apply Pt.
    - symmetry in Ho. apply app_eq_nil in Ho. destruct Ho. subst.
      simpl. apply ept_L_box. apply Br. apply Pb.
      apply ept_R_f. apply H. eapply LJFPS_exchange_structural_perm_rfc.
      apply H0. apply Pt.
    - symmetry in Ho. apply app_eq_cons in Ho. destruct Ho.
      + destruct H2. subst. simpl. 
        apply ept_L_box. apply Br. apply Pb.
        apply ept_L_box. apply Br. apply H0.
        eapply LJFPS_exchange_structural_perm_ept. apply H1. apply Permutation_cons.
        reflexivity. apply Pt.
      + destruct H2. destruct H2. subst. simpl.
        apply ept_L_box. apply H. apply H0.
        eapply IHept. apply Br. apply Permutation_sym. 
        -- apply perm_trans with ((B, tt) :: (B0, tt) :: S0). apply perm_swap.
           apply Permutation_cons. reflexivity. apply Permutation_sym. apply Pt.
        -- apply Pb.
        -- reflexivity.
    - symmetry in Ho. apply app_eq_cons in Ho. destruct Ho.
      + destruct H1. subst. simpl.
        apply ept_L_box. apply H. apply Pb.
        apply ept_L_AndP. apply H.
        eapply LJFPS_exchange_structural_perm_ept. apply H0. apply Pt.
      + destruct H1. destruct H1. subst. simpl.
        apply ept_L_AndP. apply H.
        eapply IHept with (O1 := B2 :: B1 :: x). apply Br. apply Pt. apply Pb. reflexivity.
    - symmetry in Ho. apply app_eq_cons in Ho. destruct Ho.
      + destruct H2. subst. simpl.
        apply ept_L_box. apply H. apply Pb.
        apply ept_L_Or. apply H.
        -- eapply LJFPS_exchange_structural_perm_ept. apply H0. apply Pt.
        -- eapply LJFPS_exchange_structural_perm_ept. apply H1. apply Pt.
      + destruct H2. destruct H2. subst. simpl.
        apply ept_L_Or. apply H.
        -- eapply IHept1 with (O1 := B1 :: x). apply Br. apply Pt. apply Pb. reflexivity. 
        -- eapply IHept2 with (O1 := B2 :: x). apply Br. apply Pt. apply Pb. reflexivity. 
    - symmetry in Ho. apply app_eq_cons in Ho. destruct Ho.
      + destruct H1. subst. simpl.
        apply ept_L_box. apply H. apply Pb.
        apply ept_L_True. apply H. 
        eapply LJFPS_exchange_structural_perm_ept. apply H0. apply Pt.
      + destruct H1. destruct H1. subst. simpl.
        apply ept_L_True. apply H.
        eapply IHept. apply Br. apply Pt. apply Pb. reflexivity.
    - symmetry in Ho. apply app_eq_cons in Ho. destruct Ho.
      + destruct H0. subst. simpl. 
        apply ept_L_box. apply H. apply Pb. apply ept_L_False. apply H.
      + destruct H0. destruct H0. subst. simpl. apply ept_L_False. apply H.
Qed.

Lemma LJFPS_eager_AndP :
  forall {S: sctx} {O: octx} {K: o},
    bracketable K ->
    ept S O K ->
    forall {B1 B2: o} {O1 O2: octx},
      O = O1 ++ B2 :: B1 :: O2 ->
      ept S (O1 ++ (AndP B1 B2) :: O2) K.
Proof.
  intros S O K Br H. induction H ; intros B1' B2' O1 O2 Ho.
    - symmetry in Ho. apply app_eq_nil in Ho. destruct Ho. discriminate H4.
    - symmetry in Ho. apply app_eq_nil in Ho. destruct Ho. discriminate H2.
    - symmetry in Ho. apply app_eq_cons in Ho. destruct Ho.
      + destruct H2. inversion H3. subst. clear H3. simpl.
        apply ept_L_AndP. apply H.
        apply ept_L_box. apply H. apply H0. apply H1. 
      + destruct H2. destruct H2. subst. simpl.
        apply ept_L_box. apply H. apply H0. 
        apply IHept. apply H. reflexivity.
    - symmetry in Ho. apply app_eq_cons in Ho. destruct Ho.
      + destruct H1. inversion H2. subst. simpl.
        apply ept_L_AndP. apply H. 
        apply ept_L_AndP. apply H. apply H0. 
      + destruct H1. destruct H1. subst. simpl.
        apply ept_L_AndP. apply H.
        eapply IHept with (O1 := (B2 :: B1 :: x)). apply H. reflexivity.
    - symmetry in Ho. apply app_eq_cons in Ho. destruct Ho.
      + destruct H2. inversion H3. subst. simpl. clear H3.
        apply ept_L_AndP. apply H. apply ept_L_Or. apply H.
        apply H0. apply H1.
      + destruct H2. destruct H2. subst. simpl.
        apply ept_L_Or. apply H.
        -- apply IHept1 with (O1 := (B1 :: x)). apply H. reflexivity.
        -- apply IHept2 with (O1 := (B2 :: x)). apply H. reflexivity.
    - symmetry in Ho. apply app_eq_cons in Ho. destruct Ho.
      + destruct H1. inversion H2. subst. simpl.
        apply ept_L_AndP. apply H.
        apply ept_L_True. apply H.
        apply H0.
      + destruct H1. destruct H1. subst. simpl.
        apply ept_L_True. apply H. 
        apply IHept. apply H. reflexivity.
    - symmetry in Ho. apply app_eq_cons in Ho. destruct Ho.
      + destruct H0. inversion H1. subst. simpl. 
        apply ept_L_AndP. apply H. apply ept_L_False. apply H.
      + destruct H0. destruct H0. subst. simpl.
        apply ept_L_False. apply H.
Qed.

Lemma LJFPS_eager_True :
  forall {S: sctx} {O: octx} {K: o},
    bracketable K ->
    ept S O K ->
    forall {O1 O2: octx},
      O = O1 ++ O2 ->
      ept S (O1 ++ TT :: O2) K.
Proof.
  intros S O K Br H. induction H ; intros O0 O3 Ho.
    - symmetry in Ho. apply app_eq_nil in Ho. destruct Ho. subst. simpl.
      apply ept_L_True. apply H. eapply ept_L_f. apply H. apply H0.
      apply H1. apply H2.
    - symmetry in Ho. apply app_eq_nil in Ho. destruct Ho. subst. simpl.
      apply ept_L_True. apply Br. apply ept_R_f. apply H. apply H0.
    - destruct O0.
      + simpl in Ho. subst. simpl. apply ept_L_True. apply H.
        apply ept_L_box. apply H. apply H0. apply H1.
      + simpl in Ho. inversion Ho. subst. simpl.
        apply ept_L_box. apply H. apply H0.
        apply IHept. apply H. reflexivity.
    - destruct O0.
      + simpl in Ho. subst. simpl. apply ept_L_True. apply H.
        apply ept_L_AndP. apply H. apply H0.
      + simpl in Ho. inversion Ho. subst. simpl.
        apply ept_L_AndP. apply H.
        eapply IHept with (O1 := B2 :: B1 :: O0) (O2 := O3). apply H. reflexivity.
    - destruct O0.
      + simpl in Ho. subst. simpl. apply ept_L_True. apply H.
        apply ept_L_Or. apply H. apply H0. apply H1.
      + simpl in Ho. inversion Ho. subst. simpl.
        apply ept_L_Or. apply H.
        -- eapply IHept1 with (O1 := B1 :: O0). apply H. reflexivity.
        -- eapply IHept2 with (O1 := B2 :: O0). apply H. reflexivity.
    - destruct O0.
      + simpl in Ho. subst. simpl. apply ept_L_True. apply H.
        apply ept_L_True. apply H. apply H0.
      + simpl in Ho. inversion Ho. subst. simpl.
        apply ept_L_True. apply H. apply IHept. apply H. reflexivity.
    - destruct O0.
      + simpl in Ho. subst. simpl. apply ept_L_True. apply H.
        apply ept_L_False. apply H.
      + simpl in Ho. inversion Ho. subst. simpl.
        apply ept_L_False. apply H.
Qed.


Lemma LJFPS_inversion_L_box :
  forall {S: sctx} {O: octx} {B K: o},
    bracketable K ->
    permeable B ->
    ept S O K ->
    forall {O': octx},
      O = B :: O' ->  
      ept ((B, tt) :: S) O' K.
Proof.
  intros S O B K Br Pb H. induction H ; intros O1 Ho.
    - discriminate Ho.
    - discriminate Ho.
    - inversion Ho. subst. apply H1.
    - inversion Ho. subst. inversion Pb. inversion H1. inversion H1.
    - inversion Ho. subst. inversion Pb. inversion H2. inversion H2.
    - inversion Ho. subst. inversion Pb. inversion H1. inversion H1.
    - inversion Ho. subst. inversion Pb. inversion H0. inversion H0.
Qed.

Lemma LJFPS_eager_Or :
  forall {S: sctx} {O: octx} {K: o},
    bracketable K ->
    ept S O K ->
    forall {O' : octx},
      ept S O' K ->
      forall {B1 B2: o} {O1 O2: octx},
        O = O1 ++ B1 :: O2 ->
        O' = O1 ++ B2 :: O2 ->
        ept S (O1 ++ (Or B1 B2) :: O2) K.
Proof.
  intros S O K Br H. induction H ; intros O' H' B0 B3 O1 O2 Ho Ho'.
    - subst. symmetry in Ho. apply app_eq_nil in Ho. destruct Ho.
      inversion H4.
    - subst. symmetry in Ho. apply app_eq_nil in Ho. destruct Ho.
      inversion H2.
    - subst. symmetry in Ho. apply app_eq_cons in Ho. destruct Ho.
      + destruct H2. inversion H3. subst. simpl. 
        apply ept_L_Or. apply H.
          -- apply ept_L_box. apply H. apply H0. apply H1.
          -- apply H'.
      + destruct H2. destruct H2. subst. simpl.
        apply ept_L_box. apply H. apply H0.
        simpl in H'.
        eapply IHept with (O' := x ++ B3 :: O2). apply H.
        eapply LJFPS_inversion_L_box. apply H. apply H0.
        apply H'. reflexivity. reflexivity. reflexivity.
    - symmetry in Ho. apply app_eq_cons in Ho. destruct Ho.
      + destruct H1. inversion H2. subst. simpl. 
        apply ept_L_Or. apply H. apply ept_L_AndP. apply H. apply H0. apply H'.
      + destruct H1. destruct H1. subst.
        simpl. apply ept_L_AndP. apply H.
        eapply IHept with (O1 := B2 :: B1 :: x). apply H.
        inversion H'. subst. inversion H5. inversion H1. inversion H1. subst.
        apply H7. reflexivity. reflexivity.
    - subst. symmetry in Ho. apply app_eq_cons in Ho. destruct Ho.
      + destruct H2. inversion H3. subst. simpl.
        apply ept_L_Or. apply H. apply ept_L_Or. apply H.
        apply H0. apply H1. apply H'.
      + destruct H2. destruct H2. subst. simpl.
        apply ept_L_Or. apply H. 
        inversion H'. subst. inversion H6. inversion H2. inversion H2. subst.
        eapply IHept1 with (O1 := B1 :: x). apply H. apply H8. reflexivity. reflexivity.
        inversion H'. subst. inversion H6. inversion H2. inversion H2. subst.
        eapply IHept2 with (O1 := B2 :: x). apply H. apply H9. reflexivity. reflexivity.
    - symmetry in Ho. apply app_eq_cons in Ho. destruct Ho.
      + destruct H1. inversion H2. subst. simpl.
        apply ept_L_Or. apply H.
        apply ept_L_True. apply H. apply H0.
        apply H'.
      + destruct H1. destruct H1. subst. simpl.
        apply ept_L_True. apply H.
        eapply IHept. apply H.
        inversion H'. subst. inversion H5. inversion H1. inversion H1.
        subst. apply H4. reflexivity. reflexivity.
    - symmetry in Ho. apply app_eq_cons in Ho. destruct Ho.
      + destruct H0. inversion H1. subst. simpl.
        apply ept_L_Or. apply H. apply ept_L_False. apply H. apply H'.
      + destruct H0. destruct H0. subst. simpl. apply ept_L_False. apply H.
Qed. 


Lemma LJFPS_eager_False :
  forall {O1: octx} {K: o},
    bracketable K ->
    forall {S: sctx} {O2: octx},
    ept S (O1 ++ FF :: O2) K.
Admitted.


Scheme bct_mut_async := Induction for bct Sort Prop
  with ept_mut_async := Induction for ept Sort Prop.
Combined Scheme LJFPS_mutind_async from bct_mut_async, ept_mut_async.

Lemma LJF_exchange_ordered_perm :
  (forall {C: sctx} {D: octx} {K: o}, bct C D K -> forall {D': octx}, Permutation D D' -> bct C D' K) /\
  (forall {C: sctx} {D: octx} {K: o}, ept C D K -> forall {D': octx}, Permutation D D' -> ept C D' K).
Proof.
    apply LJFPS_mutind_async ; intros.
        - apply bct_R_box. apply b. apply H. apply H0.
        - apply bct_R_AndN. apply H. apply H1. apply H0. apply H1.
        - apply bct_R_Impl. apply H. apply Permutation_cons. reflexivity. apply H0.
        - apply Permutation_nil in H. subst. apply ept_L_f with (N := N) ; assumption.
        - apply Permutation_nil in H. subst. apply ept_R_f ; assumption.
        - assert (Hin : In B D').
          + apply Permutation_in with (x := B) in H0. apply H0. apply in_eq.  
          + apply in_split in Hin. destruct Hin. destruct H1. subst.
            eapply LJFPS_eager_box.
            -- apply b.
            -- apply H. eapply Permutation_cons_app_inv. apply H0.
            -- apply Permutation_refl.
            -- apply p.
            -- reflexivity.
        - assert (Hin : In (AndP B1 B2) D').
          + apply Permutation_in with (x := (AndP B1 B2)) in H0. apply H0. apply in_eq.
          + apply in_split in Hin. destruct Hin. destruct H1. subst.
            eapply LJFPS_eager_AndP. apply b. 
            assert (H1 : ept S (x ++ B2 :: B1 :: x0) K).
            apply H. 
            apply Permutation_cons_app_inv with (l := O) in H0.
            apply Permutation_cons_app with (l := B1 :: O).
            apply Permutation_cons_app with (l := O). apply H0.
            apply H1. reflexivity.   
        - assert (Hin : In (Or B1 B2) D').
          + apply Permutation_in with (x := Or B1 B2) in H1. apply H1. apply in_eq.
          + apply in_split in Hin. destruct Hin. destruct H2. subst.
            eapply LJFPS_eager_Or. apply b.
            assert (H2 : ept S (x ++ B1 :: x0) K).
            apply H. 
            eapply Permutation_cons_app_inv with (l := O) in H1.
            eapply Permutation_cons_app with (l := O). apply H1.
            apply H2.
            assert (H2 : ept S (x ++ B2 :: x0) K).
            apply H0. 
            eapply Permutation_cons_app_inv with (l := O) in H1.
            eapply Permutation_cons_app with (l := O). apply H1.
            apply H2.
            reflexivity. reflexivity.
        - assert (Hin : In TT D').
          + apply Permutation_in with (x := TT) in H0. apply H0. apply in_eq.
          + apply in_split in Hin. destruct Hin. destruct H1. subst.
            eapply LJFPS_eager_True. apply b.
            assert (H1 : ept S (x ++ x0) K).
            apply H. 
            eapply Permutation_cons_app_inv with (l := O) in H0.
            apply H0.
            apply H1.
            reflexivity.
        - assert (Hin : In FF D').
          + apply Permutation_in with (x := FF) in H. apply H. apply in_eq.
          + apply in_split in Hin. destruct Hin. destruct H0. subst.
            eapply LJFPS_eager_False. apply b.
Qed.

