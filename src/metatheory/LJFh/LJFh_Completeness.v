From Stdlib Require Import List SetoidList Wf_nat.
From LJF Require Import SharedLogic Pndctx LJFh_Rules LJFn_Rules Schemes LJFn_MinimalHeight LJFn_Exchange.

Definition hist_height_bound (Hs : hist) (n : nat) : Prop :=
  forall (C: pndctx) (K: o), InA pndctx_o_eq (C, K) Hs -> 
    forall (m: nat), m <= n ->  ~ eptn m C nil K.

Lemma hist_height_bound_mono : 
  forall {Hs: hist} {m n: nat}, hist_height_bound Hs n -> m <= n -> hist_height_bound Hs m.
Proof.
  intros. intros C K H1 m0 H2 H3. assert (m0 <= n).
  - transitivity m. apply H2. apply H0.
  - apply (H C K H1 m0 H4 H3).
Qed.

Lemma hist_height_bound_mono_S :
  forall {Hs : hist} {n : nat}, hist_height_bound Hs (S n) -> hist_height_bound Hs n.
Proof. intros. apply (hist_height_bound_mono H (PeanoNat.Nat.le_succ_diag_r n)). Qed.
  
Lemma hist_height_bound_cons :
  forall {Hs: hist} {n: nat} {C: pndctx} {K: o}, 
  min_height_eptn (S n) C K -> hist_height_bound Hs (S n) -> hist_height_bound ((C, K) :: Hs) n.
Proof.
  intros. intros C0 K0 H1 m H2 H3.
  rewrite InA_cons in H1. destruct H1.
  - unfold pndctx_o_eq in H1 ; unfold pndctx_set_eq in H1 ; destruct H1 ; simpl in* ; subst.
    specialize (LJFn_exchange_structural_eptn H3 H1) ; intro.
    assert (m < S n).
    + unfold lt. apply (proj1 (PeanoNat.Nat.succ_le_mono m n) H2).
    + unfold min_height_eptn in H. destruct H. apply (H6 m H5 H4).
  - unfold hist_height_bound in H0.
    assert (m <= S n). transitivity n. apply H2. apply (PeanoNat.Nat.le_succ_diag_r n).
    apply (H0 C0 K0 H1 m H4 H3).
Qed.

Lemma hist_height_bound_notin :
  forall {Hs: hist} {n: nat} {C: pndctx} {K: o},
    hist_height_bound Hs n -> eptn n C nil K -> ~ InA pndctx_o_eq (C, K) Hs.
Proof.
  intros. intro. unfold hist_height_bound in H.
  assert (n <= n). reflexivity.
  apply (H C K H1 n H2 H0).
Qed.


Theorem LJFh_completeness : forall (n: nat),
  (forall {C: pndctx} {L: octx} {K: o}, bctn n C L K -> forall {Hs: hist}, hist_height_bound Hs n -> bcth Hs C L K) /\
  (forall {C: pndctx} {L: octx} {K: o}, eptn n C L K -> forall {Hs: hist}, hist_height_bound Hs n -> epth Hs C L K) /\
  (forall {C: pndctx} {N K: o}, lfcn n C N K -> forall {Hs: hist}, hist_height_bound Hs n -> lfch Hs C N K) /\
  (forall {C: pndctx} {K: o}, rfcn n C K -> forall {Hs: hist}, hist_height_bound Hs n -> rfch Hs C K).
Proof.
  intro n. induction n as [n IH] using (well_founded_ind lt_wf). repeat split.
  - intros. inversion H ; subst.
    + destruct (IH n0 (PeanoNat.Nat.lt_succ_diag_r n0)) as [IHb [IHe [IHl IHr]]].
      apply (bcth_boxR H1 (IHe C L K H2 Hs (hist_height_bound_mono_S H0))).
    + destruct (IH n0 (PeanoNat.Nat.lt_succ_diag_r n0)) as [IHb [IHe [IHl IHr]]].
      apply (bcth_AndNR (IHb C L B1 H1 Hs (hist_height_bound_mono_S H0)) (IHb C L B2 H2 Hs (hist_height_bound_mono_S H0))).
    + destruct (IH n0 (PeanoNat.Nat.lt_succ_diag_r n0)) as [IHb [IHe [IHl IHr]]].
      apply (bcth_ImpR (IHb C (B1 :: L) B2 H1 Hs (hist_height_bound_mono_S H0))).
  - intros. destruct L.
    + destruct (min_height_exists n C K H) as [x [H1 H2]].
      assert (hist_height_bound Hs x). apply (hist_height_bound_mono H0 H1).
      assert (~ InA pndctx_o_eq (C, K) Hs). apply (hist_height_bound_notin H0 H).
      assert (min_height_eptn x C K). apply H2. destruct H5.
      inversion H5 ; subst.
      -- destruct (IH n0 H1) as [IHb [IHe [IHl IHr]]].
        assert (hist_height_bound ((C, K) :: Hs) n0). apply (hist_height_bound_cons H2 H3).
        apply (epth_Lf N H4 H7 H8 H9 (IHl C N K H10 ((C, K) :: Hs) H11)).
      --  destruct (IH n0 H1) as [IHb [IHe [IHl IHr]]].
        assert (hist_height_bound ((C, K) :: Hs) n0). apply (hist_height_bound_cons H2 H3).
        apply (epth_Rf H4 H7 (IHr C K H8 ((C, K) :: Hs) H9)).
    + inversion H ; subst.
      -- destruct (IH n0 (PeanoNat.Nat.lt_succ_diag_r n0)) as [IHb [IHe [IHl IHr]]].
        apply (epth_boxL H3 H6 (IHe (pndctx_insert o C) L K H8 Hs (hist_height_bound_mono_S H0))).
      -- destruct (IH n0 (PeanoNat.Nat.lt_succ_diag_r n0)) as [IHb [IHe [IHl IHr]]]. 
        apply (epth_AndPL H5 (IHe C (B2 :: B1 :: L) K H7 Hs (hist_height_bound_mono_S H0))).
      -- destruct (IH n0 (PeanoNat.Nat.lt_succ_diag_r n0)) as [IHb [IHe [IHl IHr]]].
        apply (epth_OrL H3 (IHe C (B1 :: L) K H6 Hs (hist_height_bound_mono_S H0)) (IHe C (B2 :: L) K H8 Hs (hist_height_bound_mono_S H0))).
      -- destruct (IH n0 (PeanoNat.Nat.lt_succ_diag_r n0)) as [IHb [IHe [IHl IHr]]].
        apply (epth_TrueL H5 (IHe C L K H7 Hs (hist_height_bound_mono_S H0))).
      -- apply (epth_FalseL H6).
  - intros. inversion H ; subst.
    + destruct (IH n0 (PeanoNat.Nat.lt_succ_diag_r n0)) as [IHb [IHe [IHl IHr]]].
      apply (lfch_Rl H1 H2 (IHe C (N :: nil) K H3 Hs (hist_height_bound_mono_S H0))).
    + apply (lfch_Il H1 H2).
    + destruct (IH n0 (PeanoNat.Nat.lt_succ_diag_r n0)) as [IHb [IHe [IHl IHr]]].
      apply (lfch_AndNL_1 H1 (IHl C B1 K H2 Hs (hist_height_bound_mono_S H0))).
    + destruct (IH n0 (PeanoNat.Nat.lt_succ_diag_r n0)) as [IHb [IHe [IHl IHr]]].
      apply (lfch_AndNL_2 H1 (IHl C B2 K H2 Hs (hist_height_bound_mono_S H0))).
    + destruct (IH n0 (PeanoNat.Nat.lt_succ_diag_r n0)) as [IHb [IHe [IHl IHr]]].
      apply (lfch_ImpL H1 (IHr C B1 H2 Hs (hist_height_bound_mono_S H0)) (IHl C B2 K H3 Hs (hist_height_bound_mono_S H0))).
  - intros. inversion H ; subst.
    + destruct (IH n0 (PeanoNat.Nat.lt_succ_diag_r n0)) as [IHb [IHe [IHl IHr]]].
      apply (rfch_Rr H1 (IHb C nil K H2 Hs (hist_height_bound_mono_S H0))).
    + apply (rfch_Ir H1 H2 H3).
    + destruct (IH n0 (PeanoNat.Nat.lt_succ_diag_r n0)) as [IHb [IHe [IHl IHr]]].
      apply (rfch_AndPR (IHr C B1 H1 Hs (hist_height_bound_mono_S H0)) (IHr C B2 H2 Hs (hist_height_bound_mono_S H0))).
    + destruct (IH n0 (PeanoNat.Nat.lt_succ_diag_r n0)) as [IHb [IHe [IHl IHr]]].
      apply (rfch_OrR_1 (IHr C B1 H1 Hs (hist_height_bound_mono_S H0))).
    + destruct (IH n0 (PeanoNat.Nat.lt_succ_diag_r n0)) as [IHb [IHe [IHl IHr]]].
      apply (rfch_OrR_2 (IHr C B2 H1 Hs (hist_height_bound_mono_S H0))).
    + apply (rfch_TrueR).
Qed. 