From Stdlib Require Import List Permutation.
From LJF Require Import SharedLogic Pndctx Schemes Sequents.
From LJF Require Import LJF_Rules LJF4_Rules LJFO_Rules LJFPS_Rules LJFn_Rules LJFh_Rules.

From LJF Require Import LJF4_Soundness LJFO_Soundness LJFPS_Soundness.
From LJF Require Import LJF4_Completeness LJFO_Completeness LJFPS_Completeness LJFn_Completeness LJFh_Completeness.

From LJF Require Import LJFPS_Bracketable.

From LJF Require Import Search_Procedure Search_Wrapper Search_Completeness.


Theorem LJFPS_Sound_And_Complete_To_LJF :
    (forall {C: pndctx} {L: octx} {K: o}, bct C L K <-> ufcL (pndctx_list C) L K Unbracketed) /\
    (forall {C: pndctx} {L: octx} {K: o}, ept C L K <-> ufcL (pndctx_list C) L K Bracketed) /\
    (forall {C: pndctx} {N K: o}, lfc C N K <-> lfcL (pndctx_list C) N K) /\
    (forall {C: pndctx} {K: o}, rfc C K <-> rfcL (pndctx_list C) K).
Proof.
    destruct LJF4_soundness as [S4b [S4e [S4l S4r]]].
    destruct LJFO_soundness as [SOb [SOe [SOl SOr]]].
    destruct LJFPS_soundness as [SPb [SPe [SPl SPr]]].
    destruct LJF4_completeness as [C4u [C4l C4r]].
    destruct LJFO_completeness as [COb [COe [COl COr]]].
    destruct LJFPS_completeness as [CPb [CPe [CPl CPr]]].
    repeat split ; intros.
    - apply (S4b (pndctx_list C) L K (SOb (pndctx_list C) L K (SPb C L K H))).
    - specialize (pndctx_list_mk_commute C) ; intro ; rewrite H0.
        apply (CPb (pndctx_list C) L K (COb (pndctx_list C) L K (C4u (pndctx_list C) L K Unbracketed H))).
    - apply (S4e (pndctx_list C) L K (SOe (pndctx_list C) L K (SPe C L K H))).
    - specialize (pndctx_list_mk_commute C) ; intro ; rewrite H0.
        apply (CPe (pndctx_list C) L K (COe (pndctx_list C) L K (C4u (pndctx_list C) L K Bracketed H))).
    - apply (S4l (pndctx_list C) N K (SOl (pndctx_list C) N K (SPl C N K H))).
    - specialize (pndctx_list_mk_commute C) ; intro ; rewrite H0.
        apply (CPl (pndctx_list C) N K (COl (pndctx_list C) N K (C4l (pndctx_list C) N K H))).
    - apply (S4r (pndctx_list C) K (SOr (pndctx_list C) K (SPr C K H))).
    - specialize (pndctx_list_mk_commute C) ; intro ; rewrite H0.
        apply (CPr (pndctx_list C) K (COr (pndctx_list C) K (C4r (pndctx_list C) K H))).
Qed. 

Print Assumptions LJFPS_Sound_And_Complete_To_LJF.
    
Theorem Derivable_iff_Search_Returns_Some_left :
    forall (s : sequent), sequent_derivable s <-> returns_some_proof (decide_sequent s).
Proof.
    destruct LJFn_completeness as [Cnb [Cne [Cnl Cnr]]].
    destruct LJFh_completeness_alt as [Chb [Che [Chl Chr]]].
    destruct search_complete as [Csb [Cse [Csl Csr]]].
    destruct s as [C L K | C L K | C N K | C K] ; unfold sequent_derivable ; split ; intros.
    - apply Csb. destruct (Cnb C L K H) as [n H0]. apply (Chb n C L K H0 nil (hist_height_bound_nil n)). 
    - unfold returns_some_proof in H. destruct (decide_sequent (Sbct C L K)). destruct s. apply s. contradiction. contradiction.
    - unfold decide_sequent. destruct (Decidability.bracketable_dec K).
        + apply Cse. destruct (Cne C L K H) as [n H0]. apply (Che n C L K H0 nil (hist_height_bound_nil n)).
        + destruct (n (LJFPS_bracketable_goal_ept H)).
    - unfold returns_some_proof in H. destruct (decide_sequent (Sept C L K)). destruct s. apply s. contradiction. contradiction.
    - unfold decide_sequent. destruct (Decidability.bracketable_dec K).
        + apply Csl. destruct (Cnl C N K H) as [n H0]. apply (Chl n C N K H0 nil (hist_height_bound_nil n)).
        + destruct (n (LJFPS_bracketable_goal_lfc H)).
    - unfold returns_some_proof in H. destruct (decide_sequent (Slfc C N K)). destruct s. apply s. contradiction. contradiction.
    - apply Csr. destruct (Cnr C K H) as [n H0]. apply (Chr n C K H0 nil (hist_height_bound_nil n)).
    - unfold returns_some_proof in H. destruct (decide_sequent (Srfc C K)). destruct s. apply s. contradiction. contradiction.
Qed.

Print Assumptions Derivable_iff_Search_Returns_Some_left.

Theorem Underivable_iff_Search_Returns_Some_Right_or_None :
    forall (s : sequent), ~ sequent_derivable s <-> returns_some_disproof (decide_sequent s) \/ returns_none (decide_sequent s).
Proof.
    intro s. split.
    - destruct (decide_sequent s) as [[s0 | s0] | ] ; intro.
        + contradiction.
        + left. apply I.
        + right. apply I.
    - intros. destruct (Derivable_iff_Search_Returns_Some_left s). destruct H ; destruct (decide_sequent s) as [[s0 | s0] | ] ; simpl in H ; try contradiction.
        + apply s0.
        + simpl in*. intro. apply (H0 H2).
Qed.

Print Assumptions Underivable_iff_Search_Returns_Some_Right_or_None.

Definition decide (s : sequent) : {sequent_derivable s} + {~ sequent_derivable s}.
Proof.
    destruct (decide_sequent s) as [[s0 | s0] | ] eqn:E.
    - left. apply s0.
    - right. apply s0.
    - right. intro H.
        apply (proj1 (Derivable_iff_Search_Returns_Some_left s)) in H.
        rewrite E in H. contradiction.
Defined.

Print Assumptions decide.

