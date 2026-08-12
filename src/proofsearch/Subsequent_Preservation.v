From Stdlib Require Import List.
From LJF Require Import SharedLogic Predicates
    Pndctx Decidability Subformula Sequents.

Lemma subp_bct_boxR : 
    forall {C: pndctx} {L: octx} {D: o} {S: sequent},
    bracketable D ->
    subsequent (Sbct C L D) S ->
    subsequent (Sept C L D) S.
Proof.
    intros. destruct H0. destruct H1. repeat split.
    - apply H0.
    - apply H1.
    - unfold sequent_subformulas_bracketable. 
        apply (proj2 (filter_In _ _ _) (conj H2 (proj2 (bracketable_b_iff D) H))).
Qed.

Lemma subp_bct_AndNR : 
    forall {C: pndctx} {L: octx} {B1 B2: o} {S: sequent},
    subsequent (Sbct C L (AndN B1 B2)) S ->
    subsequent (Sbct C L B1) S /\ subsequent (Sbct C L B2) S. 
Proof.
    intros. destruct H. destruct H0. repeat split.
    - apply H.
    - apply H0.
    - apply (sequent_subformulas_transitivity (AndN B1 B2) (Sub_AndNL B1 B1 B2 (Sub_Refl B1)) H1).
    - apply H.
    - apply H0.
    - apply (sequent_subformulas_transitivity (AndN B1 B2) (Sub_AndNR B2 B1 B2 (Sub_Refl B2)) H1).
Qed.

Lemma subp_bct_ImpR :
    forall {C: pndctx} {L: octx} {B1 B2: o} {S: sequent},
    subsequent (Sbct C L (Imp B1 B2)) S ->
    subsequent (Sbct C (B1 :: L) B2) S.
Proof.
    intros. destruct H. destruct H0. unfold subsequent. repeat split.
    - apply H.
    - apply incl_cons.
        + apply (sequent_subformulas_transitivity (Imp B1 B2) (Sub_ImpL B1 B1 B2 (Sub_Refl B1)) H1).
        + apply H0.
    - apply (sequent_subformulas_transitivity (Imp B1 B2) (Sub_ImpR B2 B1 B2 (Sub_Refl B2)) H1). 
Qed.

Lemma subp_ept_Lf : 
    forall {C: pndctx} {N K : o} {S: sequent},
    In N (pndctx_list C) ->
    subsequent (Sept C nil K) S ->
    subsequent (Slfc C N K) S.
Proof.
    intros. destruct H0. destruct H1. repeat split.
    - apply H0.
    - unfold sequent_subformulas_permeable in H0.
        specialize (H0 N H). apply (proj1 (filter_In _ _ _) H0).
    - apply H2.
Qed.

Lemma subp_ept_Rf :
    forall {C: pndctx} {P: o} {S: sequent},
    subsequent (Sept C nil P) S -> 
    subsequent (Srfc C P) S.
Proof.
    intros. destruct H. destruct H0. repeat split.
    - apply H.
    - unfold sequent_subformulas_bracketable in H1. apply (proj1 (filter_In _ _ _) H1).
Qed.

Lemma subp_ept_boxL:
    forall {C: pndctx} {L: octx} {B K: o} {S: sequent},
    subsequent (Sept C (B :: L) K) S ->
    subsequent (Sept (pndctx_insert B C) L K) S.
Proof.
    intros. destruct H. destruct H0. repeat split.
    - unfold pndctx_list. unfold pndctx_insert. unfold raw_insert. simpl.
        destruct (permeable_dec B).
        + destruct (in_dec o_eq_dec B (pndctx_list C)).
            -- apply H.
            -- apply incl_cons.
                ++ unfold sequent_subformulas_permeable.
                    apply (proj2 (filter_In _ _ _) (conj (H0 B (in_eq B L)) (proj2 (permeable_b_iff B) p))).
                ++ apply H.
        + apply H.
    - apply (incl_cons_inv H0).
    - apply H1.
Qed.
    
Lemma subp_ept_AndPL:
    forall {C: pndctx} {L: octx} {B1 B2 : o} {K: o} {S: sequent},
    subsequent (Sept C ((AndP B1 B2) :: L) K) S ->
    subsequent (Sept C (B2 :: B1 :: L) K) S.
Proof.
    intros. destruct H. destruct H0. repeat split.
    - apply H.
    - destruct (incl_cons_inv H0). apply incl_cons.
        + apply (sequent_subformulas_transitivity (AndP B1 B2) (Sub_AndPR B2 B1 B2 (Sub_Refl B2)) H2).
        + apply incl_cons.
            -- apply (sequent_subformulas_transitivity (AndP B1 B2) (Sub_AndPL B1 B1 B2 (Sub_Refl B1)) H2).
            -- apply H3. 
    - apply H1.
Qed.

Lemma subp_ept_OrL :
  forall {C: pndctx} {L: octx} {B1 B2 : o} {K: o} {S: sequent},
    subsequent (Sept C ((Or B1 B2) :: L) K) S ->
    subsequent (Sept C (B1 :: L) K) S /\ 
    subsequent (Sept C (B2 :: L) K) S.
Proof.
    intros. destruct H. destruct H0. repeat split.
    - apply H.
    - destruct (incl_cons_inv H0).
        apply incl_cons.
        + apply (sequent_subformulas_transitivity (Or B1 B2) (Sub_OrL B1 B1 B2 (Sub_Refl B1)) H2).
        + apply H3.
    - apply H1.
    - apply H.
    - destruct (incl_cons_inv H0).
        apply incl_cons.
        + apply (sequent_subformulas_transitivity (Or B1 B2) (Sub_OrR B2 B1 B2 (Sub_Refl B2)) H2).
        + apply H3.
    - apply H1.
Qed.

Lemma subp_ept_TrueL :
  forall {C: pndctx} {L: octx} {K: o} {S: sequent},
    subsequent (Sept C (TT :: L) K) S ->
    subsequent (Sept C L K) S.
Proof.
    intros. destruct H. destruct H0. repeat split.
    - apply H.
    - destruct (incl_cons_inv H0). apply H3.
    - apply H1.
Qed.

Lemma subp_lfc_Rl :
  forall {C : pndctx} {P : o}  {K : o} {S: sequent},
    subsequent (Slfc C P K) S ->
    subsequent (Sept C (P :: nil) K) S. 
Proof.
    intros. destruct H. destruct H0. repeat split.
    - apply H.
    - apply incl_cons.
        + apply H0.
        + apply incl_nil_l.
    - apply H1.
Qed.

Lemma subp_lfc_AndNL_1 :
  forall {C: pndctx} {B1 B2 : o}  {K : o} {S: sequent},
    subsequent (Slfc C (AndN B1 B2) K) S ->
    subsequent (Slfc C B1 K) S.
Proof.
    intros. destruct H. destruct H0. repeat split.
    - apply H.
    - apply (sequent_subformulas_transitivity (AndN B1 B2) (Sub_AndNL B1 B1 B2 (Sub_Refl B1)) H0).
    - apply H1.
Qed.

Lemma subp_lfc_AndNL_2 :
  forall {C: pndctx} {B1 B2 : o}  {K : o} {S: sequent},
    subsequent (Slfc C (AndN B1 B2) K) S ->
    subsequent (Slfc C B2 K) S.
Proof.
    intros. destruct H. destruct H0. repeat split.
    - apply H.
    - apply (sequent_subformulas_transitivity (AndN B1 B2) (Sub_AndNR B2 B1 B2 (Sub_Refl B2)) H0).
    - apply H1.
Qed.

Lemma subp_lfc_ImpL :
  forall {C: pndctx} {B1 B2 : o}  {K : o} {S: sequent},
    subsequent (Slfc C (Imp B1 B2) K) S ->
    subsequent (Srfc C B1) S /\ subsequent (Slfc C B2 K) S.
Proof.
    intros. destruct H. destruct H0. repeat split.
    - apply H.
    - apply (sequent_subformulas_transitivity (Imp B1 B2) (Sub_ImpL B1 B1 B2 (Sub_Refl B1)) H0).
    - apply H.
    - apply (sequent_subformulas_transitivity (Imp B1 B2) (Sub_ImpR B2 B1 B2 (Sub_Refl B2)) H0).
    - apply H1.
Qed.

Lemma subp_rfc_Rr :
  forall {C: pndctx} {N: o} {S: sequent},
    subsequent (Srfc C N) S ->
    subsequent (Sbct C nil N) S.
Proof.
    intros. destruct H. repeat split.
    - apply H.
    - apply incl_nil_l.
    - apply H0.
Qed.

Lemma subp_rfc_AndPR :
  forall {C: pndctx} {B1 B2: o} {S: sequent},
    subsequent (Srfc C (AndP B1 B2)) S ->
    subsequent (Srfc C B1) S /\
    subsequent (Srfc C B2) S.
Proof.
    intros. destruct H. repeat split.
    - apply H.
    - apply (sequent_subformulas_transitivity (AndP B1 B2) (Sub_AndPL B1 B1 B2 (Sub_Refl B1)) H0).
    - apply H.
    - apply (sequent_subformulas_transitivity (AndP B1 B2) (Sub_AndPR B2 B1 B2 (Sub_Refl B2)) H0).
Qed.

Lemma subp_rfc_OrR_1 :
  forall {C: pndctx} {B1 B2: o} {S: sequent},
    subsequent (Srfc C (Or B1 B2)) S ->
    subsequent (Srfc C B1) S.
Proof.
    intros. destruct H. repeat split.
    - apply H.
    - apply (sequent_subformulas_transitivity (Or B1 B2) (Sub_OrL B1 B1 B2 (Sub_Refl B1)) H0).
Qed.

Lemma subp_rfc_OrR_2 :
  forall {C: pndctx} {B1 B2: o} {S: sequent},
    subsequent (Srfc C (Or B1 B2)) S ->
    subsequent (Srfc C B2) S.
Proof.
    intros. destruct H. repeat split.
    - apply H.
    - apply (sequent_subformulas_transitivity (Or B1 B2) (Sub_OrR B2 B1 B2 (Sub_Refl B2)) H0).
Qed.
