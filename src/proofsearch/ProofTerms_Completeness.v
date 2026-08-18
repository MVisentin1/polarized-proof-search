From Stdlib Require Import List.
From LJF Require Import SharedLogic LJFPS_Rules Pndctx Sequents Schemes ProofTerms.

Theorem verify_completeness :
  (forall {C: pndctx} {L: octx} {K: o}, bct C L K -> exists (p : pterm), verify p (Sbct C L K)) /\
  (forall {C: pndctx} {L: octx} {K: o}, ept C L K -> exists (p : pterm), verify p (Sept C L K)) /\
  (forall {C: pndctx} {N K: o}, lfc C N K -> exists (p : pterm), verify p (Slfc C N K)) /\
  (forall {C: pndctx} {K: o}, rfc C K -> exists (p : pterm), verify p (Srfc C K)).
Proof.
  apply LJFPS_mutind_all ; intros.
  - destruct H as [p H] ; eexists (pbct_boxR p) ; apply (vbct_boxR b H).
  - destruct H as [p H] ; destruct H0 as [p0 H0] ; eexists (pbct_AndNR p p0) ; apply (vbct_AndNR H H0).
  - destruct H as [p H] ; eexists (pbct_ImpR p) ; apply (vbct_ImpR H).
  - destruct H as [p H] ; eexists (pept_Lf N p) ; apply (vept_Lf i b n H).
  - destruct H as [p0 H] ; eexists (pept_Rf p0) ; apply (vept_Rf p H).
  - destruct H as [p0 H] ; eexists (pept_boxL p0) ; apply (vept_boxL b p H).
  - destruct H as [p H] ; eexists (pept_AndPL p) ; apply (vept_AndPL b H).
  - destruct H as [p H] ; destruct H0 as [p0 H0] ; eexists (pept_OrL p p0) ; apply (vept_OrL b H H0).
  - destruct H as [p H] ; eexists (pept_TrueL p) ; apply (vept_TrueL b H).
  - eexists pept_FalseL ; apply (vept_FalseL b).
  - destruct H as [p0 H] ; eexists (plfc_Rl p0) ; apply (vlfc_Rl b p H).
  - eexists plfc_Il ; apply (vlfc_Il n a).
  - destruct H as [p H] ; eexists (plfc_AndNL_1 p) ; apply (vlfc_AndNL_1 b H).
  - destruct H as [p H] ; eexists (plfc_AndNL_2 p) ; apply (vlfc_AndNL_2 b H).
  - destruct H as [p H] ; destruct H0 as [p0 H0] ; eexists (plfc_ImpL p p0) ; apply (vlfc_ImpL b H H0).
  - destruct H as [p H] ; eexists (prfc_Rr p) ; apply (vrfc_Rr n H).
  - eexists prfc_Ir ; apply (vrfc_Ir i p a).
  - destruct H as [p H] ; destruct H0 as [p0 H0] ; eexists (prfc_AndPR p p0) ; apply (vrfc_AndPR H H0).
  - destruct H as [p H] ; eexists (prfc_OrR_1 p) ; apply (vrfc_OrR_1 H).
  - destruct H as [p H] ; eexists (prfc_OrR_2 p) ; apply (vrfc_OrR_2 H).
  - eexists prfc_TrueR ; apply vrfc_TrueR.
Qed.
