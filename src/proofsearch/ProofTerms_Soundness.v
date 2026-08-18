From Stdlib Require Import List.
From LJF Require Import SharedLogic LJFPS_Rules Pndctx Sequents ProofTerms.

Theorem verify_soundness :
  forall {p: pterm} {seq: sequent}, verify p seq -> sequent_derivable seq.
Proof.
  intros. induction H ; unfold sequent_derivable in*.
  - apply (bct_boxR H IHverify).
  - apply (bct_AndNR IHverify1 IHverify2).
  - apply (bct_ImpR IHverify).
  - apply (ept_Lf N H H0 H1 IHverify).
  - apply (ept_Rf H IHverify).
  - apply (ept_boxL H H0 IHverify).
  - apply (ept_AndPL H IHverify).
  - apply (ept_OrL H IHverify1 IHverify2).
  - apply (ept_TrueL H IHverify).
  - apply (ept_FalseL H).
  - apply (lfc_Rl H H0 IHverify).
  - apply (lfc_Il H H0).
  - apply (lfc_AndNL_1 H IHverify).
  - apply (lfc_AndNL_2 H IHverify).
  - apply (lfc_ImpL H IHverify1 IHverify2).
  - apply (rfc_Rr H IHverify).
  - apply (rfc_Ir H H0 H1).
  - apply (rfc_AndPR IHverify1 IHverify2).
  - apply (rfc_OrR_1 IHverify).
  - apply (rfc_OrR_2 IHverify).
  - apply rfc_TrueR.
Qed.
