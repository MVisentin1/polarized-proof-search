From Stdlib Require Import List.
From LJF Require Import SharedLogic LJFPS_Rules Pndctx Sequents Schemes.

Inductive pterm : Type :=
  | pbct_boxR : pterm -> pterm
  | pbct_AndNR : pterm -> pterm -> pterm
  | pbct_ImpR : pterm -> pterm
  | pept_Lf : o -> pterm -> pterm
  | pept_Rf : pterm -> pterm
  | pept_boxL : pterm -> pterm
  | pept_AndPL : pterm -> pterm
  | pept_OrL : pterm -> pterm -> pterm
  | pept_TrueL : pterm -> pterm
  | pept_FalseL : pterm
  | plfc_Rl : pterm -> pterm
  | plfc_Il : pterm 
  | plfc_AndNL_1 : pterm -> pterm
  | plfc_AndNL_2 : pterm -> pterm
  | plfc_ImpL : pterm -> pterm -> pterm
  | prfc_Rr : pterm -> pterm
  | prfc_Ir : pterm
  | prfc_AndPR : pterm -> pterm -> pterm
  | prfc_OrR_1 : pterm -> pterm
  | prfc_OrR_2 : pterm -> pterm
  | prfc_TrueR : pterm
.

Inductive verify : pterm -> sequent -> Prop :=
  | vbct_boxR :
    forall {p: pterm} {C: pndctx} {L: octx} {D: o},
      bracketable D ->
      verify p (Sept C L D) ->
      verify (pbct_boxR p) (Sbct C L D)
  | vbct_AndNR :
    forall {p1 p2: pterm} {C: pndctx} {L: octx} {B1 B2: o},
      verify p1 (Sbct C L B1) ->
      verify p2 (Sbct C L B2) ->
      verify (pbct_AndNR p1 p2) (Sbct C L (AndN B1 B2))
  | vbct_ImpR :
    forall {p: pterm} {C: pndctx} {L: octx} {B1 B2: o},
      verify p (Sbct C (B1 :: L) B2) ->
      verify (pbct_ImpR p) (Sbct C L (Imp B1 B2))
  | vept_Lf :
    forall {p: pterm} {C: pndctx} {N : o} {K : o},
      In N (pndctx_list C) ->
      bracketable K ->
      negative N ->
      verify p (Slfc C N K) ->
      verify (pept_Lf N p) (Sept C nil K)
  | vept_Rf :
    forall {p: pterm} {C: pndctx} {P: o},
      positive P ->
      verify p (Srfc C P) ->
      verify (pept_Rf p) (Sept C nil P)
  | vept_boxL :
    forall {p: pterm} {C: pndctx} {L: octx} {B: o} {K: o},
      bracketable K ->
      permeable B ->
      verify p (Sept (pndctx_insert B C) L K) ->
      verify (pept_boxL p) (Sept C (B :: L) K)
  | vept_AndPL :
    forall {p: pterm} {C: pndctx} {L: octx} {B1 B2 : o} {K: o},
      bracketable K ->
      verify p (Sept C (B2 :: B1 :: L) K) ->
      verify (pept_AndPL p) (Sept C ((AndP B1 B2) :: L) K)
  | vept_OrL :
    forall {p1 p2: pterm} {C: pndctx} {L: octx} {B1 B2 : o}  {K: o},
      bracketable K ->
      verify p1 (Sept C (B1 :: L) K) ->
      verify p2 (Sept C (B2 :: L) K) ->
      verify (pept_OrL p1 p2) (Sept C ((Or B1 B2) :: L) K)
  | vept_TrueL :
    forall {p: pterm} {C: pndctx} {L: octx} {K: o},
      bracketable K ->
      verify p (Sept C L K) ->
      verify (pept_TrueL p) (Sept C (TT :: L) K)
  | vept_FalseL :
    forall {C: pndctx} {L: octx} {K: o},
      bracketable K ->
      verify pept_FalseL (Sept C (FF :: L) K)
  | vlfc_Rl :
    forall {p: pterm} {C: pndctx} {P : o}  {K : o},
      bracketable K ->
      positive P ->
      verify p (Sept C (P :: nil) K) ->
      verify (plfc_Rl p) (Slfc C P K)
  | vlfc_Il :
    forall {C: pndctx} {N : o},
      negative N ->
      atomic N ->
      verify plfc_Il (Slfc C N N)
  | vlfc_AndNL_1 :
    forall {p: pterm} {C: pndctx} {B1 B2 : o}  {K : o},
      bracketable K ->
      verify p (Slfc C B1 K) ->
      verify (plfc_AndNL_1 p) (Slfc C (AndN B1 B2) K)
  | vlfc_AndNL_2 :
    forall {p: pterm} {C: pndctx} {B1 B2 : o}  {K : o},
      bracketable K ->
      verify p (Slfc C B2 K) ->
      verify (plfc_AndNL_2 p) (Slfc C (AndN B1 B2) K)
  | vlfc_ImpL :
    forall {p1 p2: pterm} {C: pndctx} {B1 B2 : o}  {K : o},
      bracketable K ->
      verify p1 (Srfc C B1) ->
      verify p2 (Slfc C B2 K) ->
      verify (plfc_ImpL p1 p2) (Slfc C (Imp B1 B2) K)
  | vrfc_Rr :
    forall {p: pterm} {C: pndctx} {N: o},
      negative N ->
      verify p (Sbct C nil N) ->
      verify (prfc_Rr p) (Srfc C N)
  | vrfc_Ir :
    forall {C: pndctx} {P: o},
      In P (pndctx_list C) ->
      positive P ->
      atomic P ->
      verify prfc_Ir (Srfc C P)
  | vrfc_AndPR :
    forall {p1 p2: pterm} {C: pndctx} {B1 B2: o},
      verify p1 (Srfc C B1) ->
      verify p2 (Srfc C B2) ->
      verify (prfc_AndPR p1 p2) (Srfc C (AndP B1 B2))
  | vrfc_OrR_1 :
    forall {p: pterm} {C: pndctx} {B1 B2: o},
      verify p (Srfc C B1) ->
      verify (prfc_OrR_1 p) (Srfc C (Or B1 B2))
  | vrfc_OrR_2 :
    forall {p: pterm} {C: pndctx} {B1 B2: o},
      verify p (Srfc C B2) ->
      verify (prfc_OrR_2 p) (Srfc C (Or B1 B2))
  | vrfc_TrueR :
    forall {C: pndctx},
      verify prfc_TrueR (Srfc C TT)
.

Theorem verifiability_implies_derivability :
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

Theorem derivability_implies_verifiability :
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