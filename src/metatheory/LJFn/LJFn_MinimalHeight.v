From Stdlib Require Import List PeanoNat Wf_nat Classical_Prop.
From LJF Require Import SharedLogic Pndctx LJFn_Rules Schemes.

Definition min_height_eptn (m: nat) (C: pndctx) (L: octx) (K: o) :=
    eptn m C L K /\ forall (n: nat), n < m -> ~ (eptn n C L K).

Lemma min_height_exists : forall (m: nat) (C: pndctx) (K: o),
  eptn m C nil K -> exists (n: nat), n <= m /\ min_height_eptn n C nil K.
Proof.
    induction m as [m IH] using (well_founded_ind lt_wf).
    intros C K H. 
    destruct (classic (exists y, y < m /\ eptn y C nil K)).
    - destruct H0 as [y [H0 H1]].
        destruct (IH y H0 C K H1) as [x [H2 H3]].
        eexists x. split.
        + transitivity y. apply H2. apply (Nat.lt_le_incl y m H0).
        + apply H3.
    - eexists m. split. reflexivity. split.
        + apply H.
        + intros. intro. exact (H0 (ex_intro _ n (conj H1 H2))).
Qed.
