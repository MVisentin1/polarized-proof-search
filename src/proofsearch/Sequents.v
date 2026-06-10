From Stdlib Require Import List.
From LJF Require Import SharedLogic Decidability Predicates Subformula Pndctx LJFPS_Rules.

Variant sequent : Type :=
| Sbct : pndctx -> octx -> o -> sequent
| Sept : pndctx -> octx -> o -> sequent
| Slfc : pndctx -> o -> o -> sequent
| Srfc : pndctx -> o -> sequent
.

Definition sequent_derivable (S : sequent) : Prop :=
    match S with
    | Sbct C L K => bct C L K
    | Sept C L K => ept C L K
    | Slfc C N K => lfc C N K
    | Srfc C K   => rfc C K
    end
.

Definition sequent_formulas (S: sequent) : list o :=
    match S with
    | Sbct C L K => (pndctx_list C) ++ L ++ (K :: nil)
    | Sept C L K => (pndctx_list C) ++ L ++ (K :: nil)
    | Slfc C N K => (pndctx_list C) ++ (N :: K :: nil)
    | Srfc C K   => (pndctx_list C) ++ (K :: nil)
    end
.

Definition sequent_subformulas (S: sequent) : list o :=
    nodup o_eq_dec (flat_map subformulas (sequent_formulas S))
.

Lemma sequent_subformulas_transitivity :
    forall {A: o} (B: o) {S: sequent},
    subformula A B ->
    In B (sequent_subformulas S) ->
    In A (sequent_subformulas S).
Proof.
    intros.
    unfold sequent_subformulas in*.
    apply nodup_In.
    apply in_flat_map.
    apply nodup_In in H0.
    apply in_flat_map in H0.
    destruct H0.
    eexists x.
    destruct H0.
    split.
    apply H0.
    eapply subformulas_trans.
    apply subformula_iff_subformulas in H.
    apply H. apply H1.
Qed.

Definition sequent_subformulas_positive (S: sequent) : list o :=
    filter positive_b (sequent_subformulas S)
.

Definition sequent_subformulas_negative (S: sequent) : list o :=
    filter negative_b (sequent_subformulas S)
.

Definition sequent_subformulas_permeable (S: sequent) : list o :=
    filter permeable_b (sequent_subformulas S)
.

Definition subsequent (S S0: sequent) : Prop :=
    match S with
    | Sbct C L K => 
        Forall (fun A => In A (sequent_subformulas_permeable S0)) (pndctx_list C) /\
        Forall (fun A => In A (sequent_subformulas S0)) L /\
        In K (sequent_subformulas S0)
    | Sept C L K => 
        Forall (fun A => In A (sequent_subformulas_permeable S0)) (pndctx_list C) /\
        Forall (fun A => In A (sequent_subformulas S0)) L /\
        In K (sequent_subformulas S0)
    | Slfc C N K => 
        Forall (fun A => In A (sequent_subformulas_permeable S0)) (pndctx_list C) /\
        In N (sequent_subformulas S0) /\
        In K (sequent_subformulas S0)
    | Srfc C K   => 
        Forall (fun A => In A (sequent_subformulas_permeable S0)) (pndctx_list C) /\
        In K (sequent_subformulas S0)
    end
.