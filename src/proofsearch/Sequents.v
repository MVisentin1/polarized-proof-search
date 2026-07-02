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
    intros. unfold sequent_subformulas in*.
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

Definition sequent_subformulas_bracketable (S: sequent) : list o :=
    filter bracketable_b (sequent_subformulas S)
.
Definition subsequent (S S0: sequent) : Prop :=
    match S with
    | Sbct C L K => 
        incl (pndctx_list C) (sequent_subformulas_permeable S0) /\
        incl L (sequent_subformulas S0) /\
        In K (sequent_subformulas S0)
    | Sept C L K => 
        incl (pndctx_list C) (sequent_subformulas_permeable S0) /\
        incl L (sequent_subformulas S0) /\
        In K (sequent_subformulas_bracketable S0)
    | Slfc C N K => 
        incl (pndctx_list C) (sequent_subformulas_permeable S0) /\
        In N (sequent_subformulas S0) /\
        In K (sequent_subformulas_bracketable S0)
    | Srfc C K   => 
        incl (pndctx_list C) (sequent_subformulas_permeable S0) /\
        In K (sequent_subformulas S0)
    end.

Definition subsequent_refl_premise (S : sequent) : Prop :=
  match S with
  | Sept _ _ K => bracketable K
  | Slfc _ _ K => bracketable K
  | _ => True
  end.

Lemma subsequent_refl (S : sequent) : subsequent_refl_premise S -> subsequent S S.
Proof.
  destruct S as [C L K | C L K | C N K | C K] ; intro Hbr ; simpl in Hbr ; repeat split.
  - intro x. intro Hx.
    unfold sequent_subformulas_permeable, sequent_subformulas, sequent_formulas.
    apply filter_In.
    specialize (pndctx_permeable_ctx C) ; intro H0.
    unfold permeable_ctx in H0. specialize (proj1 (Forall_forall _ _) H0 x Hx) ; intro Hp.
    split.
    + apply nodup_In ; apply in_flat_map. eexists x. split.
      * apply in_app_iff. left. apply Hx.
      * apply (proj1 (subformula_iff_subformulas _ _) (Sub_Refl x)).
    + apply (proj2 (permeable_b_iff _) Hp).
  - intro x. intro Hx.
    unfold sequent_subformulas, sequent_formulas.
    apply nodup_In ; apply in_flat_map. eexists x. split.
    + apply in_app_iff. right. apply in_app_iff. left. apply Hx.
    + apply (proj1 (subformula_iff_subformulas _ _) (Sub_Refl x)).
  - unfold sequent_subformulas, sequent_formulas.
    apply nodup_In. apply in_flat_map. eexists K. split.
    + apply in_app_iff. right. apply in_app_iff. right. apply in_eq.
    + apply (proj1 (subformula_iff_subformulas _ _) (Sub_Refl K)).
  - intro x. intro Hx.
    unfold sequent_subformulas_permeable, sequent_subformulas, sequent_formulas.
    apply filter_In.
    specialize (pndctx_permeable_ctx C) ; intro H0.
    unfold permeable_ctx in H0. specialize (proj1 (Forall_forall _ _) H0 x Hx) ; intro Hp.
    split.
    + apply nodup_In ; apply in_flat_map. eexists x. split.
      * apply in_app_iff. left. apply Hx.
      * apply (proj1 (subformula_iff_subformulas _ _) (Sub_Refl x)).
    + apply (proj2 (permeable_b_iff _) Hp).
  - intro x. intro Hx.
    unfold sequent_subformulas, sequent_formulas.
    apply nodup_In ; apply in_flat_map. eexists x. split.
    + apply in_app_iff. right. apply in_app_iff. left. apply Hx.
    + apply (proj1 (subformula_iff_subformulas _ _) (Sub_Refl x)).
  - unfold sequent_subformulas_bracketable.
    apply filter_In. split.
    + unfold sequent_subformulas, sequent_formulas.
      apply nodup_In. apply in_flat_map. eexists K. split.
      * apply in_app_iff. right. apply in_app_iff. right. apply in_eq.
      * apply (proj1 (subformula_iff_subformulas _ _) (Sub_Refl K)).
    + apply (proj2 (bracketable_b_iff _) Hbr).
  - intro x. intro Hx.
    unfold sequent_subformulas_permeable, sequent_subformulas, sequent_formulas.
    apply filter_In.
    specialize (pndctx_permeable_ctx C) ; intro H0.
    unfold permeable_ctx in H0. specialize (proj1 (Forall_forall _ _) H0 x Hx) ; intro Hp.
    split.
    + apply nodup_In ; apply in_flat_map. eexists x. split.
      * apply in_app_iff. left. apply Hx.
      * apply (proj1 (subformula_iff_subformulas _ _) (Sub_Refl x)).
    + apply (proj2 (permeable_b_iff _) Hp).
  - unfold sequent_subformulas, sequent_formulas.
    apply nodup_In. apply in_flat_map. eexists N. split.
    + apply in_app_iff. right. apply in_eq.
    + apply (proj1 (subformula_iff_subformulas _ _) (Sub_Refl N)).
  - apply filter_In. split.
    + unfold sequent_subformulas, sequent_formulas.
      apply nodup_In. apply in_flat_map. eexists K. split.
      * apply in_app_iff. right. apply in_cons. apply in_eq.
      * apply (proj1 (subformula_iff_subformulas _ _) (Sub_Refl K)).
    + apply (proj2 (bracketable_b_iff _) Hbr).
  - intro x. intro Hx.
    unfold sequent_subformulas_permeable, sequent_subformulas, sequent_formulas.
    apply filter_In.
    specialize (pndctx_permeable_ctx C) ; intro H0.
    unfold permeable_ctx in H0. specialize (proj1 (Forall_forall _ _) H0 x Hx) ; intro Hp.
    split.
    + apply nodup_In ; apply in_flat_map. eexists x. split.
      * apply in_app_iff. left. apply Hx.
      * apply (proj1 (subformula_iff_subformulas _ _) (Sub_Refl x)).
    + apply (proj2 (permeable_b_iff _) Hp).
  - unfold sequent_subformulas, sequent_formulas.
    apply nodup_In. apply in_flat_map. eexists K. split.
    + apply in_app_iff. right. apply in_eq.
    + apply (proj1 (subformula_iff_subformulas _ _) (Sub_Refl K)).
Qed.       
