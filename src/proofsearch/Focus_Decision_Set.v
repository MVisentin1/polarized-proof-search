From Stdlib Require Import List RelationClasses SetoidList.
From LJF Require Import SharedLogic Decidability 
    Pndctx Sequents SetoidList_Extended Subsets.

Definition pndctx_o_eq (P1 P2 : pndctx * o) : Prop :=
  pndctx_set_eq (fst P1) (fst P2) /\ snd P1 = snd P2.

#[export] Instance pndctx_o_eq_Equivalence : Equivalence pndctx_o_eq.
Proof.
  unfold pndctx_o_eq. constructor.
  - intro P. split ; reflexivity.
  - intros P1 P2 [H1 H2]. split ; symmetry ; assumption.
  - intros P1 P2 P3 [H1 H2] [H3 H4]. split.
    + etransitivity ; eauto.
    + etransitivity ; eauto.
Qed.

Lemma pndctx_o_eq_dec :
  forall (P1 P2 : pndctx * o), {pndctx_o_eq P1 P2} + {~ pndctx_o_eq P1 P2}.
Proof.
  unfold pndctx_o_eq. intros [C1 o1] [C2 o2]. simpl.
  destruct (pndctx_set_eq_dec C1 C2) ; destruct (o_eq_dec o1 o2).
  - left. split ; assumption.
  - right. intros [_ ?]. contradiction.
  - right. intros [? _]. contradiction.
  - right. intros [? _]. contradiction.
Qed.

Definition ctx_o_eq (L1 L2 : list o * o) : Prop :=
  equivlistA eq (fst L1) (fst L2) /\ snd L1 = snd L2.

#[export] Instance ctx_o_eq_Equivalence : Equivalence ctx_o_eq.
Proof.
  unfold ctx_o_eq. constructor.
  - intro L. split ; reflexivity.
  - intros L1 L2 [H1 H2]. split ; symmetry ; assumption.
  - intros L1 L2 L3 [H1 H2] [H3 H4]. split.
    + etransitivity ; eauto.
    + etransitivity ; eauto.
Qed.

Lemma ctx_o_eq_dec :
  forall (L1 L2 : list o * o), {ctx_o_eq L1 L2} + {~ ctx_o_eq L1 L2}.
Proof.
  unfold ctx_o_eq. intros [l1 o1] [l2 o2]. simpl.
  destruct (equivlistA_dec eq o_eq_dec l1 l2) ;
  destruct (o_eq_dec o1 o2).
  - left. split ; assumption.
  - right. intros [_ ?]. contradiction.
  - right. intros [? _]. contradiction.
  - right. intros [? _]. contradiction.
Qed.

Definition get_all_focus_decision (S: sequent) : list ((list o) * o) :=
    let per := sequent_subformulas_permeable S in
    let bra := sequent_subformulas_bracketable S in
    list_prod (get_all_subsets per) bra.

Lemma InA_eq_iff_in {A : Type}:
  forall {B : A} {L: list A},
    InA eq B L <-> In B L.
Proof.
  intros. split ; intros.
  - destruct (proj1 (InA_alt _ _ _) H) as [y [-> H0]].
    apply H0.
  - apply InA_alt. eexists B. split. reflexivity. apply H.
Qed.

Lemma InclA_eq_iff_incl {A : Type} :
  forall {L1 L2 : list A},
    inclA eq L1 L2 <-> incl L1 L2.
Proof.
  intros. split ; intros.
  - intro x. intro. specialize (H x (proj2 InA_eq_iff_in H0)).
    apply (proj1 InA_eq_iff_in H).
  - intro x. intro. specialize (H x (proj1 InA_eq_iff_in H0)).
    apply (proj2 InA_eq_iff_in H).
Qed. 

Lemma get_all_focus_decision_iff_subsequent :
    forall {C: pndctx} {K: o} {S : sequent},
        subsequent (Sept C nil K) S <-> InA ctx_o_eq (pndctx_list C, K) (get_all_focus_decision S).
Proof.
    intros. split ; intros.
    - destruct H. destruct H0. unfold get_all_focus_decision.
      assert (inclA eq (pndctx_list C) (sequent_subformulas_permeable S)).
      + intro x. intros. rewrite InA_alt in*.
        destruct H2 as [y [-> H2]].
        eexists y. split. reflexivity. apply (H y H2).
      + specialize (proj1 (inclA_iff_get_all_subsets o_eq_dec) H2) ; intro.
        destruct (proj1 (InA_alt _ _ _) H3) as [x [H4 H5]].
        apply InA_alt. eexists (x, K). split.
        -- unfold ctx_o_eq. simpl. split. apply H4. reflexivity.
        -- apply (in_prod _ _ _ _ H5 H1).
    - unfold get_all_focus_decision in H. 
      destruct (proj1 (InA_alt _ _ _) H) as [x [H0 H1]].
      destruct x.
      unfold ctx_o_eq in H0. simpl in H0. destruct H0. subst.
      destruct (proj1 (in_prod_iff _ _ _ _) H1).
      repeat split.
      + assert (InA (equivlistA eq) l (get_all_subsets (sequent_subformulas_permeable S))).
        -- apply InA_alt. eexists l. split. reflexivity. apply H2.
        -- symmetry in H0. rewrite H0 in H4.
          specialize (proj2 (inclA_iff_get_all_subsets o_eq_dec) H4) ; intro.
          apply (proj1 InclA_eq_iff_incl H5).
      + apply incl_nil_l.
      + apply H3.
Qed.
          



      


        

            
         
        

        

           
            



        
        




    