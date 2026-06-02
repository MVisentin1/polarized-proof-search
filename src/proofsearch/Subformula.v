From Stdlib Require Import List.

From LJF Require Import SharedLogic Predicates.

Inductive subformula : o -> o -> Prop :=
| Sub_Refl  : forall A, subformula A A
| Sub_AndPL : forall A B C, subformula A B -> subformula A (AndP B C)
| Sub_AndPR : forall A B C, subformula A C -> subformula A (AndP B C)
| Sub_AndNL : forall A B C, subformula A B -> subformula A (AndN B C)
| Sub_AndNR : forall A B C, subformula A C -> subformula A (AndN B C)
| Sub_OrL : forall A B C, subformula A B -> subformula A (Or B C)
| Sub_OrR : forall A B C, subformula A C -> subformula A (Or B C)
| Sub_ImpL : forall A B C, subformula A B -> subformula A (Imp B C)
| Sub_ImpR : forall A B C, subformula A C -> subformula A (Imp B C)
.

Lemma subformula_trans :
    forall {A B C : o},
        subformula A B -> subformula B C -> subformula A C.
Proof.
    intros A B C H0 H1. induction H1.
    - apply H0.
    - apply Sub_AndPL. apply IHsubformula. apply H0.
    - apply Sub_AndPR. apply IHsubformula. apply H0.
    - apply Sub_AndNL. apply IHsubformula. apply H0.
    - apply Sub_AndNR. apply IHsubformula. apply H0.
    - apply Sub_OrL. apply IHsubformula. apply H0.
    - apply Sub_OrR. apply IHsubformula. apply H0.
    - apply Sub_ImpL. apply IHsubformula. apply H0.
    - apply Sub_ImpR. apply IHsubformula. apply H0.
Qed.

Fixpoint subformulas_dup (A : o) : list o :=
    match A with
    | Atom p n => Atom p n :: nil
    | TT => TT :: nil
    | FF => FF :: nil
    | AndP A B => (AndP A B) :: subformulas_dup A ++ subformulas_dup B
    | AndN A B => (AndN A B) :: subformulas_dup A ++ subformulas_dup B
    | Or A B => (Or A B) :: subformulas_dup A ++ subformulas_dup B
    | Imp A B => (Imp A B) :: subformulas_dup A ++ subformulas_dup B
    end
.

Definition subformulas (A: o) : list o :=
    nodup o_eq_dec (subformulas_dup A).

Lemma subformula_iff_subformulas_dup :
    forall (A B: o), subformula A B <-> In A (subformulas_dup B).
Proof.
    intros. split.
    - intros. induction B ; simpl.
        + inversion H. left. reflexivity.
        + inversion H. left. reflexivity.
        + inversion H. left. reflexivity.
        + inversion H ; subst.
            apply in_eq.
            apply in_cons. apply in_or_app. left. apply IHB1. apply H2.
            apply in_cons. apply in_or_app. right. apply IHB2. apply H2.
        + inversion H ; subst.
            apply in_eq.
            apply in_cons. apply in_or_app. left. apply IHB1. apply H2.
            apply in_cons. apply in_or_app. right. apply IHB2. apply H2.
        + inversion H ; subst.
            apply in_eq.
            apply in_cons. apply in_or_app. left. apply IHB1. apply H2.
            apply in_cons. apply in_or_app. right. apply IHB2. apply H2.
        + inversion H ; subst.
            apply in_eq.
            apply in_cons. apply in_or_app. left. apply IHB1. apply H2.
            apply in_cons. apply in_or_app. right. apply IHB2. apply H2.
    - intros. induction B ; simpl in H.
        + destruct H. subst. apply Sub_Refl. inversion H.
        + destruct H. subst. apply Sub_Refl. inversion H.
        + destruct H. subst. apply Sub_Refl. inversion H.
        + destruct H. subst. apply Sub_Refl.
            apply in_app_or in H. inversion H.
            apply Sub_AndPL. apply IHB1. apply H0.
            apply Sub_AndPR. apply IHB2. apply H0.
        + destruct H. subst. apply Sub_Refl.
            apply in_app_or in H. inversion H.
            apply Sub_AndNL. apply IHB1. apply H0.
            apply Sub_AndNR. apply IHB2. apply H0.
        + destruct H. subst. apply Sub_Refl.
            apply in_app_or in H. inversion H.
            apply Sub_OrL. apply IHB1. apply H0.
            apply Sub_OrR. apply IHB2. apply H0.
        + destruct H. subst. apply Sub_Refl.
            apply in_app_or in H. inversion H.
            apply Sub_ImpL. apply IHB1. apply H0.
            apply Sub_ImpR. apply IHB2. apply H0.
Qed.

Lemma subformula_iff_subformulas :
    forall (A B: o), subformula A B <-> In A (subformulas B).
Proof.
    intros. unfold subformulas. rewrite nodup_In. apply subformula_iff_subformulas_dup.
Qed. 

Definition subformulas_positive (A: o) : list o :=
    filter positive_b (subformulas A)
.

Lemma subformulas_positive_correct :
    forall (A B: o), In A (subformulas_positive B) ->
        positive A /\ subformula A B.
Proof.
    intros. unfold subformulas_positive in H. apply filter_In in H.
    destruct H. split. apply positive_b_iff in H0. apply H0.
    apply subformula_iff_subformulas. apply H.
Qed.


Definition subformulas_negative (A: o) : list o :=
    filter negative_b (subformulas A)
.

Lemma subformulas_negative_correct :
    forall (A B: o), In A (subformulas_negative B) ->
        negative A /\ subformula A B.
Proof.
    intros. unfold subformulas_negative in H. apply filter_In in H.
    destruct H. split. apply negative_b_iff in H0. apply H0.
    apply subformula_iff_subformulas. apply H.
Qed.


Definition subformulas_permeable (A: o) : list o :=
    filter permeable_b (subformulas A)
.

Lemma subformulas_permeable_correct :
    forall (A B: o), In A (subformulas_permeable B) ->
        permeable A /\ subformula A B.
Proof.
    intros. unfold subformulas_permeable in H. apply filter_In in H.
    destruct H. split. apply permeable_b_iff in H0. apply H0.
    apply subformula_iff_subformulas. apply H.
Qed.