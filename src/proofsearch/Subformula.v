From Stdlib Require Import List.

From LJF Require Import SharedLogic SharedLogic_tactics.

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

Fixpoint subformulas (A : o) : list o :=
    match A with
    | Atom p n => Atom p n :: nil
    | TT => TT :: nil
    | FF => FF :: nil
    | AndP A B => (AndP A B) :: subformulas A ++ subformulas B
    | AndN A B => (AndN A B) :: subformulas A ++ subformulas B
    | Or A B => (Or A B) :: subformulas A ++ subformulas B
    | Imp A B => (Imp A B) :: subformulas A ++ subformulas B
    end
.

Lemma subformulas_iff :
    forall (A B: o), In A (subformulas B) <-> subformula A B.
Proof.
    intros. split.
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
Qed.

Definition positive_b (A: o) : bool :=
    match A with
    | Atom Pos _ => true
    | TT => true
    | FF => true
    | AndP _ _ => true
    | Or _ _ => true
    | _ => false
    end
.

Lemma positive_b_iff : forall A, positive_b A = true <-> positive A.
Proof.
    intros. split.
    - intros. destruct A ; try (inversion H) ; try (T_positive).
        destruct p. T_positive. inversion H1.
    - intros. destruct A ; simpl ; try reflexivity ;
        try (inversion H; inversion H0; inversion H0).
        destruct p. reflexivity. inversion H.
Qed.

Definition negative_b (A: o) : bool :=
    match A with
    | Atom Neg _ => true
    | AndN _ _ => true
    | Imp _ _ => true
    | _ => false
    end
.

Lemma negative_b_iff : forall A, negative_b A = true <-> negative A.
Proof.
    intros. split.
    - intros. destruct A ; try (inversion H) ; try (T_negative).
        destruct p. inversion H1. T_negative.
    - intros. destruct A ; simpl ; try reflexivity ;
        try (inversion H; inversion H0; inversion H0).
        destruct p. inversion H. reflexivity.
Qed.

Definition permeable_b (A : o) : bool :=
    match A with
    | Atom _ _ => true
    | AndN _ _   => true
    | Imp _ _   => true
    | _          => false
    end
.

Lemma permeable_b_iff : forall A, permeable_b A = true <-> permeable A.
Proof.
    intros. split.
    - intros. destruct A ; try (inversion H) ; try (T_permeable).
        destruct p. T_permeable. T_permeable.
    - intros. destruct A ; simpl ; try reflexivity ;
        try (inversion H; inversion H0; inversion H0).
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
    apply subformulas_iff. apply H.
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
    apply subformulas_iff. apply H.
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
    apply subformulas_iff. apply H.
Qed.