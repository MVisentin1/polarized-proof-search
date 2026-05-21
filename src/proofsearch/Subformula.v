From Stdlib Require Import List.
From Equations Require Import Equations.

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

Equations subformulas (A : o) : list o :=
  subformulas (Atom p n) := Atom p n :: nil;
  subformulas TT := TT :: nil;
  subformulas FF := FF :: nil;
  subformulas (AndP A B) := (AndP A B) :: subformulas A ++ subformulas B;
  subformulas (AndN A B) := (AndN A B) :: subformulas A ++ subformulas B;
  subformulas (Or A B) := (Or A B) :: subformulas A ++ subformulas B;
  subformulas (Imp A B) := (Imp A B) :: subformulas A ++ subformulas B
.

Lemma subformulas_iff : 
    forall (A B: o), In A (subformulas B) <-> subformula A B.
Proof.
    intros. split.
    - intros. funelim (subformulas B).
        + symmetry in Heqcall. rewrite Heqcall in H. 
            destruct H. 
            subst. apply Sub_Refl.
            inversion H.
        + symmetry in Heqcall. rewrite Heqcall in H.
            destruct H. 
            subst. apply Sub_Refl.
            inversion H.
        + symmetry in Heqcall. rewrite Heqcall in H.
            destruct H. 
            subst. apply Sub_Refl.
            inversion H.
        + symmetry in Heqcall. rewrite Heqcall in H1.
            destruct H1. subst. apply Sub_Refl.
            apply in_app_or in H1. inversion H1.
            apply Sub_AndPL. apply H. apply H2.
            apply Sub_AndPR. apply H0. apply H2.
        + symmetry in Heqcall. rewrite Heqcall in H1.
            destruct H1. subst. apply Sub_Refl.
            apply in_app_or in H1. inversion H1.
            apply Sub_AndNL. apply H. apply H2.
            apply Sub_AndNR. apply H0. apply H2.
        + symmetry in Heqcall. rewrite Heqcall in H1.
            destruct H1. subst. apply Sub_Refl.
            apply in_app_or in H1. inversion H1.
            apply Sub_OrL. apply H. apply H2.
            apply Sub_OrR. apply H0. apply H2.
        + symmetry in Heqcall. rewrite Heqcall in H1.
            destruct H1. subst. apply Sub_Refl.
            apply in_app_or in H1. inversion H1.
            apply Sub_ImpL. apply H. apply H2.
            apply Sub_ImpR. apply H0. apply H2.
    - intros. funelim (subformulas B).
        + inversion H. apply in_eq.
        + inversion H. apply in_eq.
        + inversion H. apply in_eq.
        + inversion H1 ; subst.
            apply in_eq.
            apply in_cons. apply in_or_app. left. apply H. apply H4.
            apply in_cons. apply in_or_app. right. apply H0. apply H4.
        + inversion H1 ; subst.
            apply in_eq.
            apply in_cons. apply in_or_app. left. apply H. apply H4.
            apply in_cons. apply in_or_app. right. apply H0. apply H4.
        + inversion H1 ; subst.
            apply in_eq.
            apply in_cons. apply in_or_app. left. apply H. apply H4.
            apply in_cons. apply in_or_app. right. apply H0. apply H4.
        + inversion H1 ; subst.
            apply in_eq.
            apply in_cons. apply in_or_app. left. apply H. apply H4.
            apply in_cons. apply in_or_app. right. apply H0. apply H4.
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



