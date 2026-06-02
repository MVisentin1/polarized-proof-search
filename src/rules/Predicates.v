From Stdlib Require Import List.
From LJF Require Import SharedLogic SharedLogic_tactics.


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