From Stdlib Require Import List.

From LJF Require Import SharedLogic Decidability Predicates.

Inductive subformula (A: o) : o -> Prop :=
| Sub_Refl  : subformula A A
| Sub_AndPL : forall B C, subformula A B -> subformula A (AndP B C)
| Sub_AndPR : forall B C, subformula A C -> subformula A (AndP B C)
| Sub_AndNL : forall B C, subformula A B -> subformula A (AndN B C)
| Sub_AndNR : forall B C, subformula A C -> subformula A (AndN B C)
| Sub_OrL : forall B C, subformula A B -> subformula A (Or B C)
| Sub_OrR : forall B C, subformula A C -> subformula A (Or B C)
| Sub_ImpL : forall B C, subformula A B -> subformula A (Imp B C)
| Sub_ImpR : forall B C, subformula A C -> subformula A (Imp B C)
.

Lemma subformula_trans :
    forall {A B C : o},
        subformula A B -> subformula B C -> subformula A C.
Proof.
    intros A B C H0 H1. induction H1.
    - apply H0.
    - apply Sub_AndPL. apply IHsubformula.
    - apply Sub_AndPR. apply IHsubformula.
    - apply Sub_AndNL. apply IHsubformula.
    - apply Sub_AndNR. apply IHsubformula. 
    - apply Sub_OrL. apply IHsubformula. 
    - apply Sub_OrR. apply IHsubformula.
    - apply Sub_ImpL. apply IHsubformula.
    - apply Sub_ImpR. apply IHsubformula.
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
            apply in_cons. apply in_or_app. left. apply IHB1. apply H1.
            apply in_cons. apply in_or_app. right. apply IHB2. apply H1.
        + inversion H ; subst.
            apply in_eq.
            apply in_cons. apply in_or_app. left. apply IHB1. apply H1.
            apply in_cons. apply in_or_app. right. apply IHB2. apply H1.
        + inversion H ; subst.
            apply in_eq.
            apply in_cons. apply in_or_app. left. apply IHB1. apply H1.
            apply in_cons. apply in_or_app. right. apply IHB2. apply H1.
        + inversion H ; subst.
            apply in_eq.
            apply in_cons. apply in_or_app. left. apply IHB1. apply H1.
            apply in_cons. apply in_or_app. right. apply IHB2. apply H1.
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

Definition subformulas (A: o) : list o :=
    nodup o_eq_dec (subformulas_dup A).

Lemma subformula_iff_subformulas :
    forall (A B: o), subformula A B <-> In A (subformulas B).
Proof.
    intros. unfold subformulas. rewrite nodup_In. apply subformula_iff_subformulas_dup.
Qed. 

Lemma subformulas_trans :
    forall {A B C : o},
        In A (subformulas B) -> In B (subformulas C) -> In A (subformulas C).
Proof.
    intros.
    apply subformula_iff_subformulas in H.
    apply subformula_iff_subformulas in H0.
    apply subformula_iff_subformulas.
    eapply subformula_trans. apply H. apply H0.
Qed.