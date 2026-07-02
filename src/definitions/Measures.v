From Stdlib Require Import List Lia.
From LJF Require Import SharedLogic.

Fixpoint osize (A : o) : nat :=
    match A with
    | Atom _ _ => 1
    | TT       => 1
    | FF       => 1
    | AndP A B => 1 + osize A + osize B
    | AndN A B => 1 + osize A + osize B
    | Or   A B => 1 + osize A + osize B
    | Imp  A B => 1 + osize A + osize B
    end
.

Lemma osize_positive :
    forall (A : o), 0 < osize A.
Proof.
    intros. destruct A ; simpl ; lia.
Qed.

Fixpoint octx_size (L : octx) : nat :=
    match L with
    | nil      => 0
    | A :: L'  => osize A + octx_size L'
    end
.

