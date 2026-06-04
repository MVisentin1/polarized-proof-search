From Stdlib Require Import List PeanoNat.
From LJF Require Import SharedLogic.

Lemma polarity_eq_dec : forall p1 p2 : polarity, {p1 = p2} + {p1 <> p2}.
Proof. decide equality. Defined
.

Lemma o_eq_dec : forall A B : o, {A = B} + {A <> B}.
Proof.
  decide equality.
  - apply Nat.eq_dec.
  - apply polarity_eq_dec.
Defined.

Lemma permeable_dec : forall A : o, {permeable A} + {~ permeable A}.
Proof.
    intros. destruct A.
    - destruct p.
        + left. apply Permeable_pos_atom. apply Is_atom. apply Pos_atom.
        + left. apply Permeable_neg. apply Neg_atom.
    - right. intro. inversion H. inversion H0. inversion H0.
    - right. intro. inversion H. inversion H0. inversion H0.
    - right. intro. inversion H. inversion H0. inversion H0.
    - left. apply Permeable_neg. apply Neg_and.
    - right. intro. inversion H. inversion H0. inversion H0.
    - left. apply Permeable_neg. apply Neg_imp.
Defined.

Lemma permeable_ctx_dec : forall (C: sctx), {permeable_ctx C} + {~ permeable_ctx C}.
Proof.
    intros.
    apply Forall_dec.
    apply permeable_dec.
Defined.
    