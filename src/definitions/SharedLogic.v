From Stdlib Require Import List.
From Equations Require Import Equations.
From Stdlib Require Import PeanoNat.


Variant polarity : Type :=
| Pos : polarity
| Neg : polarity.

Inductive o : Type :=
| Atom  : polarity -> nat -> o   
| TT  : o
| FF : o
| AndP  : o -> o -> o
| AndN  : o -> o -> o
| Or    : o -> o -> o
| Imp  : o -> o -> o.

Variant atomic : o -> Prop :=
  | Is_atom : forall p n, atomic (Atom p n)
.

Variant positive : o -> Prop :=
  | Pos_atom : forall n, positive (Atom Pos n)
  | Pos_true : positive TT
  | Pos_false : positive FF
  | Pos_and : forall A B, positive (AndP A B)
  | Pos_or : forall A B, positive (Or A B)
.

Variant negative : o -> Prop :=
  | Neg_atom : forall n, negative (Atom Neg n)
  | Neg_and : forall A B, negative (AndN A B)
  | Neg_imp : forall A B, negative (Imp A B)
.

Variant bracketable : o -> Prop :=
  | Bracketable_pos : forall D, positive D -> bracketable D
  | Bracketable_neg_atom : forall D, atomic D -> negative D -> bracketable D
.

Variant permeable : o -> Prop :=
  | Permeable_neg : forall C, negative C -> permeable C
  | Permeable_pos_atom : forall C, atomic C -> positive C -> permeable C
.

Notation sctx := (list o).
Notation lctx := (list o).
Notation octx := (list o).

Definition permeable_ctx (C : sctx) : Prop := Forall permeable C.


