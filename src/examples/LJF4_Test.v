From Stdlib Require Import List.

From CARVe Require Import contexts.list algebras.dill.

From LJF Require Import LJF4_Rules LJF4_Prover SharedLogic.


Lemma True_proveable: bct nil TT.
Proof. T_solve. Qed.


Lemma Impl_trans_backward_chaining : forall (x y z : nat),
  let a := Atom Pos x in
  let b := Atom Neg y in
  let c := Atom Neg z in
  let C := (a, omega) :: (Impl a b, omega) :: (Impl b c, omega) :: nil in
  lfc C (Impl b c) c.
Proof. T_solve. Qed.

Lemma Impl_trans_forward_chaining : forall (x y z : nat),
  let a := Atom Pos x in
  let b := Atom Pos y in
  let c := Atom Neg z in
  let C := (a, omega) :: (Impl a b, omega) :: (Impl b c, omega) :: nil in
  lfc C (Impl a b) c.
Proof. T_solve. Qed.


Lemma Impl_trans : forall (x y z : nat),
  let a := Atom Neg x in
  let b := Atom Neg y in
  let c := Atom Neg z in
  let C := (a, omega) :: (Impl a b, omega) :: (Impl b c, omega) :: nil in
  bct C c.
Proof. T_solve. Qed.
