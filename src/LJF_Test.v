From Stdlib Require Import List.

From CARVe Require Import contexts.list algebras.dill.
From VST.msl Require Import sepalg.

From LJF Require Import LJF_Logic.


Lemma True_proveable: (rfc nil True).
  apply rfc_R_True.
  T_exh.
Qed.


Lemma Fibonnaci_backward_chaining_example : forall (x y z : nat),
  let a := Atom Pos x in
  let b := Atom Neg y in
  let c := Atom Neg z in
  let C := (a, omega) :: (Impl a b, omega) :: (Impl b c, omega) :: nil in
  lfc C (Impl b c) c.
Proof. T_solve. Qed.

Lemma Fibonnaci_forward_chaining : forall (x y z : nat),
  let a := Atom Pos x in
  let b := Atom Pos y in
  let c := Atom Neg z in
  let C := (a, omega) :: (Impl a b, omega) :: (Impl b c, omega) :: nil in
  lfc C (Impl a b) c.
(*Proof. T_solve. Qed.  INFINITE LOOP*)
Admitted.

Lemma Fibonnaci : forall (x y z : nat),
  let a := Atom Neg x in
  let b := Atom Neg y in
  let c := Atom Neg z in
  let C := (a, omega) :: (Impl a b, omega) :: (Impl b c, omega) :: nil in
  ufc C (c) Unbracketed.
Proof. T_solve. Qed.
