From Stdlib Require Import List.

From LJF Require Import LJFPS_Rules LJFPS_Prover SharedLogic.


Lemma Imp_trans_backward_chaining : forall (x y z : nat),
  let a := Atom Pos x in
  let b := Atom Neg y in
  let c := Atom Neg z in
  let C := a :: Imp a b :: Imp b c :: nil in
  lfc C (Imp b c) c.
Admitted.
Lemma Imp_trans_forward_chaining : forall (x y z : nat),
  let a := Atom Pos x in
  let b := Atom Pos y in
  let c := Atom Neg z in
  let C := a :: Imp a b :: Imp b c :: nil in
  lfc C (Imp a b) c.
Admitted.


Lemma Imp_trans : forall (x y z : nat),
  let a := Atom Neg x in
  let b := Atom Neg y in
  let c := Atom Neg z in
  let C := a :: Imp a b :: Imp b c :: nil in
  bct C nil c.
Admitted.