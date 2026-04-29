From Stdlib Require Import List.

From CARVe Require Import contexts.list.
From CARVe Require Import algebras.dill.

From LJF Require Import LJF4_Rules SharedLogic.

Ltac T_exh := solve [
    lazymatch goal with
    | [|- exh _ ] => simpl; repeat split; try (apply halo); try (apply halz); try (apply I)
    end]
.

(* Use when we know what we are looking  for, not for making decisions *)
Ltac T_has_entry := solve [
    lazymatch goal with
    | [|- has_entry _ _] =>
        solve [repeat (apply in_eq || apply in_cons)]
    end]
.

Ltac T_upd_rel_ex := solve [
  lazymatch goal with
  | [|- upd_rel_ex _ _ _ _] => eexists; constructor
  end]
.