From Stdlib Require Import List.
From LJF Require Import SharedLogic LJFC_Rules.

Inductive sequent : Type :=
| SbctC : forall {C L D}, bctC C L D -> sequent
| SeptC : forall {C L D}, eptC C L D -> sequent
| SlfcC : forall {C N K}, lfcC C N K -> sequent
| SrfcC : forall {C P}, rfcC C P   -> sequent
.

Definition phase_rank (s : sequent) : nat :=
    match s with
    | SbctC _ => 1
    | SeptC _ => 0
    | SlfcC _ => 3
    | SrfcC _ => 2
    end
.







