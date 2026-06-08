From Stdlib Require Import List.
From LJF Require Import SharedLogic Pndctx LJFPS_Rules.

Inductive sequent : Type :=
| SbctC : forall {C: pndctx} {L: octx} {K: o}, bct C L K -> sequent
| SeptC : forall {C: pndctx} {L: octx} {K: o}, ept C L K -> sequent
| SlfcC : forall {C: pndctx} {N K: o}, lfc C N K -> sequent
| SrfcC : forall {C: pndctx} {K: o}, rfc C K   -> sequent
.

Definition phase_rank (s : sequent) : nat :=
    match s with
    | SbctC _ => 1
    | SeptC _ => 0
    | SlfcC _ => 3
    | SrfcC _ => 2
    end
.







