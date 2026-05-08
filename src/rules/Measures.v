From Equations Require Import Equations.
From Stdlib Require Import List.

From CARVe Require Import contexts.list.   
From CARVe Require algebras.dill algebras.structural.  
From LJF Require Import SharedLogic.

Equations osize (A : o) : nat :=
  osize (Atom _ _) := 1;
  osize TT         := 1;
  osize FF         := 1;
  osize (AndP A B) := 1 + osize A + osize B;
  osize (AndN A B) := 1 + osize A + osize B;
  osize (Or   A B) := 1 + osize A + osize B;
  osize (Impl A B) := 1 + osize A + osize B
.

Equations octx_size (O: octx) : nat :=
    octx_size nil := 0;
    octx_size (A :: O') := osize A + octx_size O'
.

