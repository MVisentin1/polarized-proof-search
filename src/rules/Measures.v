From Equations Require Import Equations.
From Stdlib Require Import List.
From LJF Require Import SharedLogic.

Equations osize (A : o) : nat :=
  osize (Atom _ _) := 1;
  osize TT         := 1;
  osize FF         := 1;
  osize (AndP A B) := 1 + osize A + osize B;
  osize (AndN A B) := 1 + osize A + osize B;
  osize (Or   A B) := 1 + osize A + osize B;
  osize (Imp A B) := 1 + osize A + osize B
.

Equations octx_size (L: octx) : nat :=
    octx_size nil := 0;
    octx_size (A :: L') := osize A + octx_size L'
.

