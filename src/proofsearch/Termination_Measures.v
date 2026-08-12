From Stdlib Require Import List PeanoNat.
From LJF Require Import Sequents Measures.

Definition phase_ranking (S: sequent) : nat :=
    match S with
    | Sbct _ _ K => 1
    | Sept _ L _ => 0
    | Slfc _ N _ => 3
    | Srfc _ K   => 2
    end
.

Definition phase_measure (S: sequent) : nat :=
    match S with
    | Sbct _ _ K => osize K
    | Sept _ L _ => octx_size L
    | Slfc _ N _ => osize N
    | Srfc _ K   => osize K
    end
.