(* --- LJF Pure Logic Test (No External Imports) --- *)
Inductive formula : Type :=
| Atom : nat -> formula
| And : formula -> formula -> formula
| Or : formula -> formula -> formula.

(* Example usage *)
Definition test_formula := And (Atom 1) (Or (Atom 2) (Atom 3)).

Lemma atom_zero_is_formula : formula.
Proof.
  exact (Atom 0).
Qed.