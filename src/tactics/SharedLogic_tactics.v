From LJF Require Import SharedLogic.

Ltac T_atomic := solve [
  lazymatch goal with
  | [|- atomic ?a] => let a' := (eval hnf in a) in
    lazymatch a' with 
    | Atom _ _ => apply Is_atom
    end
  end]
.

Ltac T_positive := solve [
  lazymatch goal with
  | [|- positive ?a] => let a' := (eval hnf in a) in
    lazymatch a' with
    | Atom Pos _ => apply Pos_atom
    | TT => apply Pos_true
    | FF => apply Pos_false
    | AndP _ _ => apply Pos_and
    | Or _ _ => apply Pos_or
    end 
  end]
.

Ltac T_negative := solve [
  lazymatch goal with
  | [|- negative ?a] => let a' := (eval hnf in a) in
    lazymatch a' with
    | Atom Neg _ => apply Neg_atom
    | AndN _ _ => apply Neg_and
    | Imp _ _ => apply Neg_imp
    end
  end]
.

Ltac T_permeable := solve [
  lazymatch goal with
  | [|- permeable ?a ] => let a' := (eval hnf in a) in
    lazymatch a' with
    | Atom Pos _ => apply Permeable_pos_atom; [> apply Is_atom | apply Pos_atom]
    | _ => apply Permeable_neg; T_negative
    end
  end]
.

Ltac T_bracketable := solve [
  lazymatch goal with
  | [|- bracketable ?a ] => let a' := (eval hnf in a) in
    lazymatch a' with
    | Atom Neg _ => apply Bracketable_neg_atom ; [> apply Is_atom | apply Neg_atom ]
    | _ => apply Bracketable_pos ; T_positive
    end
  end]
.