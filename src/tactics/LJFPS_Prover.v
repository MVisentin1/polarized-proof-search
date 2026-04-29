From Stdlib Require Import List.

From CARVe Require Import contexts.list algebras.structural.

From LJF Require Import LJFPS_Rules SharedLogic.

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
    | Impl _ _ => apply Neg_imp
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

(* Solves a has_entry carve subgoal*)
Ltac T_has_entry := solve [
    lazymatch goal with
    | [|- has_entry _ _] => repeat (apply in_eq || apply in_cons)
    end]
.

Ltac T_noloop con formula focused  paths := 
  lazymatch paths with
  | nil => idtac
  | (?con', ?formula', ?focused') :: ?rest =>
    lazymatch con' with
    | con =>
        lazymatch formula' with
        | formula =>
            lazymatch focused' with
            | focused => fail "T_no_loop called on already processed loop"
            | _ => T_noloop con formula focused rest
            end
        | _ => T_noloop con formula focused rest
        end
    | _ => T_noloop con formula focused rest
    end
  end
.

(* Stubs for circular dependencies *)
Ltac T_bct paths := fail "T_bct: not yet defined".
Ltac T_ept paths := fail "T_ept: not yet defined".
Ltac T_decide_right paths := fail "T_decide_right: not yet defined".
Ltac T_decide_left paths := fail "T_decide_left: not yet defined".
Ltac T_lfc paths := fail "T_lfc: not yet defined".
Ltac T_rfc paths := fail "T_rfc: not yet defined".


(* T_rfc goes through the Right focus phase *)
Ltac T_rfc paths ::=
  lazymatch goal with
  | [|- rfc _ ?b] => let b' := (eval hnf in b) in
    lazymatch b' with
    (* Right focus on positive atom*)
    | Atom Pos _ => apply rfc_I_r ; [> T_positive | T_atomic | T_has_entry]

    (* Right focus on TT*)
    | TT => apply rfc_R_True

    (* Right focus on positive conjunction *)
    | AndP _ _ => apply rfc_R_AndP ; [> T_rfc paths | T_rfc paths]

    (* Right focus on disjunction. Try proving B1, if it fails, try proving B2 *)
    | Or _ _ => solve [apply rfc_R_Or_1 ; [> T_rfc paths]] 
      || (apply rfc_R_Or_2 ; [> T_rfc paths])

    (* Right focus on negative formula ends right-focus phase, transitions to bct*)
    | _ => apply rfc_R_r ; [> T_negative | T_bct paths]
  end
end
.

(* T_lfc goes through the Left Focus phase*)
Ltac  T_lfc paths ::=
  lazymatch goal with
  | [|- lfc _ ?b _] => let b' := (eval hnf in b) in
    lazymatch b' with
    (* Left focus on negative atom*)
    | Atom Neg _ => apply lfc_I_l ; [> T_negative | T_atomic ]

    (* Left focus on negative conjunction. Try proving B1, if it fails, try proving B2 *)
    | AndN _ _ => solve [apply lfc_L_AndN_1 ; [> T_bracketable | T_lfc paths ]]
      || (apply lfc_L_AndN_2 ; [> T_bracketable | T_lfc paths ])

    (* Left focus on implication *)
    | Impl _ _ => apply lfc_L_Impl ; [> T_bracketable | T_rfc paths | T_lfc paths]

    (* Left focus on a positive formula, ends left-focus phase, leaves a ufc subgoal *)
    | _ => apply lfc_R_l ; [> T_bracketable | T_positive | T_ept paths]
    end
  end
.

(* T_bct goes through the bracketing phase *)
Ltac T_bct paths ::=
  lazymatch goal with
  | [|- bct _ _ ?k ] => let k' := (eval hnf in k) in
    lazymatch k' with
    | AndN _ _ => apply bct_R_AndN ; [> T_bct paths | T_bct paths]
    | Impl _ _ => apply bct_R_Impl ; [> T_bct paths]
    | _ => apply bct_R_box ; [> T_bracketable | T_ept paths]
    end
  end
.

(* T_ufc_empty goes through the emptying phase*)
Ltac T_ept paths ::=
  lazymatch goal with
  | [|- ept _ ?c _] => let c' := (eval hnf in c) in
    lazymatch c' with
    | nil => T_decide_right paths
    | cons ?a _ => let a' := (eval hnf in a) in
      lazymatch a' with
      | AndP _ _ => apply ept_L_AndP ; [> T_bracketable | T_ept paths]
      | Or _ _ => apply ept_L_Or ; [> T_bracketable | T_ept paths | T_ept paths]
      | TT => apply ept_L_True ; [> T_bracketable | T_ept paths]
      | FF => apply ept_L_False ; [> T_bracketable]
      | _ => apply ept_L_box ; [> T_bracketable | T_permeable | T_ept paths]
      end
    end
  end
.

(* T_decide_right tries right focusing, if it fails or we cannot, we left focus instead *)
Ltac T_decide_right paths ::=
  lazymatch goal with
  | [|- ept _ _ ?k] => let k' := (eval hnf in k) in
    (* If k is positive, we right focus *)
    (* If k is negative, or right focusing fails, we left focus *)
    solve [apply ept_R_f ; [> T_positive | T_rfc paths]] 
    || T_decide_left paths
  end
.

(*Arg con : structural left to be processed*)
(*Arg formula : right side formula*)
Ltac T_decide_left_private cont formula paths :=
  let cont' := (eval hnf in cont) in
  let formula' := (eval hnf in formula) in
  lazymatch cont' with
    | nil => fail "T_decide_left: ran out of assumption to focus on"
    (* If b is negative, we left focus on it *)
    (* If b is positive, or left focusing on b fail, we go to next entry *)
    | cons (?b, tt) ?rest => let b' := (eval hnf in b) in
      let updated_paths := constr:((cont', formula', b') :: paths) in
      solve [
        T_noloop cont' formula' b' paths ; 
        apply ept_L_f with (N := b') ; 
        [> T_bracketable | T_negative | T_has_entry | T_lfc updated_paths]] 
        || T_decide_left_private rest formula' paths
  end
.

(* T_decide_left pattern matches on the goal to find initial input to T_decide_left_private *)
Ltac T_decide_left paths ::=
  lazymatch goal with
  | [|- ept ?c nil ?k] => T_decide_left_private c k paths
  end
.

Ltac T_solve :=
  intros ;
  let paths := constr:(@nil (list (o * unit) * o * o)) in
  solve [lazymatch goal with
  | [|- lfc _ _ _] => T_lfc paths
  | [|- rfc _ _] => T_rfc paths
  | [|- bct _ _ _] => T_bct paths
  | [|- ept _ _ _] => T_ept paths
  | _ => fail "T_solve: goal is not a LJFPS sequent"
  end]
.