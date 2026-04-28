From Stdlib Require Import List.

From CARVe Require Import contexts.list.
From CARVe Require Import algebras.dill.


From LJF Require Import SharedLogic.

Variant state : Type :=
  | Bracketed : state
  | Unbracketed : state
.
(*DILL context -> right side formula -> bracket state*)
Inductive ufcLJF : dctx -> o -> state -> Prop :=
| ufcLJF_L_f :
  forall {C: dctx} (N : o) {K : o},
    exh C ->
    has_entry C (N, omega) ->
    bracketable K ->
    negative N ->
    lfcLJF C N K ->
    ufcLJF C K Bracketed
| ufcLJF_R_f :
  forall {C: dctx} {P: o},
    exh C ->
    positive P ->
    rfcLJF C P ->
    ufcLJF C P Bracketed
| ufcLJF_L_box :
  forall {C C1: dctx} (B : o) {K : o},
    upd_rel_ex C (B, one) (B, omega) C1 ->
    bracketable K ->
    permeable B ->
    ufcLJF C1 K Bracketed ->
    ufcLJF C K Bracketed
| ufcLJF_L_box_star :
  forall {C C1: dctx} (B : o) {K : o},
    upd_rel_ex C (B, one) (B, omega) C1 ->
    permeable B ->
    ufcLJF C1 K Unbracketed ->
    ufcLJF C K Unbracketed
| ufcLJF_R_box :
  forall {C: dctx} {D: o},
    bracketable D ->
    ufcLJF C D Bracketed ->
    ufcLJF C D Unbracketed
| ufcLJF_L_AndP :
  forall {C C1: dctx} (B1 B2 : o) {K: o},
    has_entry C ((AndP B1 B2), one) ->
    upd_rel_ex C ((AndP B1 B2), one) ((AndP B1 B2), zero) C1 ->
    bracketable K ->
    ufcLJF ((B2, one) :: (B1, one) :: C1) K Bracketed ->
    ufcLJF C K Bracketed
| ufcLJF_L_AndP_star :
  forall {C C1: dctx} (B1 B2 : o) {K: o},
    has_entry C ((AndP B1 B2), one) ->
    upd_rel_ex C ((AndP B1 B2), one) ((AndP B1 B2), zero) C1 ->
    ufcLJF ((B2, one) :: (B1, one) :: C1) K Unbracketed->
    ufcLJF C K Unbracketed
| ufcLJF_R_AndN :
  forall {C: dctx} {B1 B2: o},
    ufcLJF C B1 Unbracketed ->
    ufcLJF C B2 Unbracketed->
    ufcLJF C (AndN B1 B2) Unbracketed
| ufcLJF_L_Or :
  forall {C C1: dctx} (B1 B2 : o)  {K: o},
    has_entry C ((Or B1 B2), one) ->
    upd_rel_ex C ((Or B1 B2), one) ((Or B1 B2), zero) C1 ->
    bracketable K ->
    ufcLJF ((B1, one) :: C1) K Bracketed ->
    ufcLJF ((B2, one) :: C1) K Bracketed ->
    ufcLJF C K Bracketed
| ufcLJF_L_Or_star :
  forall {C C1: dctx} (B1 B2 : o)  {K: o},
    has_entry C ((Or B1 B2), one) ->
    upd_rel_ex C ((Or B1 B2), one) ((Or B1 B2), zero) C1 ->
    ufcLJF ((B1, one) :: C1) K Unbracketed ->
    ufcLJF ((B2, one) :: C1) K Unbracketed ->
    ufcLJF C K Unbracketed
| ufcLJF_R_Impl :
  forall {C: dctx} {B1 B2: o},
    ufcLJF ((B1, one) :: C) B2 Unbracketed ->
    ufcLJF C (Impl B1 B2) Unbracketed
| ufcLJF_L_True :
  forall {C C1: dctx} {K: o},
    has_entry C (TT, one) ->
    upd_rel_ex C (TT, one) (TT, zero) C1 ->
    bracketable K ->
    ufcLJF C1 K Bracketed ->
    ufcLJF C K Bracketed
| ufcLJF_L_True_star :
  forall {C C1: dctx} {K: o},
    has_entry C (TT, one) ->
    upd_rel_ex C (TT, one) (TT, zero) C1 ->
    ufcLJF C1 K Unbracketed ->
    ufcLJF C K Unbracketed
| ufcLJF_L_False :
  forall {C: dctx} {K: o},
    has_entry C (FF, one) ->
    bracketable K ->
    ufcLJF C K Bracketed
| ufcLJF_L_False_star :
  forall {C: dctx} {K: o},
    has_entry C (FF, one) ->
    ufcLJF C K Unbracketed
(* DILL context -> focused formula -> right side formula*)
with lfcLJF : dctx -> o -> o -> Prop :=
| lfcLJF_R_l :
  forall {C : dctx} {P : o}  {K : o},
    exh C ->
    bracketable K ->
    positive P ->
    ufcLJF ((P, one) :: C) K Bracketed ->
    lfcLJF C P K
| lfcLJF_I_l :
  forall {C: dctx} {N : o},
    exh C ->
    negative N ->
    atomic N ->
    lfcLJF C N N
| lfcLJF_L_AndN_1 :
  forall {C: dctx} {B1 B2 : o}  {K : o},
    exh C ->
    bracketable K ->
    lfcLJF C B1 K ->
    lfcLJF C (AndN B1 B2) K
| lfcLJF_L_AndN_2 :
  forall {C: dctx} {B1 B2 : o}  {K : o},
    exh C ->
    bracketable K ->
    lfcLJF C B2 K ->
    lfcLJF C (AndN B1 B2) K
| lfcLJF_L_Impl :
  forall {C: dctx} {B1 B2 : o}  {K : o},
    exh C ->
    bracketable K ->
    rfcLJF C B1 ->
    lfcLJF C B2 K ->
    lfcLJF C (Impl B1 B2) K
(*DILL context -> focused formula*)
with rfcLJF : dctx -> o -> Prop :=
| rfcLJF_R_r :
  forall {C: dctx} {N: o},
    exh C ->
    negative N ->
    ufcLJF C N Unbracketed ->
    rfcLJF C N
| rfcLJF_I_r :
  forall {C: dctx} {P: o},
    exh C ->
    has_entry C (P, omega) ->
    positive P ->
    atomic P ->
    rfcLJF C P
| rfcLJF_R_AndP :
  forall {C: dctx} {B1 B2: o},
    exh C ->
    rfcLJF C B1 ->
    rfcLJF C B2 ->
    rfcLJF C (AndP B1 B2)
| rfcLJF_R_Or_1 :
  forall {C: dctx} {B1 B2: o},
    exh C ->
    rfcLJF C B1 ->
    rfcLJF C (Or B1 B2)
| rfcLJF_R_Or_2 :
  forall {C: dctx} {B1 B2: o},
    exh C ->
    rfcLJF C B2 ->
    rfcLJF C (Or B1 B2)
| rfcLJF_R_True :
  forall {C: dctx},
    exh C ->
    rfcLJF C TT
.