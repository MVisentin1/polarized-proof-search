From Stdlib Require Import List.

From CARVe Require Import contexts.list.
From CARVe Require Import algebras.dill.


From LJF Require Import SharedLogic. 

(* DILL context -> right side formula*)
Inductive bct4 : dctx -> o -> Prop :=
| bct4_R_box :
  forall {C: dctx} {D: o},
    bracketable D ->
    ept4 C D ->
    bct4 C D
| bct4_R_AndN :
  forall {C: dctx} {B1 B2: o},
    bct4 C B1 ->
    bct4 C B2 ->
    bct4 C (AndN B1 B2)
| bct4_R_Impl :
  forall {C : dctx} {B1 B2: o},
    bct4 ((B1, one) :: C) B2 ->
    bct4 C (Impl B1 B2)
(* DILL context -> right side formula*)
with ept4 : dctx -> o -> Prop :=
| ept4_L_f :
  forall {C: dctx} (N : o) {K : o},
    exh C ->
    has_entry C (N, omega) ->
    bracketable K ->
    negative N ->
    lfc4 C N K ->
    ept4 C K
| ept4_R_f :
  forall {C: dctx} {P: o},
    exh C ->
    positive P ->
    rfc4 C P ->
    ept4 C P
| ept4_L_box :
  forall {C C1 : dctx} (B : o) {K : o},
    has_entry C (B, one) ->
    upd_rel_ex C (B, one) (B, omega) C1 ->
    bracketable K ->
    permeable B ->
    ept4 C1 K ->
    ept4 C K
| ept4_L_AndP :
  forall {C C1: dctx} (B1 B2 : o) {K: o},
    has_entry C ((AndP B1 B2), one) ->
    upd_rel_ex C ((AndP B1 B2), one) ((AndP B1 B2), zero) C1 ->
    bracketable K -> 
    ept4 ((B2, one) :: (B1, one) :: C1) K ->
    ept4 C K
| ept4_L_Or :
  forall {C C1: dctx} (B1 B2 : o)  {K: o},
    has_entry C ((Or B1 B2), one) ->
    upd_rel_ex C ((Or B1 B2), one) ((Or B1 B2), zero) C1 ->
    bracketable K ->
    ept4 ((B1, one) :: C1) K ->
    ept4 ((B2, one) :: C1) K ->
    ept4 C K
| ept4_L_True :
  forall {C C1: dctx} {K: o},
    has_entry C (TT, one) ->
    upd_rel_ex C (TT, one) (TT, zero) C1 ->
    bracketable K ->
    ept4 C1 K ->
    ept4 C K
| ept4_L_False :
  forall {C: dctx}  {K: o},
    has_entry C (FF, one) ->
    bracketable K -> 
    ept4 C K

(* DILL context -> focused formula -> right side formula *)
with lfc4 : dctx -> o -> o -> Prop :=
| lfc4_R_l :
  forall {C : dctx} {P : o}  {K : o},
    exh C ->
    bracketable K ->
    positive P ->
    ept4 ((P, one) :: C) K ->
    lfc4 C P K
| lfc4_I_l :
  forall {C: dctx} {N : o},
    exh C ->
    negative N ->
    atomic N ->
    lfc4 C N N
| lfc4_L_AndN_1 :
  forall {C: dctx} {B1 B2 : o}  {K : o},
    exh C ->
    bracketable K ->
    lfc4 C B1 K ->
    lfc4 C (AndN B1 B2) K
| lfc4_L_AndN_2 :
  forall {C: dctx} {B1 B2 : o}  {K : o},
    exh C ->
    bracketable K ->
    lfc4 C B2 K ->
    lfc4 C (AndN B1 B2) K
| lfc4_L_Impl :
  forall {C: dctx} {B1 B2 : o}  {K : o},
    exh C ->
    bracketable K ->
    rfc4 C B1 ->
    lfc4 C B2 K ->
    lfc4 C (Impl B1 B2) K
(* DILL context -> focused formula*)
with rfc4 : dctx -> o -> Prop :=
| rfc4_R_r :
  forall {C: dctx} {N: o},
    exh C ->
    negative N ->
    bct4 C N ->
    rfc4 C N
| rfc4_I_r :
  forall {C: dctx} {P: o},
    exh C ->
    has_entry C (P, omega) ->
    positive P ->
    atomic P ->
    rfc4 C P
| rfc4_R_AndP :
  forall {C: dctx} {B1 B2: o},
    exh C ->
    rfc4 C B1 ->
    rfc4 C B2 ->
    rfc4 C (AndP B1 B2)
| rfc4_R_Or_1 :
  forall {C: dctx} {B1 B2: o},
    exh C ->
    rfc4 C B1 ->
    rfc4 C (Or B1 B2)
| rfc4_R_Or_2 :
  forall {C: dctx} {B1 B2: o},
    exh C ->
    rfc4 C B2 ->
    rfc4 C (Or B1 B2)
| rfc4_R_True :
  forall {C: dctx},
    exh C ->
    rfc4 C TT
.