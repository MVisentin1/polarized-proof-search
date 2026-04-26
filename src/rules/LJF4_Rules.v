From Stdlib Require Import List.

From CARVe Require Import contexts.list algebras.dill.

Global Arguments upd_rel_ex  {R A} _ _ _ _.

From LJF Require Import SharedLogic. 

Inductive bct : ctx -> o -> Prop :=
| bct_R_box :
  forall {C: ctx} {D: o},
    bracketable D ->
    ept C D ->
    bct C D
| bct_R_AndN :
  forall {C: ctx} {B1 B2: o},
    bct C B1 ->
    bct C B2 ->
    bct C (AndN B1 B2)
| bct_R_Impl :
  forall {C : ctx} {B1 B2: o},
    bct ((B1, one) :: C) B2 ->
    bct C (Impl B1 B2)

with ept : ctx -> o -> Prop :=
| ept_L_f :
  forall {C: ctx} {N : o} {K : o},
    exh C ->
    has_entry C (N, omega) ->
    negative N ->
    lfc C N K ->
    ept C K
| ept_R_f :
  forall {C: ctx} {P: o},
    exh C ->
    positive P ->
    rfc C P ->
    ept C P
| ept_L_box :
  forall {C C1 : ctx} {B : o} {K : o},
    upd_rel_ex C (B, one) (B, omega) C1 ->
    permeable B ->
    ept C1 K ->
    ept C K
| ept_L_AndP :
  forall {C C1: ctx} {B1 B2 : o} {K: o},
    has_entry C ((AndP B1 B2), one) ->
    upd_rel_ex C ((AndP B1 B2), one) ((AndP B1 B2), zero) C1 ->
    ept ((B1, one) :: (B2, one) :: C1) K ->
    ept C K
| ept_L_Or :
  forall {C C1: ctx} {B1 B2 : o}  {K: o},
    has_entry C ((Or B1 B2), one) ->
    upd_rel_ex C ((Or B1 B2), one) ((Or B1 B2), zero) C1 ->
    ept ((B1, one) :: C1) K ->
    ept ((B2, one) :: C1) K ->
    ept C K
| ept_L_True :
  forall {C C1: ctx}  {K: o},
    has_entry C (TT, one) ->
    upd_rel_ex C (TT, one) (TT, zero) C1 ->
    ept C1 K ->
    ept C K
| ept_L_False :
  forall {C: ctx}  {K: o},
    has_entry C (FF, one) ->
    ept C K

(* First o for focused assumption, second o for conclusion K *)
with lfc : ctx -> o -> o -> Prop :=
| lfc_R_l :
  forall {C : ctx} {P : o}  {K : o},
    exh C ->
    positive P ->
    ept ((P, one) :: C) K ->
    lfc C P K
| lfc_I_l :
  forall {C: ctx} {N : o},
    exh C ->
    negative N ->
    atomic N ->
    lfc C N N
| lfc_L_AndN_1 :
  forall {C: ctx} {B1 B2 : o}  {K : o},
    exh C ->
    lfc C B1 K ->
    lfc C (AndN B1 B2) K
| lfc_L_AndN_2 :
  forall {C: ctx} {B1 B2 : o}  {K : o},
    exh C ->
    lfc C B2 K ->
    lfc C (AndN B1 B2) K
| lfc_L_Impl :
  forall {C: ctx} {B1 B2 : o}  {K : o},
    exh C ->
    rfc C B1 ->
    lfc C B2 K ->
    lfc C (Impl B1 B2) K

with rfc : ctx -> o -> Prop :=
| rfc_R_r :
  forall {C: ctx} {N: o},
    exh C ->
    negative N ->
    bct C N ->
    rfc C N
| rfc_I_r :
  forall {C: ctx} {P: o},
    exh C ->
    has_entry C (P, omega) ->
    positive P ->
    atomic P ->
    rfc C P
| rfc_R_AndP :
  forall {C: ctx} {B1 B2: o},
    exh C ->
    rfc C B1 ->
    rfc C B2 ->
    rfc C (AndP B1 B2)
| rfc_R_Or_1 :
  forall {C: ctx} {B1 B2: o},
    exh C ->
    rfc C B1 ->
    rfc C (Or B1 B2)
| rfc_R_Or_2 :
  forall {C: ctx} {B1 B2: o},
    exh C ->
    rfc C B2 ->
    rfc C (Or B1 B2)
| rfc_R_True :
  forall {C: ctx},
    exh C ->
    rfc C TT
.