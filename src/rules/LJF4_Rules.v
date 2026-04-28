From Stdlib Require Import List.

From CARVe Require Import contexts.list.
From CARVe Require Import algebras.dill.


From LJF Require Import SharedLogic. 

Inductive bctLJF4 : dctx -> o -> Prop :=
| bctLJF4_R_box :
  forall {C: dctx} {D: o},
    bracketable D ->
    eptLJF4 C D ->
    bctLJF4 C D
| bctLJF4_R_AndN :
  forall {C: dctx} {B1 B2: o},
    bctLJF4 C B1 ->
    bctLJF4 C B2 ->
    bctLJF4 C (AndN B1 B2)
| bctLJF4_R_Impl :
  forall {C : dctx} {B1 B2: o},
    bctLJF4 ((B1, one) :: C) B2 ->
    bctLJF4 C (Impl B1 B2)
with eptLJF4 : dctx -> o -> Prop :=
| eptLJF4_L_f :
  forall {C: dctx} {N : o} {K : o},
    exh C ->
    has_entry C (N, omega) ->
    negative N ->
    lfcLJF4 C N K ->
    eptLJF4 C K
| eptLJF4_R_f :
  forall {C: dctx} {P: o},
    exh C ->
    positive P ->
    rfcLJF4 C P ->
    eptLJF4 C P
| eptLJF4_L_box :
  forall {C C1 : dctx} {B : o} {K : o},
    has_entry C (B, one) ->
    upd_rel_ex C (B, one) (B, omega) C1 ->
    permeable B ->
    eptLJF4 C1 K ->
    eptLJF4 C K
| eptLJF4_L_AndP :
  forall {C C1: dctx} {B1 B2 : o} {K: o},
    has_entry C ((AndP B1 B2), one) ->
    upd_rel_ex C ((AndP B1 B2), one) ((AndP B1 B2), zero) C1 ->
    eptLJF4 ((B1, one) :: (B2, one) :: C1) K ->
    eptLJF4 C K
| eptLJF4_L_Or :
  forall {C C1: dctx} {B1 B2 : o}  {K: o},
    has_entry C ((Or B1 B2), one) ->
    upd_rel_ex C ((Or B1 B2), one) ((Or B1 B2), zero) C1 ->
    eptLJF4 ((B1, one) :: C1) K ->
    eptLJF4 ((B2, one) :: C1) K ->
    eptLJF4 C K
| eptLJF4_L_True :
  forall {C C1: dctx}  {K: o},
    has_entry C (TT, one) ->
    upd_rel_ex C (TT, one) (TT, zero) C1 ->
    eptLJF4 C1 K ->
    eptLJF4 C K
| eptLJF4_L_False :
  forall {C: dctx}  {K: o},
    has_entry C (FF, one) ->
    eptLJF4 C K

(* First o for focused assumption, second o for conclusion K *)
with lfcLJF4 : dctx -> o -> o -> Prop :=
| lfcLJF4_R_l :
  forall {C : dctx} {P : o}  {K : o},
    exh C ->
    positive P ->
    eptLJF4 ((P, one) :: C) K ->
    lfcLJF4 C P K
| lfcLJF4_I_l :
  forall {C: dctx} {N : o},
    exh C ->
    negative N ->
    atomic N ->
    lfcLJF4 C N N
| lfcLJF4_L_AndN_1 :
  forall {C: dctx} {B1 B2 : o}  {K : o},
    exh C ->
    lfcLJF4 C B1 K ->
    lfcLJF4 C (AndN B1 B2) K
| lfcLJF4_L_AndN_2 :
  forall {C: dctx} {B1 B2 : o}  {K : o},
    exh C ->
    lfcLJF4 C B2 K ->
    lfcLJF4 C (AndN B1 B2) K
| lfcLJF4_L_Impl :
  forall {C: dctx} {B1 B2 : o}  {K : o},
    exh C ->
    rfcLJF4 C B1 ->
    lfcLJF4 C B2 K ->
    lfcLJF4 C (Impl B1 B2) K

with rfcLJF4 : dctx -> o -> Prop :=
| rfcLJF4_R_r :
  forall {C: dctx} {N: o},
    exh C ->
    negative N ->
    bctLJF4 C N ->
    rfcLJF4 C N
| rfcLJF4_I_r :
  forall {C: dctx} {P: o},
    exh C ->
    has_entry C (P, omega) ->
    positive P ->
    atomic P ->
    rfcLJF4 C P
| rfcLJF4_R_AndP :
  forall {C: dctx} {B1 B2: o},
    exh C ->
    rfcLJF4 C B1 ->
    rfcLJF4 C B2 ->
    rfcLJF4 C (AndP B1 B2)
| rfcLJF4_R_Or_1 :
  forall {C: dctx} {B1 B2: o},
    exh C ->
    rfcLJF4 C B1 ->
    rfcLJF4 C (Or B1 B2)
| rfcLJF4_R_Or_2 :
  forall {C: dctx} {B1 B2: o},
    exh C ->
    rfcLJF4 C B2 ->
    rfcLJF4 C (Or B1 B2)
| rfcLJF4_R_True :
  forall {C: dctx},
    exh C ->
    rfcLJF4 C TT
.